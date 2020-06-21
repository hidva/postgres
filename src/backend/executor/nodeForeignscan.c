/*-------------------------------------------------------------------------
 *
 * nodeForeignscan.c
 *	  Routines to support scans of foreign tables
 *
 * Portions Copyright (c) 1996-2016, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/nodeForeignscan.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * INTERFACE ROUTINES
 *
 *		ExecForeignScan			scans a foreign table.
 *		ExecInitForeignScan		creates and initializes state info.
 *		ExecReScanForeignScan	rescans the foreign relation.
 *		ExecEndForeignScan		releases any resources allocated.
 */
#include "postgres.h"

#include "executor/executor.h"
#include "executor/nodeForeignscan.h"
#include "foreign/fdwapi.h"
#include "utils/memutils.h"
#include "utils/rel.h"

static TupleTableSlot *ForeignNext(ForeignScanState *node);
static bool ForeignRecheck(ForeignScanState *node, TupleTableSlot *slot);


/* ----------------------------------------------------------------
 *		ForeignNext
 *
 *		This is a workhorse for ExecForeignScan
 * ----------------------------------------------------------------
 */
static TupleTableSlot *
ForeignNext(ForeignScanState *node)
{
	TupleTableSlot *slot;
	ForeignScan *plan = (ForeignScan *) node->ss.ps.plan;
	ExprContext *econtext = node->ss.ps.ps_ExprContext;
	MemoryContext oldcontext;

	/* Call the Iterate function in short-lived context */
	oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);
	if (plan->operation != CMD_SELECT)
		slot = node->fdwroutine->IterateDirectModify(node);
	else
		slot = node->fdwroutine->IterateForeignScan(node);
	MemoryContextSwitchTo(oldcontext);

	/*
	 * If any system columns are requested, we have to force the tuple into
	 * physical-tuple form to avoid "cannot extract system attribute from
	 * virtual tuple" errors later.  We also insert a valid value for
	 * tableoid, which is the only actually-useful system column.
	 */
	if (plan->fsSystemCol && !TupIsNull(slot))
	{
		HeapTuple	tup = ExecMaterializeSlot(slot);

		tup->t_tableOid = RelationGetRelid(node->ss.ss_currentRelation);
	}

	return slot;
}

/*
 * ForeignRecheck -- access method routine to recheck a tuple in EvalPlanQual
 */
static bool
ForeignRecheck(ForeignScanState *node, TupleTableSlot *slot)
{
	FdwRoutine *fdwroutine = node->fdwroutine;
	ExprContext *econtext;

	/*
	 * extract necessary information from foreign scan node
	 */
	econtext = node->ss.ps.ps_ExprContext;

	/* Does the tuple meet the remote qual condition? */
	econtext->ecxt_scantuple = slot;

	ResetExprContext(econtext);

	/*
	 * If an outer join is pushed down, RecheckForeignScan may need to store a
	 * different tuple in the slot, because a different set of columns may go
	 * to NULL upon recheck.  Otherwise, it shouldn't need to change the slot
	 * contents, just return true or false to indicate whether the quals still
	 * pass.  For simple cases, setting fdw_recheck_quals may be easier than
	 * providing this callback.
	 */
	if (fdwroutine->RecheckForeignScan &&
		!fdwroutine->RecheckForeignScan(node, slot))
		return false;

	return ExecQual(node->fdw_recheck_quals, econtext, false);
}

/* ----------------------------------------------------------------
 *		ExecForeignScan(node)
 *
 *		Fetches the next tuple from the FDW, checks local quals, and
 *		returns it.
 *		We call the ExecScan() routine and pass it the appropriate
 *		access method functions.
 * ----------------------------------------------------------------
 */
TupleTableSlot *
ExecForeignScan(ForeignScanState *node)
{
	return ExecScan((ScanState *) node,
					(ExecScanAccessMtd) ForeignNext,
					(ExecScanRecheckMtd) ForeignRecheck);
}


/* ----------------------------------------------------------------
 *		ExecInitForeignScan
 * ----------------------------------------------------------------
 */
ForeignScanState *
ExecInitForeignScan(ForeignScan *node, EState *estate, int eflags)
{
	ForeignScanState *scanstate;
	Relation	currentRelation = NULL;
	Index		scanrelid = node->scan.scanrelid;
	Index		tlistvarno;
	FdwRoutine *fdwroutine;

	/* check for unsupported flags */
	Assert(!(eflags & (EXEC_FLAG_BACKWARD | EXEC_FLAG_MARK)));

	/*
	 * create state structure
	 */
	scanstate = makeNode(ForeignScanState);
	scanstate->ss.ps.plan = (Plan *) node;
	scanstate->ss.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &scanstate->ss.ps);

	scanstate->ss.ps.ps_TupFromTlist = false;

	/*
	 * initialize child expressions
	 */
	scanstate->ss.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->scan.plan.targetlist,
					 (PlanState *) scanstate);
	scanstate->ss.ps.qual = (List *)
		ExecInitExpr((Expr *) node->scan.plan.qual,
					 (PlanState *) scanstate);
	scanstate->fdw_recheck_quals = (List *)
		ExecInitExpr((Expr *) node->fdw_recheck_quals,
					 (PlanState *) scanstate);

	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &scanstate->ss.ps);
	ExecInitScanTupleSlot(estate, &scanstate->ss);

	/*
	 * open the base relation, if any, and acquire an appropriate lock on it;
	 * also acquire function pointers from the FDW's handler
	 */
	if (scanrelid > 0)
	{
		currentRelation = ExecOpenScanRelation(estate, scanrelid, eflags);
		scanstate->ss.ss_currentRelation = currentRelation;
		fdwroutine = GetFdwRoutineForRelation(currentRelation, true);
	}
	else
	{
		/* We can't use the relcache, so get fdwroutine the hard way */
		fdwroutine = GetFdwRoutineByServerId(node->fs_server);
	}

	/*
	 * Determine the scan tuple type.  If the FDW provided a targetlist
	 * describing the scan tuples, use that; else use base relation's rowtype.
	 */
	if (node->fdw_scan_tlist != NIL || currentRelation == NULL)
	{
		TupleDesc	scan_tupdesc;

		scan_tupdesc = ExecTypeFromTL(node->fdw_scan_tlist, false);
		ExecAssignScanType(&scanstate->ss, scan_tupdesc);
		/* Node's targetlist will contain Vars with varno = INDEX_VAR */
		tlistvarno = INDEX_VAR;
	}
	else
	{
		ExecAssignScanType(&scanstate->ss, RelationGetDescr(currentRelation));
		/* Node's targetlist will contain Vars with varno = scanrelid */
		tlistvarno = scanrelid;
	}

	/*
	 * Initialize result tuple type and projection info.
	 */
	ExecAssignResultTypeFromTL(&scanstate->ss.ps);
	ExecAssignScanProjectionInfoWithVarno(&scanstate->ss, tlistvarno);

	/*
	 * Initialize FDW-related state.
	 */
	scanstate->fdwroutine = fdwroutine;
	scanstate->fdw_state = NULL;

	/* Initialize any outer plan. */
	if (outerPlan(node))
		outerPlanState(scanstate) =
			ExecInitNode(outerPlan(node), estate, eflags);

	/*
	 * Tell the FDW to initialize the scan.
	 */
	if (node->operation != CMD_SELECT)
		scanstate->fdwroutine->BeginDirectModify(scanstate, eflags);
	else
		scanstate->fdwroutine->BeginForeignScan(scanstate, eflags);

	return scanstate;
}

/* ----------------------------------------------------------------
 *		ExecEndForeignScan
 *
 *		frees any storage allocated through C routines.
 * ----------------------------------------------------------------
 */
void
ExecEndForeignScan(ForeignScanState *node)
{
	ForeignScan *plan = (ForeignScan *) node->ss.ps.plan;

	/* Let the FDW shut down */
	if (plan->operation != CMD_SELECT)
		node->fdwroutine->EndDirectModify(node);
	else
		node->fdwroutine->EndForeignScan(node);

	/* Shut down any outer plan. */
	if (outerPlanState(node))
		ExecEndNode(outerPlanState(node));

	/* Free the exprcontext */
	ExecFreeExprContext(&node->ss.ps);

	/* clean out the tuple table */
	ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->ss.ss_ScanTupleSlot);

	/* close the relation. */
	if (node->ss.ss_currentRelation)
		ExecCloseScanRelation(node->ss.ss_currentRelation);
}

/* ----------------------------------------------------------------
 *		ExecReScanForeignScan
 *
 *		Rescans the relation.
 * ----------------------------------------------------------------
 */
void
ExecReScanForeignScan(ForeignScanState *node)
{
	PlanState  *outerPlan = outerPlanState(node);

	node->fdwroutine->ReScanForeignScan(node);

	/*
	 * If chgParam of subnode is not null then plan will be re-scanned by
	 * first ExecProcNode.  outerPlan may also be NULL, in which case there is
	 * nothing to rescan at all.
	 */
	if (outerPlan != NULL && outerPlan->chgParam == NULL)
		ExecReScan(outerPlan);

	ExecScanReScan(&node->ss);
}

/* ----------------------------------------------------------------
 *		ExecForeignScanEstimate
 *
 *		Informs size of the parallel coordination information, if any
 * ----------------------------------------------------------------
 */
void
ExecForeignScanEstimate(ForeignScanState *node, ParallelContext *pcxt)
{
	FdwRoutine *fdwroutine = node->fdwroutine;

	if (fdwroutine->EstimateDSMForeignScan)
	{
		node->pscan_len = fdwroutine->EstimateDSMForeignScan(node, pcxt);
		shm_toc_estimate_chunk(&pcxt->estimator, node->pscan_len);
		shm_toc_estimate_keys(&pcxt->estimator, 1);
	}
}

/* ----------------------------------------------------------------
 *		ExecForeignScanInitializeDSM
 *
 *		Initialize the parallel coordination information
 * ----------------------------------------------------------------
 */
void
ExecForeignScanInitializeDSM(ForeignScanState *node, ParallelContext *pcxt)
{
	FdwRoutine *fdwroutine = node->fdwroutine;

	if (fdwroutine->InitializeDSMForeignScan)
	{
		int			plan_node_id = node->ss.ps.plan->plan_node_id;
		void	   *coordinate;

		coordinate = shm_toc_allocate(pcxt->toc, node->pscan_len);
		fdwroutine->InitializeDSMForeignScan(node, pcxt, coordinate);
		shm_toc_insert(pcxt->toc, plan_node_id, coordinate);
	}
}

/* ----------------------------------------------------------------
 *		ExecForeignScanInitializeDSM
 *
 *		Initialization according to the parallel coordination information
 * ----------------------------------------------------------------
 */
void
ExecForeignScanInitializeWorker(ForeignScanState *node, shm_toc *toc)
{
	FdwRoutine *fdwroutine = node->fdwroutine;

	if (fdwroutine->InitializeWorkerForeignScan)
	{
		int			plan_node_id = node->ss.ps.plan->plan_node_id;
		void	   *coordinate;

		coordinate = shm_toc_lookup(toc, plan_node_id);
		fdwroutine->InitializeWorkerForeignScan(node, toc, coordinate);
	}
}

BufferedForeignScanState*
ExecInitBufferedForeignScan(ForeignScan *node, EState *estate, int eflags)
{
	BufferedForeignScanState *state = (BufferedForeignScanState*)makeNode(BufferedForeignScanState);
	Index		tlistvarno;
	Index		scanrelid = node->scan.scanrelid;
	ForeignScanState *scanstate = &state->scan;
	scanstate->ss.ps.plan = (Plan *) node;
	scanstate->ss.ps.state = estate;
	ExecAssignExprContext(estate, &scanstate->ss.ps);
	scanstate->ss.ps.ps_TupFromTlist = false;
	scanstate->ss.ps.targetlist = (List *)ExecInitExpr((Expr *) node->scan.plan.targetlist, (PlanState *) scanstate);
	scanstate->ss.ps.qual = (List *)ExecInitExpr((Expr *) node->scan.plan.qual, (PlanState *) scanstate);
	scanstate->fdw_recheck_quals = (List *)ExecInitExpr((Expr *) node->fdw_recheck_quals, (PlanState *) scanstate);
	ExecInitResultTupleSlot(estate, &scanstate->ss.ps);
	ExecInitScanTupleSlot(estate, &scanstate->ss);
	if (scanrelid > 0) {
		scanstate->ss.ss_currentRelation = ExecOpenScanRelation(estate, scanrelid, eflags);;
		scanstate->fdwroutine = GetFdwRoutineForRelation(scanstate->ss.ss_currentRelation, true);
	} else {
		scanstate->fdwroutine = GetFdwRoutineByServerId(node->fs_server);
	}
	if (node->fdw_scan_tlist != NIL || scanstate->ss.ss_currentRelation == NULL) {
		TupleDesc	scan_tupdesc;
		scan_tupdesc = ExecTypeFromTL(node->fdw_scan_tlist, false);
		ExecAssignScanType(&scanstate->ss, scan_tupdesc);
		tlistvarno = INDEX_VAR;
	} else {
		ExecAssignScanType(&scanstate->ss, RelationGetDescr(scanstate->ss.ss_currentRelation));
		tlistvarno = scanrelid;
	}
	ExecAssignResultTypeFromTL(&scanstate->ss.ps);
	ExecAssignScanProjectionInfoWithVarno(&scanstate->ss, tlistvarno);
	scanstate->fdw_state = NULL;
	if (outerPlan(node))
		outerPlanState(scanstate) = ExecInitNode(outerPlan(node), estate, eflags);
	if (node->operation != CMD_SELECT)
		scanstate->fdwroutine->BeginDirectModify(scanstate, eflags);
	else
		scanstate->fdwroutine->BeginForeignScan(scanstate, eflags);

	state->buffers = palloc0(sizeof(TupleTableSlot) * buffered_scan_cap);
	for (int i = 0; i < buffered_scan_cap; ++i)
	{
		TupleTableSlot *slot = &state->buffers[i];
		slot->type = T_TupleTableSlot;
		slot->tts_isempty = true;
		slot->tts_mcxt = CurrentMemoryContext;
		ExecSetSlotDescriptor(slot, RelationGetDescr(scanstate->ss.ss_currentRelation));
		estate->es_tupleTable = lappend(estate->es_tupleTable, slot);
	}
	if (state->scan.ss.ps.ps_ProjInfo)
		elog(ERROR, "unsupported");
	return state;
}

/*
 * `node->buffersize >= buffered_Foreignscan_cap || TupIsNull(node->buffers[node->buffersize])`
 * shoule be true after the return
 */
void
ExecBufferedForeignScan(BufferedForeignScanState *bufferedstate)
{
	TupleTableSlot *oldscanslot = bufferedstate->scan.ss.ss_ScanTupleSlot;
	ExprContext *econtext = bufferedstate->scan.ss.ps.ps_ExprContext;
	List *qual = bufferedstate->scan.ss.ps.qual;
	ScanState *node = &bufferedstate->scan.ss;
	for (bufferedstate->buffersize = 0; bufferedstate->buffersize < buffered_scan_cap; ++bufferedstate->buffersize) {
		TupleTableSlot *slot = &bufferedstate->buffers[bufferedstate->buffersize];
		bufferedstate->scan.ss.ss_ScanTupleSlot = slot;
		while (true) {
			ForeignNext(&bufferedstate->scan);
			if (TupIsNull(slot)) {
				bufferedstate->is_done = true;
				bufferedstate->scan.ss.ss_ScanTupleSlot = oldscanslot;
				return;
			}
			econtext->ecxt_scantuple = slot;
			if (!qual || ExecQual(qual, econtext, false))
				break;
			else
				InstrCountFiltered1(node, 1);
		}
	}
	bufferedstate->scan.ss.ss_ScanTupleSlot = oldscanslot;
	return;
}

void
ExecEndBufferedForeignScan(BufferedForeignScanState *state)
{
	ForeignScanState *node = &state->scan;
	ForeignScan *plan = (ForeignScan *) node->ss.ps.plan;

	/* Let the FDW shut down */
	if (plan->operation != CMD_SELECT)
		node->fdwroutine->EndDirectModify(node);
	else
		node->fdwroutine->EndForeignScan(node);

	/* Shut down any outer plan. */
	if (outerPlanState(node))
		ExecEndNode(outerPlanState(node));

	/* Free the exprcontext */
	ExecFreeExprContext(&node->ss.ps);

	/* clean out the tuple table */
	ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->ss.ss_ScanTupleSlot);

	/* close the relation. */
	if (node->ss.ss_currentRelation)
		ExecCloseScanRelation(node->ss.ss_currentRelation);

	for (int i = 0; i < state->buffersize; ++i)
		ExecClearTuple(&state->buffers[i]);
}