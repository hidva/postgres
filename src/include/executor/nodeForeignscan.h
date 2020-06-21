/*-------------------------------------------------------------------------
 *
 * nodeForeignscan.h
 *
 *
 *
 * Portions Copyright (c) 1996-2016, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/include/executor/nodeForeignscan.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef NODEFOREIGNSCAN_H
#define NODEFOREIGNSCAN_H

#include "access/parallel.h"
#include "nodes/execnodes.h"

extern ForeignScanState *ExecInitForeignScan(ForeignScan *node, EState *estate, int eflags);
extern TupleTableSlot *ExecForeignScan(ForeignScanState *node);
extern void ExecEndForeignScan(ForeignScanState *node);
extern void ExecReScanForeignScan(ForeignScanState *node);

extern void ExecForeignScanEstimate(ForeignScanState *node,
						ParallelContext *pcxt);
extern void ExecForeignScanInitializeDSM(ForeignScanState *node,
							 ParallelContext *pcxt);
extern void ExecForeignScanInitializeWorker(ForeignScanState *node,
								shm_toc *toc);

extern int buffered_scan_cap;
extern BufferedForeignScanState *ExecInitBufferedForeignScan(ForeignScan *node, EState *estate, int eflags);
extern void ExecBufferedForeignScan(BufferedForeignScanState *node);
extern void ExecEndBufferedForeignScan(BufferedForeignScanState *node);
#endif   /* NODEFOREIGNSCAN_H */
