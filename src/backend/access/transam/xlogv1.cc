#include <unistd.h>

extern "C" {

#include "postgres.h"

#include "access/xact.h"
#include "access/xlog.h"
#include "access/xlog_internal.h"
#include "access/xloginsert.h"
#include "access/xlogreader.h"
#include "access/xlogutils.h"
#include "access/xlogrecord.h"
#include "access/rmgr.h"
#include "catalog/pg_control.h"
#include "storage/shmem.h"

extern ControlFileData *ControlFile;
extern XLogRecPtr RedoRecPtr;
extern bool doPageWrites;
void UpdateRedoRecPtrPageWrite();

}

#include <mutex>

#include <pthread.h>

struct SharedMutex {
	SharedMutex() noexcept;
	~SharedMutex() noexcept;
	void lock() noexcept;
	void unlock() noexcept;
private:
	pthread_mutex_t mutex_;
	pthread_mutexattr_t attr_;
};

#define ASSERT_PTHREAD(callstmt) do { \
		int ret = (callstmt);	\
		if (ret)	\
			elog(PANIC, #callstmt " failed; ret: %d", ret);	\
	} while(0);

SharedMutex::SharedMutex() noexcept
{
	ASSERT_PTHREAD(pthread_mutexattr_init(&attr_));
	ASSERT_PTHREAD(pthread_mutexattr_setpshared(&attr_, PTHREAD_PROCESS_SHARED));
	ASSERT_PTHREAD(pthread_mutex_init(&mutex_, &attr_));
}

SharedMutex::~SharedMutex() noexcept
{
	ASSERT_PTHREAD(pthread_mutex_destroy(&mutex_));
	ASSERT_PTHREAD(pthread_mutexattr_destroy(&attr_));
}

void SharedMutex::lock() noexcept
{
	ASSERT_PTHREAD(pthread_mutex_lock(&mutex_));
}

void SharedMutex::unlock() noexcept
{
	ASSERT_PTHREAD(pthread_mutex_unlock(&mutex_));
}

struct XLOGV1Insert {
	uint64 prev_pos;
	uint64 curr_pos;
	SharedMutex mux;
};

/*
 *  * if fd >= 0, it means that the fd point to the file where the curr_pos is placed in, and the
 *   * offset of fd is set to the position that its logical offset is curr_pos.
 *    */
static int
Open(XLogRecPtr pos) noexcept
{
	XLogSegNo segno = pos / XLogSegSize;
	char path[MAXPGPATH];
	XLogFilePath(path, ThisTimeLineID, segno);
	int fd = open(path, O_WRONLY | O_CREAT, S_IRUSR | S_IWUSR);
	if (fd < 0) {
		elog(PANIC, "Open Error");
	}
	uint64 off = pos % XLogSegSize;
	if (lseek(fd, off, SEEK_SET) < 0) {
		elog(PANIC, "SEEK Error");
	}
	return fd;
}

static void
Fsync(int fd) noexcept
{
	if (fdatasync(fd) < 0)
		elog(PANIC, "sync error");
}

static void
Close(int fd) noexcept
{
	Fsync(fd);
	close(fd);
}

static void
Write(int fd, const void *ptr, uint32 size) noexcept
{
	uint32 nleft = size;
	do {
		errno = 0;
		uint32 writen = write(fd, ptr, nleft);
		if (writen < 0) {
			if (errno == EINTR) {
				continue;
			}
			ereport(PANIC, (errcode_for_file_access(), errmsg("CannotWrite")));
		}
		nleft -= writen;
	} while (nleft > 0);
	return;
}

static XLOGV1Insert *g_insertctx;

extern "C" void
XLOGV1InsertShmemInit() noexcept
{
	bool found = false;
	void *ptr = ShmemInitStruct("XLogV1Insert", sizeof(XLOGV1Insert), &found);
	if (found) {
		g_insertctx = (XLOGV1Insert *)ptr;
	} else {
		g_insertctx = new(ptr) XLOGV1Insert();
	}
	return;
}

extern "C" void
InitXLOGV1Insert(uint64 prev, uint64 curr) noexcept
{
	g_insertctx->prev_pos = prev;
	g_insertctx->curr_pos = curr;
	return;
}

static void
AppendRecData(XLogRecData *header, XLogRecData *ptr)
{
	while (header->next != NULL) {
		header = header->next;
	}
	header->next = ptr;
}

extern "C" XLogRecPtr
XLogInsertRecord(struct XLogRecData *rdata, XLogRecPtr fpw_lsn) noexcept
{
	bool prevDoPageWrites = doPageWrites;
	UpdateRedoRecPtrPageWrite();  /* FIXME: should read on locked */
	if (doPageWrites &&
		(!prevDoPageWrites ||
		 (fpw_lsn != InvalidXLogRecPtr && fpw_lsn <= RedoRecPtr)))
	{
		return InvalidXLogRecPtr;
	}
	std::lock_guard<SharedMutex> _guard(g_insertctx->mux);

	XLogRecord *rechdr = (XLogRecord *) rdata->data;
	bool isLogSwitch = (rechdr->xl_rmid == RM_XLOG_ID && rechdr->xl_info == XLOG_SWITCH);
	if (isLogSwitch) {
		elog(PANIC, "isLogSwitch: true");
	}

	rechdr->xl_prev = XLogBytePosToRecPtr(g_insertctx->prev_pos);
	COMP_CRC32C(rechdr->xl_crc, rechdr, offsetof(XLogRecord, xl_crc));
	FIN_CRC32C(rechdr->xl_crc);

	char padding_buf[MAXIMUM_ALIGNOF]{};
	uint32 aligned_size = MAXALIGN(rechdr->xl_tot_len);
	uint32 padding_size = aligned_size - rechdr->xl_tot_len;
	XLogRecData padding;
	padding.next = NULL;
	padding.data = padding_buf;
	padding.len = padding_size;
	AppendRecData(rdata, &padding);  /* rdata don't be used after return from XLogInsertRecord. */

	int filefd = -1;
	uint32 remain_size = aligned_size;
	uint32 rdata_left = rdata->len;
	XLogRecPtr curfilepos = XLogBytePosToEndRecPtr(g_insertctx->curr_pos);
	while (remain_size > 0) {
		if (filefd < 0) {
			filefd = Open(curfilepos);
		}
		uint32 freespace;  /* free space in current page */
		if (curfilepos % XLOG_BLCKSZ == 0) {
			/* Currently XLogLongPageHeaderData has been max-aligned. */
			XLogLongPageHeaderData pageheader;
			MemSet(&pageheader, 0, sizeof(pageheader));
			pageheader.std.xlp_magic = XLOG_PAGE_MAGIC;
			pageheader.std.xlp_tli = ThisTimeLineID;
			pageheader.std.xlp_pageaddr = curfilepos;
			if (remain_size < aligned_size) {
				Assert(remain_size > padding_size);
				pageheader.std.xlp_rem_len = remain_size - padding_size;
				pageheader.std.xlp_info |= XLP_FIRST_IS_CONTRECORD;
			}
			pageheader.std.xlp_info |= XLP_BKP_REMOVABLE;  /* set only when forcePageWrite is true. */
			if (curfilepos % XLogSegSize == 0) {
				pageheader.xlp_sysid = ControlFile->system_identifier;
				pageheader.xlp_seg_size = XLogSegSize;
				pageheader.xlp_xlog_blcksz = XLOG_BLCKSZ;
				pageheader.std.xlp_info |= XLP_LONG_HEADER;
				freespace = XLOG_BLCKSZ - sizeof(pageheader);
			} else {
				freespace = XLOG_BLCKSZ - sizeof(pageheader.std);
			}
			uint32 writen = XLOG_BLCKSZ - freespace;
			Write(filefd, &pageheader, writen);
			curfilepos += writen;
		} else {
			freespace = XLOG_BLCKSZ - curfilepos % XLOG_BLCKSZ;
		}
		uint32 writen = rdata_left > freespace ? freespace : rdata_left;
		Write(filefd, rdata->data + (rdata->len - rdata_left), writen);
		remain_size -= writen;
		rdata_left -= writen;
		curfilepos += writen;
		if (curfilepos % XLogSegSize == 0) {
			Close(filefd);
			filefd = -1;
		}
		if (rdata_left == 0 && remain_size > 0) {
			rdata = rdata->next;
			rdata_left = rdata->len;
		}
	}
	if (filefd >= 0) {
		Close(filefd);
	}
	g_insertctx->prev_pos = g_insertctx->curr_pos;
	g_insertctx->curr_pos += aligned_size;

	MarkCurrentTransactionIdLoggedIfAny();
	ProcLastRecPtr = XLogBytePosToRecPtr(g_insertctx->prev_pos);
	XactLastRecEnd = curfilepos;
	return curfilepos;
}

extern "C" void
XLogFlush(XLogRecPtr RecPtr) noexcept
{
	return;
}



