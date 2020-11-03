/**
 * Purpose: Read redo logs continuously and apply latest modification to buffer pool pages.
 * Most of methods are copied from log0recv.cc.
 * Note: Prefix methods with "sbuf"
 */

#include "s0buf0refresher.h"

#include "stdio.h"
#include "btr0btr.h"
#include "btr0cur.h"
#include "buf0buf.h"
#include "buf0flu.h"
#include "clone0api.h"
#include "dict0dd.h"
#include "fil0fil.h"
#include "ha_prototypes.h"
#include "ibuf0ibuf.h"
#include "log0log.h"
#include "mem0mem.h"
#include "mtr0log.h"
#include "mtr0mtr.h"
#include "my_compiler.h"
#include "my_dbug.h"
#include "my_inttypes.h"
#include "os0thread-create.h"
#include "page0cur.h"
#include "page0zip.h"
#include "trx0rec.h"
#include "trx0undo.h"
#include "ut0new.h"
#include "log0recv.h"
#include "trx0sys.h"
#include "dict0priv.h"
#include "my_thread.h"
#include <iostream>
#include <pthread.h>
#include "current_thd.h"

// sql/* - header files.
#include "sql/mdl.h"
#include "sql/sql_base.h"
#include "sql/sql_class.h"
#include "sql/table.h"
#include "sql_thd_internal_api.h"
#include "mysql/psi/mysql_mutex.h"

#define RECV_DATA_BLOCK_SIZE (MEM_MAX_ALLOC_IN_BUF - sizeof(recv_data_t))

/** The following counter is used to decide when to print info on
log scan */
static ulint recv_scan_print_counter;

/** The type of the previous parsed redo log record */
static mlog_id_t recv_previous_parsed_rec_type;

/** The offset of the previous parsed redo log record */
static ulint recv_previous_parsed_rec_offset;

/** The 'multi' flag of the previous parsed redo log record */
static ulint recv_previous_parsed_rec_is_multi;

//PSI_memory_key mem_log_recv_page_hash_key;
extern PSI_memory_key mem_sbuf_space_hash_key;

/** The maximum lsn we see for a page during the recovery process. If this
is bigger than the lsn we are able to scan up to, that is an indication that
the recovery failed and the database may be corrupt. */
static lsn_t recv_max_page_lsn;

lsn_t page_newest_lsn = 0;
/* Count applied and skipped log records */
size_t applied_recs = 0;
size_t skipped_recs = 0;

/** This the maximum lsn upto which we have complete redo log **/
static lsn_t sbuf_consistent_lsn;

static recv_sys_t * sbuf_recv_sys = nullptr;
static bool sbuf_refresh_on=false;

static ulint sbuf_latest_checkpoint_no;

static sbuf_struct_gen_var_t sbuf_gen_var;

/** Local memory heap **/
struct sbuf_struct_mem_heap_t{
	mem_heap_t * heap;
	ulint st_chkpt;
	ulint end_chkpt;
};

static struct sbuf_struct_gen_var_t * sbuf_cur_mheap;
static struct sbuf_struct_gen_var_t * sbuf_old_mheap;


/** Table meta refersh related variables **/
static mysql_mutex_t sbuf_tmr_mutex;

/** Chain node of the list of tables to drop in the background. */
struct sbuf_struct_tmr_table_node_t {
  char table_name[100]; /*!< table name */
  UT_LIST_NODE_T(sbuf_struct_gen_var_t) tnode;
  /*!< list chain node */
};

static UT_LIST_BASE_NODE_T(sbuf_struct_gen_var_t ) sbuf_tmr_table_list;

bool recv_check_log_header_checksum(const byte *buf) {

	auto c1 = log_block_get_checksum(buf);
	auto c2 = log_block_calc_checksum_crc32(buf);

	return (c1 == c2);
}

/** Try to parse a single log record body and also applies it if
specified.
@param[in]	type		redo log entry type
@param[in]	ptr		redo log record body
@param[in]	end_ptr		end of buffer
@param[in]	space_id	tablespace identifier
@param[in]	page_no		page number
@param[in,out]	block		buffer block, or nullptr if
                                a page log record should not be applied
                                or if it is a MLOG_FILE_ operation
@param[in,out]	mtr		mini-transaction, or nullptr if
                                a page log record should not be applied
@param[in]	parsed_bytes	Number of bytes parsed so far
@return log record end, nullptr if not a complete record */
static byte *recv_parse_or_apply_log_rec_body(
    mlog_id_t type, byte *ptr, byte *end_ptr, space_id_t space_id,
    page_no_t page_no, buf_block_t *block, mtr_t *mtr, ulint parsed_bytes) {


	recv_sys_t * recv_sys=sbuf_recv_sys;
  ut_ad(!block == !mtr);

  switch (type) {
    case MLOG_FILE_DELETE:

      return (fil_tablespace_redo_delete(
          ptr, end_ptr, page_id_t(space_id, page_no), parsed_bytes,
          recv_sys->bytes_to_ignore_before_checkpoint != 0));

    case MLOG_FILE_CREATE:

      return (fil_tablespace_redo_create(
          ptr, end_ptr, page_id_t(space_id, page_no), parsed_bytes,
          recv_sys->bytes_to_ignore_before_checkpoint != 0));

    case MLOG_FILE_RENAME:

      return (fil_tablespace_redo_rename(
          ptr, end_ptr, page_id_t(space_id, page_no), parsed_bytes,
          recv_sys->bytes_to_ignore_before_checkpoint != 0));

    case MLOG_INDEX_LOAD:
#ifdef UNIV_HOTBACKUP
      /* While scaning redo logs during  backup phase a
      MLOG_INDEX_LOAD type redo log record indicates a DDL
      (create index, alter table...)is performed with
      'algorithm=inplace'. This redo log indicates that

      1. The DDL was started after MEB started backing up, in which
      case MEB will not be able to take a consistent backup and should
      fail. or
      2. There is a possibility of this record existing in the REDO
      even after the completion of the index create operation. This is
      because of InnoDB does  not checkpointing after the flushing the
      index pages.

      If MEB gets the last_redo_flush_lsn and that is less than the
      lsn of the current record MEB fails the backup process.
      Error out in case of online backup and emit a warning in case
      of offline backup and continue. */
      if (!recv_recovery_on) {
        if (is_online_redo_copy) {
          if (backup_redo_log_flushed_lsn < recv_sys->recovered_lsn) {
            ib::trace_1() << "Last flushed lsn: " << backup_redo_log_flushed_lsn
                          << " load_index lsn " << recv_sys->recovered_lsn;

            if (backup_redo_log_flushed_lsn == 0) {
              ib::error(ER_IB_MSG_715) << "MEB was not able"
                                       << " to determine the"
                                       << " InnoDB Engine"
                                       << " Status";
            }

            ib::fatal(ER_IB_MSG_716) << "An optimized(without"
                                     << " redo logging) DDL"
                                     << " operation has been"
                                     << " performed. All modified"
                                     << " pages may not have been"
                                     << " flushed to the disk yet.\n"
                                     << "    MEB will not be able to"
                                     << " take a consistent backup."
                                     << " Retry the backup"
                                     << " operation";
          }
          /** else the index is flushed to disk before
          backup started hence no error */
        } else {
          /* offline backup */
          ib::trace_1() << "Last flushed lsn: " << backup_redo_log_flushed_lsn
                        << " load_index lsn " << recv_sys->recovered_lsn;

          ib::warn(ER_IB_MSG_717);
        }
      }
#endif /* UNIV_HOTBACKUP */
      if (end_ptr < ptr + 8) {
        return (nullptr);
      }

      return (ptr + 8);

    case MLOG_WRITE_STRING:

#ifdef UNIV_HOTBACKUP
      if (recv_recovery_on && meb_is_space_loaded(space_id)) {
#endif /* UNIV_HOTBACKUP */
        /* For encrypted tablespace, we need to get the
        encryption key information before the page 0 is
        recovered. Otherwise, redo will not find the key
        to decrypt the data pages. */

        if (page_no == 0 && !fsp_is_system_or_temp_tablespace(space_id) &&
            /* For cloned db header page has the encryption information. */
            !recv_sys->is_cloned_db) {
          return (fil_tablespace_redo_encryption(ptr, end_ptr, space_id));
        }
#ifdef UNIV_HOTBACKUP
      }
#endif /* UNIV_HOTBACKUP */

      break;

    default:
      break;
  }

  page_t *page;
  page_zip_des_t *page_zip;
  dict_index_t *index = nullptr;

#ifdef UNIV_DEBUG
  ulint page_type;
#endif /* UNIV_DEBUG */

#if defined(UNIV_HOTBACKUP) && defined(UNIV_DEBUG)
  ib::trace_3() << "recv_parse_or_apply_log_rec_body { type: "
                << get_mlog_string(type) << ", space_id: " << space_id
                << ", page_no: " << page_no
                << ", ptr : " << static_cast<const void *>(ptr)
                << ", end_ptr: " << static_cast<const void *>(end_ptr)
                << ", block: " << static_cast<const void *>(block)
                << ", mtr: " << static_cast<const void *>(mtr) << " }";
#endif /* UNIV_HOTBACKUP && UNIV_DEBUG */

  if (block != nullptr) {
    /* Applying a page log record. */

    page = block->frame;
    page_zip = buf_block_get_page_zip(block);

    ut_d(page_type = fil_page_get_type(page));
#if defined(UNIV_HOTBACKUP) && defined(UNIV_DEBUG)
    if (page_type == 0) {
      meb_print_page_header(page);
    }
#endif /* UNIV_HOTBACKUP && UNIV_DEBUG */

  } else {
    /* Parsing a page log record. */
    page = nullptr;
    page_zip = nullptr;

    ut_d(page_type = FIL_PAGE_TYPE_ALLOCATED);
  }

  const byte *old_ptr = ptr;

  switch (type) {
#ifdef UNIV_LOG_LSN_DEBUG
    case MLOG_LSN:
      /* The LSN is checked in recv_parse_log_rec(). */
      break;
#endif /* UNIV_LOG_LSN_DEBUG */
    case MLOG_4BYTES:

      ut_ad(page == nullptr || end_ptr > ptr + 2);

      /* Most FSP flags can only be changed by CREATE or ALTER with
      ALGORITHM=COPY, so they do not change once the file
      is created. The SDI flag is the only one that can be
      changed by a recoverable transaction. So if there is
      change in FSP flags, update the in-memory space structure
      (fil_space_t) */

      if (page != nullptr && page_no == 0 &&
          mach_read_from_2(ptr) == FSP_HEADER_OFFSET + FSP_SPACE_FLAGS) {
        ptr = mlog_parse_nbytes(MLOG_4BYTES, ptr, end_ptr, page, page_zip);

        /* When applying log, we have complete records.
        They can be incomplete (ptr=nullptr) only during
        scanning (page==nullptr) */

        ut_ad(ptr != nullptr);

        fil_space_t *space = fil_space_acquire(space_id);

        ut_ad(space != nullptr);

        fil_space_set_flags(space, mach_read_from_4(FSP_HEADER_OFFSET +
                                                    FSP_SPACE_FLAGS + page));
        fil_space_release(space);

        break;
      }

      // fall through

    case MLOG_1BYTE:
      /* If 'ALTER TABLESPACE ... ENCRYPTION' was in progress and page 0 has
      REDO entry for this, set encryption_op_in_progress flag now so that any
      other page of this tablespace in redo log is written accordingly. */
      if (page_no == 0 && page != nullptr && end_ptr >= ptr + 2) {
        ulint offs = mach_read_from_2(ptr);

        fil_space_t *space = fil_space_acquire(space_id);
        ut_ad(space != nullptr);
        ulint offset = fsp_header_get_encryption_progress_offset(
            page_size_t(space->flags));

        if (offs == offset) {
          ptr = mlog_parse_nbytes(MLOG_1BYTE, ptr, end_ptr, page, page_zip);
          byte op = mach_read_from_1(page + offset);
          switch (op) {
            case ENCRYPTION_IN_PROGRESS:
              space->encryption_op_in_progress = ENCRYPTION;
              break;
            case UNENCRYPTION_IN_PROGRESS:
              space->encryption_op_in_progress = UNENCRYPTION;
              break;
            default:
              /* Don't reset operation in progress yet. It'll be done in
              fsp_resume_encryption_unencryption(). */
              break;
          }
        }
        fil_space_release(space);
      }

      // fall through

    case MLOG_2BYTES:
    case MLOG_8BYTES:
#ifdef UNIV_DEBUG
      if (page && page_type == FIL_PAGE_TYPE_ALLOCATED && end_ptr >= ptr + 2) {
        /* It is OK to set FIL_PAGE_TYPE and certain
        list node fields on an empty page.  Any other
        write is not OK. */

        /* NOTE: There may be bogus assertion failures for
        dict_hdr_create(), trx_rseg_header_create(),
        trx_sys_create_doublewrite_buf(), and
        trx_sysf_create().
        These are only called during database creation. */

        ulint offs = mach_read_from_2(ptr);

        switch (type) {
          default:
            ut_error;
          case MLOG_2BYTES:
            /* Note that this can fail when the
            redo log been written with something
            older than InnoDB Plugin 1.0.4. */
            ut_ad(
                offs == FIL_PAGE_TYPE ||
                offs == IBUF_TREE_SEG_HEADER + IBUF_HEADER + FSEG_HDR_OFFSET ||
                offs == PAGE_BTR_IBUF_FREE_LIST + PAGE_HEADER + FIL_ADDR_BYTE ||
                offs == PAGE_BTR_IBUF_FREE_LIST + PAGE_HEADER + FIL_ADDR_BYTE +
                            FIL_ADDR_SIZE ||
                offs == PAGE_BTR_SEG_LEAF + PAGE_HEADER + FSEG_HDR_OFFSET ||
                offs == PAGE_BTR_SEG_TOP + PAGE_HEADER + FSEG_HDR_OFFSET ||
                offs == PAGE_BTR_IBUF_FREE_LIST_NODE + PAGE_HEADER +
                            FIL_ADDR_BYTE + 0 /*FLST_PREV*/
                || offs == PAGE_BTR_IBUF_FREE_LIST_NODE + PAGE_HEADER +
                               FIL_ADDR_BYTE + FIL_ADDR_SIZE /*FLST_NEXT*/);
            break;
          case MLOG_4BYTES:
            /* Note that this can fail when the
            redo log been written with something
            older than InnoDB Plugin 1.0.4. */
            ut_ad(
                0 ||
                offs == IBUF_TREE_SEG_HEADER + IBUF_HEADER + FSEG_HDR_SPACE ||
                offs == IBUF_TREE_SEG_HEADER + IBUF_HEADER + FSEG_HDR_PAGE_NO ||
                offs == PAGE_BTR_IBUF_FREE_LIST + PAGE_HEADER /* flst_init */
                ||
                offs == PAGE_BTR_IBUF_FREE_LIST + PAGE_HEADER + FIL_ADDR_PAGE ||
                offs == PAGE_BTR_IBUF_FREE_LIST + PAGE_HEADER + FIL_ADDR_PAGE +
                            FIL_ADDR_SIZE ||
                offs == PAGE_BTR_SEG_LEAF + PAGE_HEADER + FSEG_HDR_PAGE_NO ||
                offs == PAGE_BTR_SEG_LEAF + PAGE_HEADER + FSEG_HDR_SPACE ||
                offs == PAGE_BTR_SEG_TOP + PAGE_HEADER + FSEG_HDR_PAGE_NO ||
                offs == PAGE_BTR_SEG_TOP + PAGE_HEADER + FSEG_HDR_SPACE ||
                offs == PAGE_BTR_IBUF_FREE_LIST_NODE + PAGE_HEADER +
                            FIL_ADDR_PAGE + 0 /*FLST_PREV*/
                || offs == PAGE_BTR_IBUF_FREE_LIST_NODE + PAGE_HEADER +
                               FIL_ADDR_PAGE + FIL_ADDR_SIZE /*FLST_NEXT*/);
            break;
        }
      }
#endif /* UNIV_DEBUG */

      ptr = mlog_parse_nbytes(type, ptr, end_ptr, page, page_zip);

      if (ptr != nullptr && page != nullptr && page_no == 0 &&
          type == MLOG_4BYTES) {
        ulint offs = mach_read_from_2(old_ptr);

        switch (offs) {
          fil_space_t *space;
          uint32_t val;
          default:
            break;

          case FSP_HEADER_OFFSET + FSP_SPACE_FLAGS:
          case FSP_HEADER_OFFSET + FSP_SIZE:
          case FSP_HEADER_OFFSET + FSP_FREE_LIMIT:
          case FSP_HEADER_OFFSET + FSP_FREE + FLST_LEN:

            space = fil_space_get(space_id);

            ut_a(space != nullptr);

            val = mach_read_from_4(page + offs);

            switch (offs) {
              case FSP_HEADER_OFFSET + FSP_SPACE_FLAGS:
                space->flags = val;
                break;

              case FSP_HEADER_OFFSET + FSP_SIZE:

                space->size_in_header = val;

                if (space->size >= val) {
                  break;
                }

                ib::info(ER_IB_MSG_718, ulong{space->id}, space->name,
                         ulong{val});

                if (fil_space_extend(space, val)) {
                  break;
                }

                ib::error(ER_IB_MSG_719, ulong{space->id}, space->name,
                          ulong{val});
                break;

              case FSP_HEADER_OFFSET + FSP_FREE_LIMIT:
                space->free_limit = val;
                break;

              case FSP_HEADER_OFFSET + FSP_FREE + FLST_LEN:
                space->free_len = val;
                ut_ad(val == flst_get_len(page + offs));
                break;
            }
        }
      }
      break;

    case MLOG_REC_INSERT:
    case MLOG_COMP_REC_INSERT:

      ut_ad(!page || fil_page_type_is_index(page_type));

      if (nullptr !=
          (ptr = mlog_parse_index(ptr, end_ptr, type == MLOG_COMP_REC_INSERT,
                                  &index))) {
        ut_a(!page ||
             (ibool) !!page_is_comp(page) == dict_table_is_comp(index->table));


       /*  Attempted to find meta_modfied tables info from xlog, but the attempt doesn't succeeded.
        * Now created new XLOG records to capture the table meta modifications.
        * if(space_id == dict_sys->s_space_id ){
        	if( index->n_fields==37){
        		parse_dd_tables( ptr, end_ptr,  index, mtr);
        	}
        } */

        ptr = page_cur_parse_insert_rec(FALSE, ptr, end_ptr, block, index, mtr);
      }

      break;

    case MLOG_REC_CLUST_DELETE_MARK:
    case MLOG_COMP_REC_CLUST_DELETE_MARK:

      ut_ad(!page || fil_page_type_is_index(page_type));

      if (nullptr != (ptr = mlog_parse_index(
                          ptr, end_ptr, type == MLOG_COMP_REC_CLUST_DELETE_MARK,
                          &index))) {
        ut_a(!page ||
             (ibool) !!page_is_comp(page) == dict_table_is_comp(index->table));

        ptr = btr_cur_parse_del_mark_set_clust_rec(ptr, end_ptr, page, page_zip,
                                                   index);
      }

      break;

    case MLOG_COMP_REC_SEC_DELETE_MARK:

      ut_ad(!page || fil_page_type_is_index(page_type));

      /* This log record type is obsolete, but we process it for
      backward compatibility with MySQL 5.0.3 and 5.0.4. */

      ut_a(!page || page_is_comp(page));
      ut_a(!page_zip);

      ptr = mlog_parse_index(ptr, end_ptr, true, &index);

      if (ptr == nullptr) {
        break;
      }

      /* Fall through */

    case MLOG_REC_SEC_DELETE_MARK:

      ut_ad(!page || fil_page_type_is_index(page_type));

      ptr = btr_cur_parse_del_mark_set_sec_rec(ptr, end_ptr, page, page_zip);
      break;

    case MLOG_REC_UPDATE_IN_PLACE:
    case MLOG_COMP_REC_UPDATE_IN_PLACE:

      ut_ad(!page || fil_page_type_is_index(page_type));

      if (nullptr !=
          (ptr = mlog_parse_index(
               ptr, end_ptr, type == MLOG_COMP_REC_UPDATE_IN_PLACE, &index))) {
        ut_a(!page ||
             (ibool) !!page_is_comp(page) == dict_table_is_comp(index->table));

        ptr =
            btr_cur_parse_update_in_place(ptr, end_ptr, page, page_zip, index);
      }

      break;

    case MLOG_LIST_END_DELETE:
    case MLOG_COMP_LIST_END_DELETE:
    case MLOG_LIST_START_DELETE:
    case MLOG_COMP_LIST_START_DELETE:

      ut_ad(!page || fil_page_type_is_index(page_type));

      if (nullptr !=
          (ptr = mlog_parse_index(ptr, end_ptr,
                                  type == MLOG_COMP_LIST_END_DELETE ||
                                      type == MLOG_COMP_LIST_START_DELETE,
                                  &index))) {
        ut_a(!page ||
             (ibool) !!page_is_comp(page) == dict_table_is_comp(index->table));

        ptr = page_parse_delete_rec_list(type, ptr, end_ptr, block, index, mtr);
      }

      break;

    case MLOG_LIST_END_COPY_CREATED:
    case MLOG_COMP_LIST_END_COPY_CREATED:

      ut_ad(!page || fil_page_type_is_index(page_type));

      if (nullptr != (ptr = mlog_parse_index(
                          ptr, end_ptr, type == MLOG_COMP_LIST_END_COPY_CREATED,
                          &index))) {
        ut_a(!page ||
             (ibool) !!page_is_comp(page) == dict_table_is_comp(index->table));

        ptr = page_parse_copy_rec_list_to_created_page(ptr, end_ptr, block,
                                                       index, mtr);
      }

      break;

    case MLOG_PAGE_REORGANIZE:
    case MLOG_COMP_PAGE_REORGANIZE:
    case MLOG_ZIP_PAGE_REORGANIZE:

      ut_ad(!page || fil_page_type_is_index(page_type));

      if (nullptr !=
          (ptr = mlog_parse_index(ptr, end_ptr, type != MLOG_PAGE_REORGANIZE,
                                  &index))) {
        ut_a(!page ||
             (ibool) !!page_is_comp(page) == dict_table_is_comp(index->table));

        ptr = btr_parse_page_reorganize(
            ptr, end_ptr, index, type == MLOG_ZIP_PAGE_REORGANIZE, block, mtr);
      }

      break;

    case MLOG_PAGE_CREATE:
    case MLOG_COMP_PAGE_CREATE:

      /* Allow anything in page_type when creating a page. */
      ut_a(!page_zip);

      page_parse_create(block, type == MLOG_COMP_PAGE_CREATE, FIL_PAGE_INDEX);

      break;

    case MLOG_PAGE_CREATE_RTREE:
    case MLOG_COMP_PAGE_CREATE_RTREE:

      page_parse_create(block, type == MLOG_COMP_PAGE_CREATE_RTREE,
                        FIL_PAGE_RTREE);

      break;

    case MLOG_PAGE_CREATE_SDI:
    case MLOG_COMP_PAGE_CREATE_SDI:

      page_parse_create(block, type == MLOG_COMP_PAGE_CREATE_SDI, FIL_PAGE_SDI);

      break;

    case MLOG_UNDO_INSERT:

      ut_ad(!page || page_type == FIL_PAGE_UNDO_LOG);

      ptr = trx_undo_parse_add_undo_rec(ptr, end_ptr, page);

      break;

    case MLOG_UNDO_ERASE_END:

      ut_ad(!page || page_type == FIL_PAGE_UNDO_LOG);

      ptr = trx_undo_parse_erase_page_end(ptr, end_ptr, page, mtr);

      break;

    case MLOG_UNDO_INIT:

      /* Allow anything in page_type when creating a page. */

      ptr = trx_undo_parse_page_init(ptr, end_ptr, page, mtr);

      break;
    case MLOG_UNDO_HDR_CREATE:
    case MLOG_UNDO_HDR_REUSE:

      ut_ad(!page || page_type == FIL_PAGE_UNDO_LOG);

      ptr = trx_undo_parse_page_header(type, ptr, end_ptr, page, mtr);

      break;

    case MLOG_REC_MIN_MARK:
    case MLOG_COMP_REC_MIN_MARK:

      ut_ad(!page || fil_page_type_is_index(page_type));

      /* On a compressed page, MLOG_COMP_REC_MIN_MARK
      will be followed by MLOG_COMP_REC_DELETE
      or MLOG_ZIP_WRITE_HEADER(FIL_PAGE_PREV, FIL_nullptr)
      in the same mini-transaction. */

      ut_a(type == MLOG_COMP_REC_MIN_MARK || !page_zip);

      ptr = btr_parse_set_min_rec_mark(
          ptr, end_ptr, type == MLOG_COMP_REC_MIN_MARK, page, mtr);

      break;

    case MLOG_REC_DELETE:
    case MLOG_COMP_REC_DELETE:

      ut_ad(!page || fil_page_type_is_index(page_type));

      if (nullptr !=
          (ptr = mlog_parse_index(ptr, end_ptr, type == MLOG_COMP_REC_DELETE,
                                  &index))) {
        ut_a(!page ||
             (ibool) !!page_is_comp(page) == dict_table_is_comp(index->table));

        ptr = page_cur_parse_delete_rec(ptr, end_ptr, block, index, mtr);
      }

      break;

    case MLOG_IBUF_BITMAP_INIT:

      /* Allow anything in page_type when creating a page. */

      ptr = ibuf_parse_bitmap_init(ptr, end_ptr, block, mtr);

      break;

    case MLOG_INIT_FILE_PAGE:
    case MLOG_INIT_FILE_PAGE2:

      /* Allow anything in page_type when creating a page. */

      ptr = fsp_parse_init_file_page(ptr, end_ptr, block);

      break;

    case MLOG_WRITE_STRING:

      ut_ad(!page || page_type != FIL_PAGE_TYPE_ALLOCATED || page_no == 0);

      ptr = mlog_parse_string(ptr, end_ptr, page, page_zip);

      break;

    case MLOG_ZIP_WRITE_NODE_PTR:

      ut_ad(!page || fil_page_type_is_index(page_type));

      ptr = page_zip_parse_write_node_ptr(ptr, end_ptr, page, page_zip);

      break;

    case MLOG_ZIP_WRITE_BLOB_PTR:

      ut_ad(!page || fil_page_type_is_index(page_type));

      ptr = page_zip_parse_write_blob_ptr(ptr, end_ptr, page, page_zip);

      break;

    case MLOG_ZIP_WRITE_HEADER:

      ut_ad(!page || fil_page_type_is_index(page_type));

      ptr = page_zip_parse_write_header(ptr, end_ptr, page, page_zip);

      break;

    case MLOG_ZIP_PAGE_COMPRESS:

      /* Allow anything in page_type when creating a page. */
      ptr = page_zip_parse_compress(ptr, end_ptr, page, page_zip);
      break;

    case MLOG_ZIP_PAGE_COMPRESS_NO_DATA:

      if (nullptr != (ptr = mlog_parse_index(ptr, end_ptr, true, &index))) {
        ut_a(!page || ((ibool) !!page_is_comp(page) ==
                       dict_table_is_comp(index->table)));

        ptr = page_zip_parse_compress_no_data(ptr, end_ptr, page, page_zip,
                                              index);
      }

      break;

    case MLOG_TEST:
#ifndef UNIV_HOTBACKUP
      if (log_test != nullptr) {
        ptr = log_test->parse_mlog_rec(ptr, end_ptr);
      } else {
        /* Just parse and ignore record to pass it and go forward. Note that
        this record is also used in the innodb.log_first_rec_group mtr test. The
        record is written in the buf0flu.cc when flushing page in that case. */
        Log_test::Key key;
        Log_test::Value value;
        lsn_t start_lsn, end_lsn;

        ptr = Log_test::parse_mlog_rec(ptr, end_ptr, key, value, start_lsn,
                                       end_lsn);
      }
      break;
#endif /* !UNIV_HOTBACKUP */
       /* Fall through. */

    default:
      ptr = nullptr;
      recv_sys->found_corrupt_log = true;
  }

  if (index != nullptr) {
    dict_table_t *table = index->table;

    dict_mem_index_free(index);
    dict_mem_table_free(table);
  }

  return (ptr);
}

/** recv_writer thread tasked with flushing dirty pages from the buffer
pools. */

static void recv_read_log_seg(log_t &log, byte *buf, lsn_t start_lsn,
                              lsn_t end_lsn) {
 // log_background_threads_inactive_validate(log); /* Commenting it */

  do {
    lsn_t source_offset;

    source_offset = log_files_real_offset_for_lsn(log, start_lsn);

    ut_a(end_lsn - start_lsn <= ULINT_MAX);

    ulint len;

    len = (ulint)(end_lsn - start_lsn);

    ut_ad(len != 0);

    if ((source_offset % log.file_size) + len > log.file_size) {
      /* If the above condition is true then len
      (which is ulint) is > the expression below,
      so the typecast is ok */
      len = (ulint)(log.file_size - (source_offset % log.file_size));
    }

    ++log.n_log_ios;

    ut_a(source_offset / UNIV_PAGE_SIZE <= PAGE_NO_MAX);

    const page_no_t page_no =
        static_cast<page_no_t>(source_offset / univ_page_size.physical());

    dberr_t

        err = fil_redo_io(
            IORequestLogRead, page_id_t(log.files_space_id, page_no),
            univ_page_size, (ulint)(source_offset % univ_page_size.physical()),
            len, buf);

    ut_a(err == DB_SUCCESS);

    start_lsn += len;
    buf += len;

  } while (start_lsn != end_lsn);
}


/** Initialize crash recovery environment. Can be called iff
recv_needed_recovery == false. */
static void sbuf_init_setup() {

	  if (sbuf_recv_sys != nullptr) {
	    return;
	  }

	  sbuf_recv_sys = static_cast<recv_sys_t *>(ut_zalloc_nokey(sizeof(*recv_sys)));

		//mysql_mutex_init(PSI_NOT_INSTRUMENTED, &recv_sys_mutex, MY_MUTEX_INIT_FAST);
	  mutex_create(LATCH_ID_RECV_SYS, &sbuf_recv_sys->mutex);
	 // mutex_create(LATCH_ID_RECV_WRITER, &sbuf_rev_sys->writer_mutex);

	  sbuf_recv_sys->spaces = nullptr;


	  recv_sys_t * recv_sys=sbuf_recv_sys;
	  recv_sys->flush_start = os_event_create(0);
	  recv_sys->flush_end = os_event_create(0);
	  if (buf_pool_get_curr_size() >= (10 * 1024 * 1024) &&
	      (buf_pool_get_curr_size() >= ((512 + 128) * UNIV_PAGE_SIZE))) {
	    /* Buffer pool of size greater than 10 MB. */
	    recv_n_pool_free_frames = 512;
	  }

	  recv_sys->buf = static_cast<byte *>(ut_malloc_nokey(RECV_PARSING_BUF_SIZE));
	  recv_sys->buf_len = RECV_PARSING_BUF_SIZE;

	  recv_sys->len = 0;
	  recv_sys->recovered_offset = 0;

	  using Spaces = recv_sys_t::Spaces;

	  recv_sys->spaces = UT_NEW(Spaces(), mem_log_recv_space_hash_key);

	  recv_sys->n_addrs = 0;

	  recv_sys->apply_log_recs = false;
	  recv_sys->apply_batch_on = false;
	  recv_sys->is_cloned_db = false;

	  recv_sys->last_block_buf_start =
	      static_cast<byte *>(ut_malloc_nokey(2 * OS_FILE_LOG_BLOCK_SIZE));

	  recv_sys->last_block = static_cast<byte *>(
	      ut_align(recv_sys->last_block_buf_start, OS_FILE_LOG_BLOCK_SIZE));

	  recv_sys->found_corrupt_log = false;
	  recv_sys->found_corrupt_fs = false;

	  recv_max_page_lsn = 0;

	  /* Call the constructor for both placement new objects. */
	  new (&recv_sys->dblwr) recv_dblwr_t();

	  new (&recv_sys->deleted) recv_sys_t::Missing_Ids();

	  new (&recv_sys->missing_ids) recv_sys_t::Missing_Ids();

	  recv_sys->metadata_recover = UT_NEW_NOKEY(MetadataRecover());


	  sbuf_cur_mheap= new sbuf_struct_gen_var_t();//static_cast<redo_mem_heap * >(ut_malloc_nokey(sizeof(struct redo_mem_heap)));
	  sbuf_cur_mheap->st_chkpt=0;
	  sbuf_cur_mheap->heap=mem_heap_create_typed(256, MEM_HEAP_FOR_RECV_SYS);
	  sbuf_old_mheap= new sbuf_struct_gen_var_t(); //static_cast<redo_mem_heap * >(ut_malloc_nokey(sizeof(struct redo_mem_heap)));
	  sbuf_old_mheap->st_chkpt=0;
	  sbuf_old_mheap->heap=mem_heap_create_typed(256, MEM_HEAP_FOR_RECV_SYS);

}

static void recv_reset_buffer() {
	recv_sys_t * recv_sys=sbuf_recv_sys;
  ut_memmove(recv_sys->buf, recv_sys->buf + recv_sys->recovered_offset,
             recv_sys->len - recv_sys->recovered_offset);

  recv_sys->len -= recv_sys->recovered_offset;

  recv_sys->recovered_offset = 0;
}
/** Empties the hash table when it has been fully processed. */
static void recv_sys_empty_hash() {
	recv_sys_t * recv_sys=sbuf_recv_sys;
   ut_ad(mutex_own(&recv_sys->mutex));

  if (recv_sys->n_addrs != 0) {
    ib::fatal(ER_IB_MSG_699, ulonglong{recv_sys->n_addrs});
  }

  if( recv_sys->spaces != nullptr){
	  for (auto &space : *recv_sys->spaces) {
	     if (space.second.m_heap != nullptr) {
	       mem_heap_free(space.second.m_heap);
	       space.second.m_heap = nullptr;
	     }
	   }
  }


  UT_DELETE(recv_sys->spaces);

  using Spaces = recv_sys_t::Spaces;

  recv_sys->spaces = UT_NEW(Spaces(), mem_log_recv_space_hash_key);
}

static void recv_track_changes_of_recovered_lsn() {
	recv_sys_t * recv_sys=sbuf_recv_sys;
  if (recv_sys->parse_start_lsn == 0) {
    return;
  }
  /* If we have already found the first block with mtr beginning there,
  we started to track boundaries between blocks. Since then we track
  all proper values of first_rec_group for consecutive blocks.
  The reason for that is to ensure that the first_rec_group of the last
  block is correct. Even though we do not depend during this recovery
  on that value, it would become important if we crashed later, because
  the last recovered block would become the first used block in redo and
  since then we would depend on a proper value of first_rec_group there.
  The checksums of log blocks should detect if it was incorrect, but the
  checksums might be disabled in the configuration. */
  const auto old_block =
      recv_sys->previous_recovered_lsn / OS_FILE_LOG_BLOCK_SIZE;

  const auto new_block = recv_sys->recovered_lsn / OS_FILE_LOG_BLOCK_SIZE;

  if (old_block != new_block) {
    ut_a(new_block > old_block);

    recv_sys->last_block_first_rec_group =
        recv_sys->recovered_lsn % OS_FILE_LOG_BLOCK_SIZE;
  }

  recv_sys->previous_recovered_lsn = recv_sys->recovered_lsn;
}

static void recv_data_copy_to_buf(byte *buf, recv_t *recv) {
  ulint len = recv->len;
  recv_data_t *recv_data = recv->data;

  while (len > 0) {
    ulint part_len;

    if (len > RECV_DATA_BLOCK_SIZE) {
      part_len = RECV_DATA_BLOCK_SIZE;
    } else {
      part_len = len;
    }

    memcpy(buf, ((byte *)recv_data) + sizeof(*recv_data), part_len);

    buf += part_len;
    len -= part_len;

    recv_data = recv_data->next;
  }
}

/** Resize the recovery parsing buffer upto log_buffer_size */
static bool recv_sys_resize_buf() {

	recv_sys_t * recv_sys=sbuf_recv_sys;
  ut_ad(recv_sys->buf_len <= srv_log_buffer_size);

  /* If the buffer cannot be extended further, return false. */
  if (recv_sys->buf_len == srv_log_buffer_size) {
    ib::error(ER_IB_MSG_723, srv_log_buffer_size);
    return false;
  }

  /* Extend the buffer by double the current size with the resulting
  size not more than srv_log_buffer_size. */
  recv_sys->buf_len = ((recv_sys->buf_len * 2) >= srv_log_buffer_size)
                          ? srv_log_buffer_size
                          : recv_sys->buf_len * 2;

  /* Resize the buffer to the new size. */
  recv_sys->buf =
      static_cast<byte *>(ut_realloc(recv_sys->buf, recv_sys->buf_len));

  ut_ad(recv_sys->buf != nullptr);

  /* Return error and fail the recovery if not enough memory available */
  if (recv_sys->buf == nullptr) {
    ib::error(ER_IB_MSG_740);
    return false;
  }
  fprintf(stderr,"sbuf - increased buffer size to : %d\n",recv_sys->buf_len);
  return true;
}

/** Get the page map for a tablespace. It will create one if one isn't found.
@param[in]	space_id	Tablespace ID for which page map required.
@param[in]	create		false if lookup only
@return the space data or null if not found */
static recv_sys_t::Space *recv_get_page_map(space_id_t space_id, bool create) {


  recv_sys_t * recv_sys=sbuf_recv_sys;
  auto it = recv_sys->spaces->find(space_id);

  if (it != recv_sys->spaces->end()) {
    return (&it->second);

  } else if (create) {

	//mem_heap_t *heap;
	//heap = mem_heap_create_typed(256, MEM_HEAP_FOR_RECV_SYS);

    using Space = recv_sys_t::Space;
    using value_type = recv_sys_t::Spaces::value_type;

    auto where =
        recv_sys->spaces->insert(it, value_type(space_id, Space()));

   //sbuf_gen_var.logfile<<"Recv hash created for space: "<<space_id<<endl;
    return (&where->second);
  }

  return (nullptr);
}

/** Gets the list of log records for a <space, page>.
@param[in]	space_id	Tablespace ID
@param[in]	page_no		Page number
@return the redo log entries or nullptr if not found */
static recv_addr_t *recv_get_rec(space_id_t space_id, page_no_t page_no) {
  recv_sys_t::Space *space;

  space = recv_get_page_map(space_id, false);

  if (space != nullptr) {
    auto it = space->m_pages.find(page_no);

    if (it != space->m_pages.end()) {
      return (it->second);
    }
  }

  return (nullptr);
}


/** Applies the hashed log records to the page, if the page lsn is less than the
lsn of a log record. This can be called when a buffer page has just been
read in, or also for a page already in the buffer pool.
@param[in]	just_read_in	true if the IO handler calls this for a freshly
                                read page
@param[in,out]	block		Buffer block */
void sbuf_recv_recover_page( bool just_read_in,  buf_block_t *block) {


	if(!sbuf_refresh_on){
		return;
	}

	recv_sys_t * recv_sys = sbuf_recv_sys;
    mutex_enter(&recv_sys->mutex);

/*
  if (recv_sys->apply_log_recs == false) {
	fprintf(stderr, "Log record should not be applied for page(%d,%d) as apply_log_recs== false, is just_read_in: %d\n",block->page.id.space(), block->page.id.page_no(), just_read_in);
    mutex_exit(&recv_sys->mutex);

    return;
  }
  */

  recv_addr_t *recv_addr;

  recv_addr = recv_get_rec(block->page.id.space(), block->page.id.page_no());

  mutex_exit(&recv_sys->mutex);

  if(recv_addr==nullptr){
	  return;
  }


  mysql_mutex_lock(&recv_addr->page_mutex);

  if (recv_addr->state == RECV_BEING_PROCESSED ||
      recv_addr->state == RECV_PROCESSED) {
	  mysql_mutex_unlock(&recv_addr->page_mutex);
//      mutex_exit(&recv_sys->mutex);
    return;
  }

  if(just_read_in){
	  fprintf(stderr,"Just read in recovery for page(%d, %d)\n",recv_addr->space,recv_addr->page_no);
  }


#ifndef UNIV_HOTBACKUP
  /*
  buf_page_t bpage = block->page;

  if (!fsp_is_system_temporary(bpage.id.space()) &&
      (arch_page_sys != nullptr && arch_page_sys->is_active())) {
    page_t *frame;
    lsn_t frame_lsn;

    frame = bpage.zip.data;

    if (!frame) {
      frame = block->frame;
    }
    frame_lsn = mach_read_from_8(frame + FIL_PAGE_LSN);

    arch_page_sys->track_page(&bpage, LSN_MAX, frame_lsn, true);
  }
  */
#endif /* !UNIV_HOTBACKUP */


#ifdef UNIV_DEBUG
  lsn_t max_lsn;

  ut_d(max_lsn = log_sys->scanned_lsn);
#endif /* UNIV_DEBUG */

  recv_addr->state = RECV_BEING_PROCESSED;

  //mutex_exit(&recv_sys->mutex);

  mtr_t mtr;

  mtr_start(&mtr);

  mtr_set_log_mode(&mtr, MTR_LOG_NONE);

  page_t *page = block->frame;

  page_zip_des_t *page_zip = buf_block_get_page_zip(block);

#ifndef UNIV_HOTBACKUP
  if (just_read_in) {
    /* Move the ownership of the x-latch on the page to
    this OS thread, so that we can acquire a second
    x-latch on it.  This is needed for the operations to
    the page to pass the debug checks. */

    rw_lock_x_lock_move_ownership(&block->lock);
  }

  bool success = buf_page_get_known_nowait(
      RW_X_LATCH, block, Cache_hint::KEEP_OLD, __FILE__, __LINE__, &mtr);
  ut_a(success);

  buf_block_dbg_add_level(block, SYNC_NO_ORDER_CHECK);
#endif /* !UNIV_HOTBACKUP */

  /* Read the newest modification lsn from the page */
  lsn_t page_lsn = mach_read_from_8(page + FIL_PAGE_LSN);


#ifndef UNIV_HOTBACKUP

  /* It may be that the page has been modified in the buffer
  pool: read the newest modification LSN there */

  lsn_t page_newest_lsn;

  page_newest_lsn = buf_page_get_newest_modification(&block->page);
  //sbuf_gen_var.logfile<<"Page newest lsn: "<<page_newest_lsn<<endl;


  if (page_newest_lsn) {
    page_lsn = page_newest_lsn;
  }
  //sbuf_gen_var.logfile<<"Page lsn: "<<page_lsn<<endl;

#else  /* !UNIV_HOTBACKUP */
  /* In recovery from a backup we do not really use the buffer pool */
  lsn_t page_newest_lsn = 0;
  /* Count applied and skipped log records */
  size_t applied_recs = 0;
  size_t skipped_recs = 0;
#endif /* !UNIV_HOTBACKUP */

#ifndef UNIV_HOTBACKUP
  lsn_t end_lsn = 0;

#endif /* !UNIV_HOTBACKUP */
//  lsn_t start_lsn = 0;

  bool modification_to_page = false;
  bool just_read_in_skip=false;

  for (auto recv = UT_LIST_GET_FIRST(recv_addr->rec_list); recv != nullptr;
      ) {
#ifndef UNIV_HOTBACKUP
    end_lsn = recv->end_lsn;

    ut_ad(end_lsn <= max_lsn);
#endif /* !UNIV_HOTBACKUP */

    bool can_remove=false;
    byte *buf;

    if (recv->len > RECV_DATA_BLOCK_SIZE) {
      /* We have to copy the record body to a separate
      buffer */

      buf = static_cast<byte *>(ut_malloc_nokey(recv->len));

      recv_data_copy_to_buf(buf, recv);
    } else {
      buf = ((byte *)(recv->data)) + sizeof(recv_data_t);
    }

  // sbuf_gen_var.logfile<<"mtr record Lsn: "<<recv->start_lsn<<" -> "<<recv->end_lsn<<", Len: "<<recv->len<<", Type: "<<get_mlog_string(recv->type)<<endl;

    if (recv->type == MLOG_INIT_FILE_PAGE) {
      page_lsn = page_newest_lsn;

      memset(FIL_PAGE_LSN + page, 0, 8);
      memset(UNIV_PAGE_SIZE - FIL_PAGE_END_LSN_OLD_CHKSUM + page, 0, 8);

      if (page_zip) {
        memset(FIL_PAGE_LSN + page_zip->data, 0, 8);
      }
    }

    /* Ignore applying the redo logs for tablespace that is
    truncated. Truncated tablespaces are handled explicitly
    post-recovery, where we will restore the tablespace back
    to a normal state.

    Applying redo at this stage will cause problems because the
    redo will have action recorded on page before tablespace
    was re-inited and that would lead to a problem later. */

    if (recv->start_lsn >= page_lsn  && (!just_read_in ||  recv->end_lsn < sbuf_consistent_lsn)
#ifndef UNIV_HOTBACKUP
        && undo::is_active(recv_addr->space)
#endif /* !UNIV_HOTBACKUP */
    ) {

      lsn_t end_lsn;
      //lsn_t start_lsn;
      if (!modification_to_page) {
        modification_to_page = true;
    //    start_lsn = recv->start_lsn;
      }

      DBUG_PRINT("ib_log", ("apply " LSN_PF ":"
                            " %s len " ULINTPF " page %u:%u",
                            recv->start_lsn, get_mlog_string(recv->type),
                            recv->len, recv_addr->space, recv_addr->page_no));


      recv_parse_or_apply_log_rec_body(recv->type, buf, buf + recv->len,
                                       recv_addr->space, recv_addr->page_no,
                                       block, &mtr, ULINT_UNDEFINED);

      end_lsn = recv->start_lsn + recv->len;

      mach_write_to_8(FIL_PAGE_LSN + page, end_lsn);

      mach_write_to_8(UNIV_PAGE_SIZE - FIL_PAGE_END_LSN_OLD_CHKSUM + page,
                      end_lsn);

      if (page_zip) {
        mach_write_to_8(FIL_PAGE_LSN + page_zip->data, end_lsn);
      }
      ++applied_recs;
    } else {
      ++skipped_recs;
      can_remove=true;

      if(just_read_in && !just_read_in_skip &&  recv->end_lsn < sbuf_consistent_lsn){
    	  fprintf(stderr,"For page(%d, %d) records are skipped in read in; recv_end_lsn: %ld, consistent_lsn: %ld\n",recv_addr->space,recv_addr->page_no,  recv->end_lsn,sbuf_consistent_lsn );
    	  just_read_in_skip=true;
      }


     //sbuf_gen_var.logfile<<"Page LSN is newer than the mtr, hence ignoring this record. "<<endl;

    }


    if (recv->len > RECV_DATA_BLOCK_SIZE) {
      ut_free(buf);
    }

    struct recv_t * old=recv;

    recv = UT_LIST_GET_NEXT(rec_list, recv);
    if(can_remove && !just_read_in && old ){

    	UT_LIST_REMOVE(recv_addr->rec_list,old);  //Removing old entry from list..
    	ut_free(old->data);
    	delete(old);
    }

  }

#ifdef UNIV_ZIP_DEBUG
  if (fil_page_index_page_check(page)) {
    page_zip_des_t *page_zip = buf_block_get_page_zip(block);

    ut_a(!page_zip || page_zip_validate_low(page_zip, page, nullptr, FALSE));
  }
#endif /* UNIV_ZIP_DEBUG */

#ifndef UNIV_HOTBACKUP
  /*
  if (modification_to_page) {
    buf_flush_recv_note_modification(block, start_lsn, end_lsn);
  }
  */
#else  /* !UNIV_HOTBACKUP */
  UT_NOT_USED(start_lsn);
#endif /* !UNIV_HOTBACKUP */

  /* Make sure that committing mtr does not change the modification
  LSN values of page */

  mtr.discard_modifications();

  mtr_commit(&mtr);

 // mutex_enter(&recv_sys->mutex);

  if (recv_max_page_lsn < page_lsn) {
    recv_max_page_lsn = page_lsn;
  }

  if(just_read_in_skip){
	  recv_addr->state=RECV_NOT_PROCESSED;
  }else{
	  recv_addr->state = RECV_PROCESSED;
	  ut_a(recv_sys->n_addrs > 0);
	  --recv_sys->n_addrs;
  }

  mysql_mutex_unlock(&recv_addr->page_mutex);


//  mutex_exit(&recv_sys->mutex);

#ifdef UNIV_HOTBACKUP
  ib::trace_2() << "Applied " << applied_recs << " Skipped " << skipped_recs;
#endif /* UNIV_HOTBACKUP */
}

static void sbuf_recv_remove_old_entry(recv_addr_t * recv_addr){

	  mysql_mutex_lock(&recv_addr->page_mutex);

	  for (auto recv = UT_LIST_GET_FIRST(recv_addr->rec_list); recv != nullptr;
		      ) {
			  struct recv_t * old=recv;
			  recv = UT_LIST_GET_NEXT(rec_list, recv);
			  if(old->end_lsn < sbuf_rev_sys->checkpoint_lsn  && (sbuf_rev_sys->checkpoint_lsn-old->end_lsn)>1000){
				  UT_LIST_REMOVE(recv_addr->rec_list,old);  //Removing old entry from list..
				  ut_free(old->data);
				  delete(old);
			  }
	  }
	  mysql_mutex_unlock(&recv_addr->page_mutex);
}


static void recv_apply_log_rec(recv_addr_t *recv_addr) {

	recv_sys_t * recv_sys=sbuf_recv_sys;
  if (recv_addr->state == RECV_DISCARDED) {
    ut_a(recv_sys->n_addrs > 0);
    --recv_sys->n_addrs;
    return;
  }

  bool found;
  const page_id_t page_id(recv_addr->space, recv_addr->page_no);


  const page_size_t page_size =
      fil_space_get_page_size(recv_addr->space, &found);


// sbuf_gen_var.logfile<<"=> Apply modification from page: ("<<recv_addr->space<<","<<recv_addr->page_no<<"), is tablespace exist: "<<found<<endl;
// sbuf_gen_var.logfile<<"Recv state: "<<recv_addr->state<<endl;

  if (!found ){ //|| recv_sys->missing_ids.find(recv_addr->space) !=                    recv_sys->missing_ids.end()) {

	  fprintf(stderr,"\nIgnoring changes for page (%d,%d) as tablespace not found\n",recv_addr->space,recv_addr->page_no);

	  return;
    /* Tablespace was discarded or dropped after changes were
    made to it. Or, we have ignored redo log for this tablespace
    earlier and somehow it has been found now. We can't apply
    this redo log out of order. */

    recv_addr->state = RECV_PROCESSED;

    ut_a(recv_sys->n_addrs > 0);
    --recv_sys->n_addrs;

    /* If the tablespace has been explicitly deleted, we
    can safely ignore it. */

    if (recv_sys->deleted.find(recv_addr->space) == recv_sys->deleted.end()) {
      recv_sys->missing_ids.insert(recv_addr->space);
    }

  } else if (recv_addr->state == RECV_NOT_PROCESSED) {
    mutex_exit(&recv_sys->mutex);

    if (buf_page_peek(page_id)) {
      mtr_t mtr;

      mtr_start(&mtr);

      buf_block_t *block;

      block = buf_page_get(page_id, page_size, RW_X_LATCH, &mtr);

      buf_block_dbg_add_level(block, SYNC_NO_ORDER_CHECK);

      aur_recv_recover_page(false, block);

      mtr_commit(&mtr);

    }else {

  //  	sbuf_gen_var.logfile<<"Ignoring because page not present in the buffer_pool  "<<std::endl;
 //   	recv_remove_stale_entry(recv_addr);
    //  recv_read_in_area(page_id);
    }

    mutex_enter(&recv_sys->mutex);
  }else{
	  sbuf_recv_remove_old_entry(recv_addr);
	  fprintf(stderr,"Recovery already completed for to page (%d,%d)\n",recv_addr->space,recv_addr->page_no);
  }
}

/** Empties the hash table of stored log records, applying them to appropriate
pages.
@param[in,out]	log		Redo log
@param[in]	allow_ibuf	if true, ibuf operations are allowed during
                                the application; if false, no ibuf operations
                                are allowed, and after the application all
                                file pages are flushed to disk and invalidated
                                in buffer pool: this alternative means that
                                no new log records can be generated during
                                the application; the caller must in this case
                                own the log mutex */
void sbuf_recv_apply_hashed_log_recs(log_t &log, bool allow_ibuf) {

	recv_sys_t * recv_sys=sbuf_recv_sys;
	//sbuf_gen_var.logfile<<"===> Start applying logs "<<endl;
  for (;;) {
    mutex_enter(&recv_sys->mutex);


    if (!recv_sys->apply_batch_on) {
      break;
    }

    mutex_exit(&recv_sys->mutex);
    fprintf(stderr, "Waiting for recv_sys->mutex\n");

    os_thread_sleep(500000);
  }

  if (!allow_ibuf) {
    recv_no_ibuf_operations = true;
  }

  recv_sys->apply_log_recs = true;
  recv_sys->apply_batch_on = true;

  auto batch_size = recv_sys->n_addrs;

 //sbuf_gen_var.logfile<<"Applying patches for redo log, size: "<<batch_size<<endl;

  static const size_t PCT = 10;

  size_t pct = PCT;
  size_t applied = 0;
  auto unit = batch_size / PCT;

  if (unit <= PCT) {
    pct = 100;
    unit = batch_size;
  }

  auto start_time = ut_time_monotonic();

  for ( auto &space : *recv_sys->spaces) {
    bool dropped;

    //Commented by Sudalai
   // if (space.first != TRX_SYS_SPACE &&
    //    !aur_fil_tablespace_open_for_recovery(space.first)) {
      /* Tablespace was dropped. It should not have been scanned unless it
      is an undo space that was under construction. */
    //  ut_ad(!aur_fil_tablespace_lookup_for_recovery(space.first) ||
      //      fsp_is_undo_tablespace(space.first));

     // dropped = true;
   // } else {
     // dropped = false;
   // }
    dropped=false;
   //sbuf_gen_var.logfile<<"Is Tablespace dropped: "<<dropped<<endl;


    recv_sys_t::Pages::iterator pages =space.second.m_pages.begin();
    //for (auto pages : space.second.m_pages) {
    while(pages!=space.second.m_pages.end()){

      recv_addr_t *recv_addr=pages->second;

      page_no_t page_no=pages->first;

      ut_ad(recv_addr->space == space.first);

      if (dropped) {
        pages->second->state = RECV_DISCARDED;
      }

      recv_apply_log_rec(recv_addr);
      pages++;
      if(recv_addr->rec_list.count == 0 ){ //Delting  empty pages.

    	  space.second.m_pages.erase(page_no);
    	  mysql_mutex_destroy(&recv_addr->page_mutex);

    	  delete(recv_addr);
      }

      ++applied;

      if (unit == 0 || (applied % unit) == 0) {
        ib::info(ER_IB_MSG_708) << pct << "%";

        pct += PCT;

        start_time = ut_time_monotonic();

      } else if (ut_time_monotonic() - start_time >= PRINT_INTERVAL_SECS) {
        start_time = ut_time_monotonic();

        ib::info(ER_IB_MSG_709)
            << std::setprecision(2)
            << ((double)applied * 100) / (double)batch_size << "%";
      }
    }
  }

  /* Wait until all the pages have been processed */

 // while (recv_sys->n_addrs != 0) {
  //  mutex_exit(&recv_sys->mutex);

   // os_thread_sleep(500000);

   // mutex_enter(&recv_sys->mutex);
 // }

  if (!allow_ibuf) {
	fputs("IBUF: ..... Not yet implemented allow_ibuf in apply recv_logs\n");
  }

  recv_sys->apply_log_recs = false;
  recv_sys->apply_batch_on = false;

  //recv_sys_empty_hash();

  mutex_exit(&recv_sys->mutex);

  ib::info(ER_IB_MSG_710);
}



static void sbuf_TrxStart(mlog_id_t type, byte *ptr, byte *end_ptr,
        space_id_t space_id, page_no_t page_no){

	 if ( type ==MLOG_UNDO_HDR_CREATE || type==MLOG_UNDO_HDR_REUSE ){

			 const byte * con_new_ptr=ptr;
			  trx_id_t trx_id = mach_u64_parse_compressed(&con_new_ptr, end_ptr);
			  page_id_t undo_page(space_id,page_no);
			  ut_a(space_id>200);

			  ulint undo_space_num=undo::id2num(space_id);

			  ut_a(undo_space_num<5);

			  ulint fold=(undo_space_num<<32)+(page_no);
			 //sbuf_gen_var.logfile<<"Trx ID: "<<trx_id<<", Page: ("<<undo_page.space()<<","<<undo_page.page_no()<<")"<<std::endl;


			  trx_ids_t::iterator it = std::lower_bound(trx_sys->rw_trx_ids.begin(),
														 trx_sys->rw_trx_ids.end(), trx_id);
			  if(it==trx_sys->rw_trx_ids.end()){
		  // using UndoHdr=sbuf_struct_gen_var_t::UndoHdr;
				  auto it=sbuf_gen_var.m_undohdr->find(fold);

				  if(it!=sbuf_gen_var.m_undohdr->end()){
					  sbuf_gen_var.logfile<<"Undo page already has trx - "<<it->second<<std::endl;
				  }else{
					  using value_type=sbuf_struct_gen_var_t::UndoHdr::value_type;
					  sbuf_gen_var.m_undohdr->insert(it,value_type(fold,trx_id) );
					//  sbuf_gen_var.logfile<<"No. trx length : "<<sys_gen_var.m_undohdr->size()<<std::endl;
				  }

				  trx_sys->rw_trx_ids.push_back(trx_id);
				  trx_sys->max_trx_id=trx_id+1;
			  }

	  }

}

static void sbuf_TrxCommit(mlog_id_t type, byte *ptr, byte *end_ptr,
        space_id_t space_id, page_no_t page_no){
	if(type == MLOG_2BYTES) {
		    	bool undospace=false;
		    	if(sbuf_gen_var.m_undo_space.size()!=undo::spaces->m_spaces.size()){

		    		sbuf_gen_var.m_undo_space.clear();
		    		for(auto sp=undo::spaces->m_spaces.begin(); sp !=undo::spaces->m_spaces.end();++sp){
		    			sys_gen_var.m_undo_space.push_back((*sp)->id());
		    		}

		    	}
		    	for ( auto sp= sbuf_gen_var.m_undo_space.begin(); sp!=sbuf_gen_var.m_undo_space.end() && !undospace; sp++){
		    		if(*sp == space_id){
		    			undospace=true;
		    		}
		    	}

		    	//sbuf_gen_var.logfile<<" Is undo space: "<<undospace<<std::endl;
		    	if(undospace){
		            ulint offs = mach_read_from_2(ptr);
		            ptr+=2;
		            const byte * con_ptr =ptr;
		            ulint val=mach_parse_compressed(&con_ptr, end_ptr);
		            if(offs==TRX_UNDO_SEG_HDR  && (val >=2 && val <=4) ){

		            //	sbuf_gen_var.logfile<<"Undo page change - trx commit "<<std::endl;

		            	ulint undo_num=undo::id2num(space_id);
		            	ulint fold=(undo_num<<32)+(page_no);

		            	auto it=sys_gen_var.m_undohdr->find(fold);
		            	if(it!=sys_gen_var.m_undohdr->end()){

		            		trx_id_t trx_id=it->second;
		            		sbuf_gen_var.logfile<<"Trx commit: "<<trx_id<<", Page: ("<<space_id<<","<<page_no<<")"<<std::endl;

		            		sbuf_gen_var.m_undohdr->erase(it);
		            		 trx_ids_t::iterator it1 = std::lower_bound(trx_sys->rw_trx_ids.begin(),
		            			                                             trx_sys->rw_trx_ids.end(), trx_id);

		            		if(trx_sys->rw_trx_ids.end() != it1){
		            			trx_sys->rw_trx_ids.erase(it1);
		            			sbuf_gen_var.logfile<<"Trx : "<<trx_id<<" removed from rw list"<<std::endl;
		            		}

		            		 trx_id_t min_id = trx_sys->rw_trx_ids.empty() ? trx_sys->max_trx_id
		            		                                                : trx_sys->rw_trx_ids.front();
		            		  trx_sys->min_active_id.store(min_id);


		            	}else{
		            		sbuf_gen_var.logfile<<"Trx commit undo details missing for , Page: ("<<space_id<<","<<page_no<<")"<<std::endl;
		            	}

		            }

		    	}
		    }
}

/** Tries to parse a single log record.
@param[out]	type		log record type
@param[in]	ptr		pointer to a buffer
@param[in]	end_ptr		end of the buffer
@param[out]	space_id	tablespace identifier
@param[out]	page_no		page number
@param[out]	body		start of log record body
@return length of the record, or 0 if the record was not complete */
static ulint recv_parse_log_rec(mlog_id_t *type, byte *ptr, byte *end_ptr,
                                space_id_t *space_id, page_no_t *page_no,
                                byte **body, bool process_txid) {
  byte *new_ptr;

  *body = nullptr;

 // ulint offset;
  //ib_uint64_t dval;


  recv_sys_t * recv_sys=sbuf_recv_sys;

  UNIV_MEM_INVALID(type, sizeof *type);
  UNIV_MEM_INVALID(space_id, sizeof *space_id);
  UNIV_MEM_INVALID(page_no, sizeof *page_no);
  UNIV_MEM_INVALID(body, sizeof *body);

  if (ptr == end_ptr) {
    return (0);
  }

  switch (*ptr) {
#ifdef UNIV_LOG_LSN_DEBUG
    case MLOG_LSN | MLOG_SINGLE_REC_FLAG:
    case MLOG_LSN:

      new_ptr =
          mlog_parse_initial_log_record(ptr, end_ptr, type, space_id, page_no);

      if (new_ptr != nullptr) {
        const lsn_t lsn = static_cast<lsn_t>(*space_id) << 32 | *page_no;

        ut_a(lsn == recv_sys->recovered_lsn);
      }

      *type = MLOG_LSN;
      return (new_ptr == nullptr ? 0 : new_ptr - ptr);
#endif /* UNIV_LOG_LSN_DEBUG */

    case MLOG_MULTI_REC_END:
    case MLOG_DUMMY_RECORD:
      *page_no = FIL_NULL;
      *space_id = SPACE_UNKNOWN;
      *type = static_cast<mlog_id_t>(*ptr);
      return (1);

    case MLOG_MULTI_REC_END | MLOG_SINGLE_REC_FLAG:
    case MLOG_DUMMY_RECORD | MLOG_SINGLE_REC_FLAG:
      recv_sys->found_corrupt_log = true;
      return (0);

    case MLOG_TABLE_DYNAMIC_META:
    case MLOG_TABLE_DYNAMIC_META | MLOG_SINGLE_REC_FLAG:

    sbuf_gen_var.logfile<<"MLOG_TABLE_DYNAMIC_META not yet implemented "<<endl;

      table_id_t id;
      uint64 version;

      *page_no = FIL_NULL;
      *space_id = SPACE_UNKNOWN;


      new_ptr =
          mlog_parse_initial_dict_log_record(ptr, end_ptr, type, &id, &version);

      if (new_ptr != nullptr) {
        new_ptr = recv_sys->metadata_recover->parseMetadataLog(
            id, version, new_ptr, end_ptr);
      }

      return (new_ptr == nullptr ? 0 : new_ptr - ptr);

  }
  if(MLOG_SAS_DDL == (*ptr & ~MLOG_SINGLE_REC_FLAG) ){
     	*page_no=FIL_NULL;
     	*space_id=SPACE_UNKNOWN;
     	*type=static_cast<mlog_id_t>(*ptr & ~MLOG_SINGLE_REC_FLAG);
     	char tablename[200];
     	char * table=tablename;
     	new_ptr=mlog_parse_sas_drop_table(ptr, end_ptr,table);
     	if (new_ptr == nullptr) {
     	    return (0);
     	}
     	sbuf_gen_var.logfile<<"Drop table : "<<table<<std::endl;


     	mysql_mutex_lock(&sbuf_tmr_mutex);

     	sbuf_struct_gen_var_t * drop = static_cast<sbuf_struct_gen_var_t *>(
     	      ut_malloc_nokey(sizeof(sbuf_struct_gen_var_t)));

     	  strncpy(drop->table_name,table,strlen(table));

     	  drop->table_name[strlen(table)]='\0';

     	  UT_LIST_ADD_LAST(sbuf_tmr_table_list, drop);


     	mysql_mutex_unlock(&sbuf_tmr_mutex);


     	/*

     	close_cached_tables(nullptr,nullptr,false, 300 );


     	mutex_enter(&dict_sys->mutex);
     	dict_table_t * dtable=dict_table_check_if_in_cache_low(table);
     	if(dtable != NULL){

         	sbuf_gen_var.logfile<<"Drop table: "<< dtable->name<<" - refcount="<<dtable->get_ref_count()<<" - Discard_after_ddl: "<<dtable->discard_after_ddl<<std::endl;

         	if(dtable->get_ref_count()==0){
             	sbuf_gen_var.logfile<<"Drop table: "<< dtable->name<<" - cache removed "<<std::endl;
             	dict_table_remove_from_cache(dtable);
         	}
         	//To DO:  FLUSH TABLES.


     	}else{
         	sbuf_gen_var.logfile<<"Drop table: "<< table<<" - No cahe "<<std::endl;
     	}
     	mutex_exit(&dict_sys->mutex);

		*/

     	return (new_ptr - ptr);
  }


  new_ptr =
      mlog_parse_initial_log_record(ptr, end_ptr, type, space_id, page_no);

  //sbuf_gen_var.logfile<<"Log record - [ Type:  "<<*type<<", space: "<<*space_id<<", page: "<<*page_no<<endl;

  *body = new_ptr;

  if (new_ptr == nullptr) {
    return (0);
  }

  if(process_txid  ) {

	 if ( (*type) ==MLOG_UNDO_HDR_CREATE || (*type)==MLOG_UNDO_HDR_REUSE ){
		 sbuf_TrxStart(*type, new_ptr,end_ptr, *space_id, *page_no);
	 }else if((*type) == MLOG_2BYTES) {
		 sbuf_TrxCommit(*type, new_ptr,end_ptr, *space_id, *page_no);
	 }

  }


  /*
  if((*space_id) == TRX_SYS_SPACE && (*page_no) == TRX_SYS_PAGE_NO){

	  if( (*type) ==MLOG_8BYTES){

		  //recv_apply_trx_rec(new_ptr-ptr);
		  offset = mach_read_from_2(new_ptr);
		  if ( offset == 15908){
				 new_ptr += 2;

				 const byte * con_new_ptr=new_ptr;
				 dval = mach_u64_parse_compressed(&con_new_ptr, end_ptr);
				 if (con_new_ptr == NULL) {
					 return 0;
				 }

				sbuf_gen_var.logfile<<"Trx record  - ID : "<<(dval-1);

				 trx_sys_mutex_enter();

				// trx->id = trx_sys_get_new_trx_id();

				 trx_sys->rw_trx_ids.push_back(dval-1);
				 trx_sys->max_trx_id=dval;
				 trx_sys_mutex_exit();
				 return (con_new_ptr-ptr);
		  }

	  }

  }
  */

  new_ptr = recv_parse_or_apply_log_rec_body(*type, new_ptr, end_ptr, *space_id,
                                             *page_no, nullptr, nullptr,
                                             new_ptr - ptr);
  if (new_ptr == nullptr) {
    return (0);
  }

  return (new_ptr - ptr);
}


static bool recv_update_bytes_to_ignore_before_checkpoint(
    size_t next_parsed_bytes) {

	recv_sys_t * recv_sys=sbuf_recv_sys;
  auto &to_ignore = recv_sys->bytes_to_ignore_before_checkpoint;

  if (to_ignore != 0) {
    if (to_ignore >= next_parsed_bytes) {
      to_ignore -= next_parsed_bytes;
    } else {
      to_ignore = 0;
    }
    return (true);
  }

  return (false);
}



/** Adds a new log record to the hash table of log records.
@param[in]	type		log record type
@param[in]	space_id	Tablespace id
@param[in]	page_no		page number
@param[in]	body		log record body
@param[in]	rec_end		log record end
@param[in]	start_lsn	start lsn of the mtr
@param[in]	end_lsn		end lsn of the mtr */
static void recv_add_to_hash_table(mlog_id_t type, space_id_t space_id,
                                   page_no_t page_no, byte *body, byte *rec_end,
                                   lsn_t start_lsn, lsn_t end_lsn) {
  ut_ad(type != MLOG_FILE_DELETE);
  ut_ad(type != MLOG_FILE_CREATE);
  ut_ad(type != MLOG_FILE_RENAME);
  ut_ad(type != MLOG_DUMMY_RECORD);
  ut_ad(type != MLOG_INDEX_LOAD);

  recv_sys_t * recv_sys=sbuf_recv_sys;
  recv_sys_t::Space *space;

  space = recv_get_page_map(space_id, true);
  cur_heap->end_chkpt=redo_checkpoint_no;
  if(cur_heap->st_chkpt==0){
	  cur_heap->st_chkpt=redo_checkpoint_no;
  }

  recv_t *recv;

  //recv = static_cast<recv_t *>(mem_heap_alloc(space->m_heap, sizeof(*recv)));
  recv = new recv_t(); //static_cast<recv_t *>(mem_heap_alloc(cur_heap->heap, sizeof(*recv)));


  recv->type = type;
  recv->end_lsn = end_lsn;
  recv->len = rec_end - body;
  recv->start_lsn = start_lsn;

  auto it = space->m_pages.find(page_no);

  recv_addr_t *recv_addr;

  if (it != space->m_pages.end()) {
	//sbuf_gen_var.logfile<<"Page entry already exist for page: "<<page_no<<endl;
    recv_addr = it->second;

  } else {
    recv_addr = new recv_addr_t(); //static_cast<recv_addr_t *>(ut_zalloc_nokey(sizeof(*recv_addr)));
        //mem_heap_alloc(cur_heap->heap, sizeof(*recv_addr)));

    recv_addr->space = space_id;
    recv_addr->page_no = page_no;
    recv_addr->state = RECV_PROCESSED;

	mysql_mutex_init(PSI_NOT_INSTRUMENTED, &recv_addr->page_mutex, MY_MUTEX_INIT_FAST);

    UT_LIST_INIT(recv_addr->rec_list, &recv_t::rec_list);

    using value_type = recv_sys_t::Pages::value_type;

    space->m_pages.insert(it, value_type(page_no, recv_addr));

  }

  recv_data_t **prev_field;

   prev_field = &recv->data;

   /* Store the log record body in chunks of less than UNIV_PAGE_SIZE:
   the heap grows into the buffer pool, and bigger chunks could not
   be allocated */

   while (rec_end > body) {
     ulint len = rec_end - body;

     if (len > RECV_DATA_BLOCK_SIZE) {
       len = RECV_DATA_BLOCK_SIZE;
     }

     recv_data_t *recv_data;

     //recv_data = static_cast<recv_data_t *>(mem_heap_alloc(cur_heap->heap, sizeof(*recv_data) + len));
     recv_data=static_cast<recv_data_t *>(ut_malloc_nokey( sizeof(struct recv_data_t) + len));

     *prev_field = recv_data;

     memcpy(recv_data + 1, body, len);

     prev_field = &recv_data->next;

     body += len;
   }

  mysql_mutex_lock(&recv_addr->page_mutex);

  UT_LIST_ADD_LAST(recv_addr->rec_list, recv);
  if(recv_addr->state!=RECV_NOT_PROCESSED){  //Added by Sudalai for workaround.
  	//	sbuf_gen_var.logfile<<"Page ("<<space_id<<", "<<page_no<<") recovery state: "<< recv_addr->state<<", updating it to not processed state"<<endl;
  	recv_addr->state=RECV_NOT_PROCESSED;
      ++recv_sys->n_addrs;
  }

  mysql_mutex_unlock(&recv_addr->page_mutex);



  sbuf_gen_var.logfile<<"Recv added to HASH Table - Type: "<<get_mlog_string(type)<<", Page: ("<<recv_addr->space<<", "<<recv_addr->page_no<<"), LSN: "<<recv->start_lsn<<"->"<<recv->end_lsn<<", Len: "<<recv->len<<endl;

  *prev_field = nullptr;
}

/** Calculates the new value for lsn when more data is added to the log.
@param[in]	lsn		Old LSN
@param[in]	len		This many bytes of data is added, log block
                                headers not included
@return LSN after data addition */
lsn_t recv_calc_lsn_on_data_add(lsn_t lsn, uint64_t len) ;

/** Parse and store a single log record entry.
@param[in]	ptr		start of buffer
@param[in]	end_ptr		end of buffer
@return true if end of processing */
static bool recv_single_rec(byte *ptr, byte *end_ptr) {


  recv_sys_t * recv_sys= sbuf_recv_sys;
  /* The mtr did not modify multiple pages */
  lsn_t old_lsn = recv_sys->recovered_lsn;

  /* Try to parse a log record, fetching its type, space id,
  page no, and a pointer to the body of the log record */

  byte *body;
  mlog_id_t type;
  page_no_t page_no;
  space_id_t space_id;

  ulint len =
      recv_parse_log_rec(&type, ptr, end_ptr, &space_id, &page_no, &body,true);

  if (recv_sys->found_corrupt_log) {

   // recv_report_corrupt_log(ptr, type, space_id, page_no);

#ifdef UNIV_HOTBACKUP
    return (true);
#endif /* UNIV_HOTBACKUP */

  } else if (len == 0 || recv_sys->found_corrupt_fs) {
    return (true);
  }

  lsn_t new_recovered_lsn;

  new_recovered_lsn = recv_calc_lsn_on_data_add(old_lsn, len);

  if (new_recovered_lsn > recv_sys->scanned_lsn) {
    /* The log record filled a log block, and we
    require that also the next log block should
    have been scanned in */

    return (true);
  }

  recv_previous_parsed_rec_type = type;
  recv_previous_parsed_rec_is_multi = 0;
  recv_previous_parsed_rec_offset = recv_sys->recovered_offset;

  recv_sys->recovered_offset += len;
  recv_sys->recovered_lsn = new_recovered_lsn;

  recv_track_changes_of_recovered_lsn();

  if (recv_update_bytes_to_ignore_before_checkpoint(len)) {
    return (false);
  }

  switch (type) {
    case MLOG_DUMMY_RECORD:
    case MLOG_SAS_DDL:
      /* Do nothing */
      break;

#ifdef UNIV_LOG_LSN_DEBUG
    case MLOG_LSN:
      /* Do not add these records to the hash table.
      The page number and space id fields are misused
      for something else. */
      break;
#endif /* UNIV_LOG_LSN_DEBUG */

    default:

    	//Removed tablespace missing & deleted case ...
      // sbuf_gen_var.logfile<<"Adding to HASH Table - type: "<<get_mlog_string(type)<<", for page: ("<<space_id<<","<<page_no<<")"<<endl;
          recv_add_to_hash_table(type, space_id, page_no, body, ptr + len,
                                 old_lsn, recv_sys->recovered_lsn);


      /* fall through */

    case MLOG_INDEX_LOAD:
    case MLOG_FILE_DELETE:
    case MLOG_FILE_RENAME:
    case MLOG_FILE_CREATE:
    case MLOG_TABLE_DYNAMIC_META:

      /* These were already handled by
      recv_parse_log_rec() and
      recv_parse_or_apply_log_rec_body(). */

      DBUG_PRINT("ib_log",
                 ("scan " LSN_PF ": log rec %s"
                  " len " ULINTPF " " PAGE_ID_PF,
                  old_lsn, get_mlog_string(type), len, space_id, page_no));
      break;
  }

  return (false);
}
static bool recv_report_corrupt_log(const byte *ptr, int type, space_id_t space,
                                    page_no_t page_no) {
  ib::error(ER_IB_MSG_694);
  return true;
}




/** Parse and store a multiple record log entry.
@param[in]	ptr		start of buffer
@param[in]	end_ptr		end of buffer
@return true if end of processing */
static bool recv_multi_rec(byte *ptr, byte *end_ptr) {
  /* Check that all the records associated with the single mtr
  are included within the buffer */

  ulint n_recs = 0;
  ulint total_len = 0;
  recv_sys_t * recv_sys=sbuf_recv_sys;

  for (;;) {
    mlog_id_t type;
    byte *body;
    page_no_t page_no;
    space_id_t space_id;

    ulint len =
        recv_parse_log_rec(&type, ptr, end_ptr, &space_id, &page_no, &body,false);

    if (recv_sys->found_corrupt_log) {
      recv_report_corrupt_log(ptr, type, space_id, page_no);

      return (true);

    } else if (len == 0) {
      return (true);

    } else if ((*ptr & MLOG_SINGLE_REC_FLAG)) {
      recv_sys->found_corrupt_log = true;

      recv_report_corrupt_log(ptr, type, space_id, page_no);

      return (true);

    } else if (recv_sys->found_corrupt_fs) {
      return (true);
    }

    recv_previous_parsed_rec_type = type;

    recv_previous_parsed_rec_offset = recv_sys->recovered_offset + total_len;

    recv_previous_parsed_rec_is_multi = 1;

    total_len += len;
    ++n_recs;

    ptr += len;

    if (type == MLOG_MULTI_REC_END) {
      DBUG_PRINT("ib_log", ("scan " LSN_PF ": multi-log end total_len " ULINTPF
                            " n=" ULINTPF,
                            recv_sys->recovered_lsn, total_len, n_recs));

      break;
    }

    DBUG_PRINT("ib_log",
               ("scan " LSN_PF ": multi-log rec %s len " ULINTPF " " PAGE_ID_PF,
                recv_sys->recovered_lsn, get_mlog_string(type), len, space_id,
                page_no));
  }

  lsn_t new_recovered_lsn =
      recv_calc_lsn_on_data_add(recv_sys->recovered_lsn, total_len);

  if (new_recovered_lsn > recv_sys->scanned_lsn) {
    /* The log record filled a log block, and we require
    that also the next log block should have been scanned in */

    return (true);
  }

  /* Add all the records to the hash table */

  ptr = recv_sys->buf + recv_sys->recovered_offset;

  for (;;) {
    lsn_t old_lsn = recv_sys->recovered_lsn;

    /* This will apply MLOG_FILE_ records. */

    mlog_id_t type;
    byte *body;
    page_no_t page_no;
    space_id_t space_id;

    ulint len =
        recv_parse_log_rec(&type, ptr, end_ptr, &space_id, &page_no, &body,true);


    if (recv_sys->found_corrupt_log &&
        !recv_report_corrupt_log(ptr, type, space_id, page_no)) {
      return (true);

    } else if (recv_sys->found_corrupt_fs) {
      return (true);
    }

    ut_a(len != 0);
    ut_a(!(*ptr & MLOG_SINGLE_REC_FLAG));

    recv_sys->recovered_offset += len;

    recv_sys->recovered_lsn = recv_calc_lsn_on_data_add(old_lsn, len);

    const bool apply = !recv_update_bytes_to_ignore_before_checkpoint(len);

    switch (type) {
      case MLOG_MULTI_REC_END:
        recv_track_changes_of_recovered_lsn();
        /* Found the end mark for the records */
        return (false);

#ifdef UNIV_LOG_LSN_DEBUG
      case MLOG_LSN:
        /* Do not add these records to the hash table.
        The page number and space id fields are misused
        for something else. */
        break;
#endif /* UNIV_LOG_LSN_DEBUG */
      case MLOG_SAS_DDL:
    	  break;
      case MLOG_FILE_DELETE:
      case MLOG_FILE_CREATE:
      case MLOG_FILE_RENAME:
      case MLOG_TABLE_DYNAMIC_META:
        /* case MLOG_TRUNCATE: Disabled for WL6378 */
        /* These were already handled by
        recv_parse_or_apply_log_rec_body(). */
        break;

      default:

        if (!apply) {
          break;
        }

     //  sbuf_gen_var.logfile<<"Multi-rec mtr add to HASH table - type: "<<get_mlog_string(type)<<", page: ("<<space_id<<","<<page_no<<")"<<endl;
        recv_add_to_hash_table(type, space_id, page_no, body, ptr + len,
                                   old_lsn, new_recovered_lsn);

    }

    ptr += len;
  }

  return (false);
}

static bool recv_sys_add_to_parsing_buf(const byte *log_block,
                                        lsn_t scanned_lsn) {

  recv_sys_t * recv_sys=sbuf_recv_sys;
  ut_ad(scanned_lsn >= recv_sys->scanned_lsn);

  if (!recv_sys->parse_start_lsn) {
    /* Cannot start parsing yet because no start point for
    it found */

    return (false);
  }

  ulint more_len;
  ulint data_len = log_block_get_data_len(log_block);

  if (recv_sys->parse_start_lsn >= scanned_lsn) {
    return (false);

  } else if (recv_sys->scanned_lsn >= scanned_lsn) {
    return (false);

  } else if (recv_sys->parse_start_lsn > recv_sys->scanned_lsn) {
    more_len = (ulint)(scanned_lsn - recv_sys->parse_start_lsn);

  } else {
    more_len = (ulint)(scanned_lsn - recv_sys->scanned_lsn);
  }

  if (more_len == 0) {
    return (false);
  }

  ut_ad(data_len >= more_len);

  ulint start_offset = data_len - more_len;

  if (start_offset < LOG_BLOCK_HDR_SIZE) {
    start_offset = LOG_BLOCK_HDR_SIZE;
  }

  ulint end_offset = data_len;

  if (end_offset > OS_FILE_LOG_BLOCK_SIZE - LOG_BLOCK_TRL_SIZE) {
    end_offset = OS_FILE_LOG_BLOCK_SIZE - LOG_BLOCK_TRL_SIZE;
  }

  ut_ad(start_offset <= end_offset);

  if (start_offset < end_offset) {
    memcpy(recv_sys->buf + recv_sys->len, log_block + start_offset,
           end_offset - start_offset);

    recv_sys->len += end_offset - start_offset;

    ut_a(recv_sys->len <= recv_sys->buf_len);
  }

  //sbuf_gen_var.logfile <<"Data ("<<start_offset<<","<<end_offset<<") added to parsing buffer"<<endl;
  //sbuf_gen_var.logfile<<"Recovery buffer len: "<<recv_sys->len<<endl;

  return (true);
}
bool
log_block_checksum_is_ok(const byte *block) {
return (!srv_log_checksums ||
      log_block_get_checksum(block) == log_block_calc_checksum(block));
}

static void recv_parse_log_recs(lsn_t checkpoint_lsn) {

  recv_sys_t * recv_sys=sbuf_recv_sys;
  ut_ad(recv_sys->parse_start_lsn != 0);

  for (;;) {
    byte *ptr = recv_sys->buf + recv_sys->recovered_offset;

    byte *end_ptr = recv_sys->buf + recv_sys->len;

    if (ptr == end_ptr) {
      return;
    }

    bool single_rec;

    switch (*ptr) {

#ifdef UNIV_LOG_LSN_DEBUG
      case MLOG_LSN:
#endif /* UNIV_LOG_LSN_DEBUG */
      case MLOG_DUMMY_RECORD:
        single_rec = true;
        break;
      default:
        single_rec = !!(*ptr & MLOG_SINGLE_REC_FLAG);

    }

 //  sbuf_gen_var.logfile<<"Is single rec: "<<single_rec<<endl;
 //  sbuf_gen_var.logfile<<"recovered_offset : "<<recv_sys->recovered_offset<<", LSN : "<<recv_sys->recovered_lsn<<endl;

    if (single_rec) {
      if (recv_single_rec(ptr, end_ptr)) {
        return;
      }

    } else if (recv_multi_rec(ptr, end_ptr)) {
      return;
    }

    sbuf_consistent_lsn=recv_sys->recovered_lsn;

  }
}

/** Get the number of bytes used by all the heaps
@return number of bytes used */
/*
static size_t recv_heap_used()
{
  size_t size = 0;
  recv_sys_t * recv_sys=sbuf_rev_sys;
  for (auto &space : *recv_sys->spaces) {
    if (space.second.m_heap != nullptr) {
      size += mem_heap_get_size(space.second.m_heap);
    }
  }

  return (size);
}
*/


bool  recv_scan_log_recs(log_t &log,
                               ulint max_memory, const byte *buf, ulint len,
                               lsn_t checkpoint_lsn, lsn_t start_lsn,
                               lsn_t *contiguous_lsn, lsn_t *read_upto_lsn) {

  const byte *log_block = buf;
  lsn_t scanned_lsn = start_lsn;
  bool finished = false;
  bool more_data = false;

  recv_sys_t * recv_sys=sbuf_recv_sys;

  ut_ad(start_lsn % OS_FILE_LOG_BLOCK_SIZE == 0);
  ut_ad(len % OS_FILE_LOG_BLOCK_SIZE == 0);
  ut_ad(len >= OS_FILE_LOG_BLOCK_SIZE);

  sbuf_gen_var.logfile<<"== Redo log scan start from LSN : "<<start_lsn<<endl;
  do {
    ut_ad(!finished);



    ulint no = log_block_get_hdr_no(log_block);

    ulint expected_no = log_block_convert_lsn_to_no(scanned_lsn);

   //sbuf_gen_var.logfile<<"Block LSN: "<<scanned_lsn<<" Header no:"<<no<<", expected : "<<expected_no<<endl;


    if (no != expected_no) {
      /* Garbage or an incompletely written log block.

      We will not report any error, because this can
      happen when InnoDB was killed while it was
      writing redo log. We simply treat this as an
      abrupt end of the redo log. */

      finished = true;
      sbuf_gen_var.logfile<<"Log block corruption - invalid header no : (actual, expected) = ("<<no<<", "<<expected_no<<")"<<endl;

      break;
    }

    if (!log_block_checksum_is_ok(log_block)) {
      uint32_t checksum1 = log_block_get_checksum(log_block);
      uint32_t checksum2 = log_block_calc_checksum(log_block);
      ib::error(ER_IB_MSG_720, ulonglong{no}, ulonglong{scanned_lsn},
                ulong{checksum1}, ulong{checksum2});

      /* Garbage or an incompletely written log block.

      This could be the result of killing the server
      while it was writing this log block. We treat
      this as an abrupt end of the redo log. */

      finished = true;

      sbuf_gen_var.logfile<<"Log block checksum: "<<checksum1<<", calculated checksum: "<<checksum2<<endl;
      sbuf_gen_var.logfile<<"Log block corruption - invalid check sum"<<endl;



      break;
    }

    if (log_block_get_flush_bit(log_block)) {
      /* This block was a start of a log flush operation:
      we know that the previous flush operation must have
      been completed before this block can have been flushed.
      Therefore, we know that log data is contiguous up to
      scanned_lsn. */

      if (scanned_lsn > *contiguous_lsn) {
        *contiguous_lsn = scanned_lsn;
      }
    }

    ulint data_len = log_block_get_data_len(log_block);

    uint32_t block_checkpoint_no=log_block_get_checkpoint_no(log_block) ;
  // sbuf_gen_var.logfile<<"Block checkpoint No: "<<block_checkpoint_no<<", checkpoint_lsn: "<<recv_sys->checkpoint_lsn<<endl;



    if (scanned_lsn + data_len > recv_sys->scanned_lsn &&
        block_checkpoint_no <
            recv_sys->scanned_checkpoint_no &&
        (recv_sys->scanned_checkpoint_no -
             log_block_get_checkpoint_no(log_block) >
         0x80000000UL)) {
      /* Garbage from a log buffer flush which was made
      before the most recent database recovery */
      sbuf_gen_var.logfile<<"Log block corruption - unknown case 3"<<endl;

      finished = true;

      break;
    }


    sbuf_gen_var.logfile<<"Data Len : "<<data_len<<", First rec group : "<<log_block_get_first_rec_group(log_block)<<endl;
	redo_checkpoint_no=block_checkpoint_no;

    if(recv_sys->scanned_checkpoint_no!=block_checkpoint_no){
    	sbuf_gen_var.logfile<<"Checkpoint switch: "<<recv_sys->checkpoint_lsn<<", recovered_lsn: "<<recv_sys->recovered_lsn<<", No: "<<redo_checkpoint_no<<std::endl;
    	recv_sys->checkpoint_lsn=recv_sys->recovered_lsn;
    }



    if (!recv_sys->parse_start_lsn &&
        log_block_get_first_rec_group(log_block) > 0) {
      /* We found a point from which to start the parsing
      of log records */

      recv_sys->parse_start_lsn =
          scanned_lsn + log_block_get_first_rec_group(log_block);

    //  ib::info(ER_IB_MSG_1261)
      //    << "Starting to parse redo log at lsn = " << recv_sys->parse_start_lsn
        //  << ", whereas checkpoint_lsn = " << recv_sys->checkpoint_lsn;

     sbuf_gen_var.logfile << "Starting to parse redo log at lsn = " << recv_sys->parse_start_lsn
              << ", whereas checkpoint_lsn = " << recv_sys->checkpoint_lsn<<endl;

      if (recv_sys->parse_start_lsn < recv_sys->checkpoint_lsn) {
        /* We start to parse log records even before
        checkpoint_lsn, from the beginning of the log
        block which contains the checkpoint_lsn.

        That's because the first group of log records
        in the log block, starts before checkpoint_lsn,
        and checkpoint_lsn could potentially point to
        the middle of some log record. We need to find
        the first group of log records that starts at
        or after checkpoint_lsn. This could be only
        achieved by traversing all groups of log records
        that start within the log block since the first
        one (to discover their beginnings we need to
        parse them). However, we don't want to report
        missing tablespaces for space_id in log records
        before checkpoint_lsn. Hence we need to ignore
        those records and that's why we need a counter
        of bytes to ignore. */

        recv_sys->bytes_to_ignore_before_checkpoint =
            recv_sys->checkpoint_lsn - recv_sys->parse_start_lsn;
       sbuf_gen_var.logfile<<"Bytes to ignore: "+recv_sys->bytes_to_ignore_before_checkpoint<<endl;

        ut_a(recv_sys->bytes_to_ignore_before_checkpoint <=
             OS_FILE_LOG_BLOCK_SIZE - LOG_BLOCK_HDR_SIZE);

        ut_a(recv_sys->checkpoint_lsn % OS_FILE_LOG_BLOCK_SIZE +
                 LOG_BLOCK_TRL_SIZE <
             OS_FILE_LOG_BLOCK_SIZE);

        ut_a(recv_sys->parse_start_lsn % OS_FILE_LOG_BLOCK_SIZE >=
             LOG_BLOCK_HDR_SIZE);
      }

      recv_sys->scanned_lsn = recv_sys->parse_start_lsn;
      recv_sys->recovered_lsn = recv_sys->parse_start_lsn;

      recv_track_changes_of_recovered_lsn();
    }

    scanned_lsn += data_len;

    if (scanned_lsn > recv_sys->scanned_lsn) {
      /* We were able to find more log data: add it to the
      parsing buffer if parse_start_lsn is already
      non-zero */

      if (recv_sys->len + 4 * OS_FILE_LOG_BLOCK_SIZE >= recv_sys->buf_len) {
        if (!recv_sys_resize_buf()) {
          recv_sys->found_corrupt_log = true;
          scanned_lsn-=data_len;   //Reverting...
         sbuf_gen_var.logfile<<"!!!!!---------Recovery buffer overflow------- !!!!! "<<endl;
        }
      }

      if (!recv_sys->found_corrupt_log) {
        more_data = recv_sys_add_to_parsing_buf(log_block, scanned_lsn);
      }else{
    	 sbuf_gen_var.logfile << "Corrupted log block @ " << scanned_lsn<<endl;
    	  break;
      }

      recv_sys->scanned_lsn = scanned_lsn;

      recv_sys->scanned_checkpoint_no = log_block_get_checkpoint_no(log_block);
    }

    if (data_len < OS_FILE_LOG_BLOCK_SIZE) {
      /* Log data for this group ends here */
      finished = true;

      break;

    } else {
      log_block += OS_FILE_LOG_BLOCK_SIZE;
    }

  } while (log_block < buf + len);

  *read_upto_lsn = scanned_lsn;
  ++recv_scan_print_counter;

  if (more_data && !recv_sys->found_corrupt_log) {
	  recv_parse_log_recs(checkpoint_lsn);

      aur_recv_apply_hashed_log_recs(log, false);

    if (recv_sys->recovered_offset > recv_sys->buf_len / 4) {
      recv_reset_buffer();
    }
  }

  return (finished);
}


static void sbuf_refresh_begin(log_t &log, lsn_t *contiguous_lsn){
	  recv_sys_t * recv_sys=sbuf_recv_sys;
	  recv_sys->len = 0;
	   recv_sys->recovered_offset = 0;
	   recv_sys->n_addrs = 0;

	   mutex_enter(&recv_sys->mutex);
	   recv_sys_empty_hash();

	   /* Since 8.0, we can start recovery at checkpoint_lsn which points
	   to the middle of log record. In such case we first to need to find
	   the beginning of the first group of log records, which is at lsn
	   greater than the checkpoint_lsn. */
	   recv_sys->parse_start_lsn = 0;

	   /* This is updated when we find value for parse_start_lsn. */
	   recv_sys->bytes_to_ignore_before_checkpoint = 0;

	   recv_sys->checkpoint_lsn = *contiguous_lsn;
	   recv_sys->scanned_lsn = *contiguous_lsn;
	   recv_sys->recovered_lsn = *contiguous_lsn;

	   /* We have to trust that the first_rec_group in the first block is
	   correct as we can't start parsing earlier to check it ourselves. */
	   recv_sys->previous_recovered_lsn = *contiguous_lsn;
	   recv_sys->last_block_first_rec_group = 0;

	   recv_sys->scanned_checkpoint_no = 0;
	   recv_previous_parsed_rec_type = MLOG_SINGLE_REC_FLAG;
	   recv_previous_parsed_rec_offset = 0;
	   recv_previous_parsed_rec_is_multi = 0;
	   ut_ad(recv_max_page_lsn == 0);

	   mutex_exit(&recv_sys->mutex);

	   ulint max_mem =
	       UNIV_PAGE_SIZE * (buf_pool_get_n_pages() -
	                         (recv_n_pool_free_frames * srv_buf_pool_instances));

	   *contiguous_lsn =
	       ut_uint64_align_down(*contiguous_lsn, OS_FILE_LOG_BLOCK_SIZE);

	   lsn_t start_lsn = *contiguous_lsn;

	   lsn_t checkpoint_lsn = start_lsn;

	   sbuf_gen_var.logfile<<"Checkpoint lsn : "<<recv_sys->checkpoint_lsn<<endl;

	   bool finished = false;

	   aur_recovery_on=true;

	   while (!finished) {

	     sbuf_gen_var.logfile<<"---------------------------------------"<<endl;

	     start_lsn=ut_uint64_align_down(start_lsn, OS_FILE_LOG_BLOCK_SIZE);
	     lsn_t end_lsn = start_lsn + RECV_SCAN_SIZE;

	     //sbuf_gen_var.logfile<<"Start scan from lsn: "<<start_lsn<<endl;

	     recv_read_log_seg(log, log.buf, start_lsn, end_lsn);

	     finished = recv_scan_log_recs(log, max_mem, log.buf, RECV_SCAN_SIZE,
	                                   checkpoint_lsn, start_lsn, contiguous_lsn,
	                                   &log.scanned_lsn);


	     sbuf_gen_var.logfile<<"Finished: "<<finished<<", is corrupted: "<<recv_sys->found_corrupt_log<<", corrupted fs: "<<recv_sys->found_corrupt_fs<<endl;
	     sbuf_gen_var.logfile<<"Expected endlsn "<<end_lsn<<" but scanned upto lsn: "<<recv_sys->scanned_lsn<<", Recovered lsn: "<<recv_sys->recovered_lsn<<endl;

	     start_lsn =  recv_sys->scanned_lsn;
	     if(finished || recv_sys->found_corrupt_log || recv_sys->found_corrupt_fs ){
	    	 finished=false;
	    	 recv_sys->found_corrupt_fs=false;
	    	 recv_sys->found_corrupt_log=false;
	    	// sbuf_gen_var.logfile<<"Sleeping 3 sec "<<endl;
	    	 sleep(1);
	     }
	   }

	   DBUG_PRINT("ib_log", ("scan " LSN_PF " completed", log.scanned_lsn));
}

MY_ATTRIBUTE((warn_unused_result))
static bool  acquire_exclusive_table_lock(const char * schema, const char * tablename, THD * thd, 	MDL_request_list * mdl_requests){

    MDL_request *schema_request = new (thd->mem_root) MDL_request;
    MDL_REQUEST_INIT(schema_request, MDL_key::SCHEMA, schema, "",
                     MDL_INTENTION_EXCLUSIVE, MDL_EXPLICIT);
    mdl_requests->push_front(schema_request);

    MDL_request *table_request = new (thd->mem_root) MDL_request;

    MDL_REQUEST_INIT(table_request, MDL_key::TABLE, schema, tablename,
    		MDL_EXCLUSIVE, MDL_EXPLICIT);
    mdl_requests->push_front(table_request);

    return thd->mdl_context.acquire_locks(mdl_requests, 60);

}

static void * sbuf_tmr_thd(void * args){

	  sbuf_struct_gen_var_t *drop;
	  ulint n_tables;
	  char schema_name[100];
	  const char * table_name_ptr;
	//  ulint n_tables_dropped = 0;
	  THD * thd= (THD * )args;

	  std::ofstream errfile;
	  errfile.open("/home/sas/mysql8/ref_meta.log", ios::out|ios::app);

loop:
	  mysql_mutex_lock(&sbuf_tmr_mutex);

	  drop = UT_LIST_GET_FIRST(sbuf_tmr_table_list);

	  n_tables = UT_LIST_GET_LEN(sbuf_tmr_table_list);
	  errfile<<"No. of tables to drop: "<<n_tables<<std::endl;


	  mysql_mutex_unlock(&sbuf_tmr_mutex);

	  if(drop == NULL){
		  os_thread_sleep(5000000);
		  errfile<<"Sleeping "<<std::endl;
		  goto loop;
	  }

	  errfile<<"Going to drop: "<<drop<<std::endl;
	  {
		  current_thd=thd;
		  int db_len=dict_get_db_name_len(drop->table_name) ;

		  strncpy(schema_name, drop->table_name,db_len);

		  table_name_ptr=dict_remove_db_name(drop->table_name);

		  MDL_request_list  mdl_requests;

		  if( acquire_exclusive_table_lock(schema_name, table_name_ptr, thd, &mdl_requests)){
			 errfile<<"Lock acqurition failed"<<std::endl;
			 goto loop;
		  }

		  TABLE_LIST * tlist=new TABLE_LIST(schema_name, db_len, table_name_ptr, strlen(table_name_ptr),nullptr, TL_WRITE);

		  close_cached_tables(thd, tlist,true, 300);

		  mutex_enter(&dict_sys->mutex);
		  dict_table_t * dtable=dict_table_check_if_in_cache_low(drop->table_name);
		  if(dtable != NULL){
			  fprintf(stderr,"\nTable dropped: %s, refcount: %lu\n", drop->table_name,dtable->get_ref_count() );
			  sbuf_gen_var.logfile<<"Drop table: "<< dtable->name<<" - refcount="<<dtable->get_ref_count()<<" - Discard_after_ddl: "<<dtable->discard_after_ddl<<std::endl;
			  if(dtable->get_ref_count()==0){
				sbuf_gen_var.logfile<<"Drop table: "<< dtable->name<<" - cache removed "<<std::endl;
				dict_table_remove_from_cache(dtable);
			  }
		  }
		  mutex_exit(&dict_sys->mutex);

		  {
			  if(thd->dd_client()->invalidate(schema_name, table_name_ptr)){
				  errfile<<"Dictionary table remove failed"<<std::endl;
			  }
		  }


		  while(!mdl_requests.is_empty()){
			  MDL_request * request=mdl_requests.front();
			  thd->mdl_context.release_lock(request->ticket);
			  mdl_requests.remove(request);
			  //free(request); //Freeing memory.
		  }
		  delete (tlist);

	  }

	  mysql_mutex_lock(&sbuf_tmr_mutex);
	  UT_LIST_REMOVE(sbuf_tmr_table_list, drop);
	  mysql_mutex_unlock(&sbuf_tmr_mutex);


	  goto loop;

	  return NULL;

}


MY_ATTRIBUTE((warn_unused_result))
dberr_t print_dict_table(const char * table){

     	mutex_enter(&dict_sys->mutex);
     	dict_table_t * dtable=dict_table_check_if_in_cache_low(table);

	if(dtable != NULL){
		sbuf_gen_var.logfile<<"DD table: "<< dtable->name<<" - refcount="<<dtable->get_ref_count()<<std::endl;
	}else{
		sbuf_gen_var.logfile<<"DD table ("<<table<<") not present"<<std::endl;
	}
     	mutex_exit(&dict_sys->mutex);

        mysql_mutex_lock(&LOCK_open);

        char a[50];
        char * dtable_ch=a;
        strncpy(dtable_ch, table, dict_get_db_name_len(table));

        TABLE_SHARE * share=get_cached_table_share( dtable_ch,dict_remove_db_name(table));

        sbuf_gen_var.logfile<<"Table definition_cache entry: "<<share<<std::endl;

        if(share){

        	sbuf_gen_var.logfile<<"Table name: "<<share->table_name.str<<" - ref_count: "<<share->ref_count()<<std::endl;

        }
        mysql_mutex_unlock(&LOCK_open);


     	return (DB_SUCCESS);
}



MY_ATTRIBUTE((warn_unused_result))
dberr_t remove_dict_table(const char * table ){


 	mutex_enter(&dict_sys->mutex);
 	dict_table_t * dtable=dict_table_check_if_in_cache_low(table);

 	sys_gen_var.logfile.errfile<<"Table to remove: "<<dtable<<std::endl;
 	int ref_count=-1;
 	if(dtable && (ref_count=dtable->get_ref_count())==0){
 		dict_table_remove_from_cache(dtable);
 	}
 	mutex_exit(&dict_sys->mutex);

	return (DB_SUCCESS);
}

static THD* make_mysql_thread() {
  THD *new_thd = NULL;
  my_thread_handle th;
  if (!(new_thd = new THD)) {
    return NULL;
  }
  new_thd->security_context()->set_master_access(0);
  new_thd->security_context()->cache_current_db_access(0);
 // new_thd->security_context()->set_host_or_ip_ptr((char *)my_localhost,
//                                              strlen(my_localhost));
  new_thd->get_protocol_classic()->init_net(NULL);
  new_thd->security_context()->set_user_ptr(C_STRING_WITH_LEN("event_scheduler"));
  new_thd->get_protocol_classic()->get_net()->read_timeout = 100000;
  new_thd->slave_thread = 0;
  new_thd->variables.option_bits |= OPTION_AUTO_IS_NULL;
  new_thd->get_protocol_classic()->set_client_capabilities(CLIENT_MULTI_RESULTS);

  new_thd->set_new_thread_id();
  current_thd=new_thd;
  /*
    Guarantees that we will see the thread in SHOW PROCESSLIST though its
    vio is NULL.
  */
  //new_thd->thread_stack =reinterpret_cast<char *>(&new_thd);
  new_thd->proc_info = "Initialized";
  new_thd->set_time();

  /* Do not use user-supplied timeout value for system threads. */
  new_thd->variables.lock_wait_timeout = LONG_TIMEOUT;
  new_thd->set_command(COM_DAEMON);

  return new_thd;
}


MY_ATTRIBUTE((warn_unused_result))
dberr_t sub_create_tmr_thd(){

    THD *thd = make_mysql_thread();

	my_thread_attr_t thr_attr;
	my_thread_attr_init(&thr_attr);
	my_thread_attr_setdetachstate(&thr_attr, MY_THREAD_CREATE_JOINABLE);
	my_thread_handle thread_handle;

	mysql_mutex_init(PSI_NOT_INSTRUMENTED, &sbuf_tmr_mutex, MY_MUTEX_INIT_FAST);
	UT_LIST_INIT(sbuf_tmr_table_list, &sbuf_struct_tmr_table_node_t::tnode);

	if (my_thread_create(&thread_handle, &thr_attr, sbuf_tmr_thd,
					   (void *)thd) != 0) {
	// fprintf(stderr, "Could not create heartbeat thread!\n");

		exit(0);
	}


	return (DB_SUCCESS);
}

static void *  sbuf_chkpt_notifier(void * nullptr1) {

	DBUG_PRINT("sbuf_chkpt_notifier starts",("Checkpoint notifier"));

	  dberr_t err;
	  ulint max_cp_field;

	  log_t &log= *  (log_t *)nullptr1; //sbuf_rev_sys->log;

	  err = recv_find_max_checkpoint(log, &max_cp_field);


	  if (err != DB_SUCCESS) {
	    return NULL;
	  }

	  using namespace std;
	  std::ofstream &errfile=sys_gen_var.logfile;
	  errfile.open("/home/sas/mysql8/aur.log", ios::out|ios::app);
	 // sys_gen_var.dd_client= new dd::cache::Dictionary_client((THD *)malloc(sizeof(THD)));

	  //sys_gen_var.m_heap=mem_heap_create_typed(256, MEM_HEAP_FOR_RECV_SYS);


	  using UndoHdr = sbuf_struct_gen_var_t::UndoHdr;

	  sys_gen_var.m_undohdr = UT_NEW(UndoHdr(), mem_log_recv_space_hash_key);


	  log_files_header_read(log, static_cast<uint32_t>(max_cp_field));

	  lsn_t checkpoint_lsn;
	  checkpoint_no_t checkpoint_no;

	  checkpoint_lsn = mach_read_from_8(log.checkpoint_buf + LOG_CHECKPOINT_LSN);

	  checkpoint_no = mach_read_from_8(log.checkpoint_buf + LOG_CHECKPOINT_NO);

	  DBUG_PRINT("Checkpoint",("(%lu,%lu)",checkpoint_lsn,checkpoint_no));

	  DBUG_PRINT("iblog",("Checkpoint lsn " LSN_PF " checkpoint no: %lu",checkpoint_lsn, checkpoint_no));

      errfile<<"Checkpoint (lsn,no) "<<checkpoint_lsn<<", "<<checkpoint_no<<endl;

	  sleep(10);

	  if(start_meta_dropper_thread()!= DB_SUCCESS){
		  errfile<<"Dumper thread startup Failed ";

	  }


	 // checkpoint_lsn=20386304;

	  lsn_t start_lsn=ut_uint64_align_down(checkpoint_lsn, OS_FILE_LOG_BLOCK_SIZE);

	  sbuf_init_setup();

	  srv_force_recovery=0;  // Setting srv_force_recovery to 0 to allow proper trx handling.

	  recv_begin(log, &start_lsn);

	  errfile.close();

	  return NULL;
}




/** Start recovering from a redo log checkpoint.
@see recv_recovery_from_checkpoint_finish
@param[in,out]	log		redo log
@param[in]	flush_lsn	FIL_PAGE_FILE_FLUSH_LSN
                                of first system tablespace page
@return error code or DB_SUCCESS */
MY_ATTRIBUTE((warn_unused_result))
dberr_t sbuf_start_bufpool_refresher(log_t &log, lsn_t flush_lsn) {


	  ut_ad(srv_read_only_mode);
	  ut_ad(srv_force_recovery == SRV_FORCE_NO_LOG_REDO);


	  DBUG_PRINT("BufPool refresher started @ ", ("Flush LSN: %lu", flush_lsn)); //Sudalai

	  sbuf_init_setup();

	  my_thread_attr_t attr; /* Thread attributes */
	  my_thread_attr_init(&attr);
	  my_thread_attr_setdetachstate(&attr, MY_THREAD_CREATE_JOINABLE);

	  my_thread_handle * handle=&sys_gen_var.ckpt_notifyer;
	  if (my_thread_create(handle, &attr, aur_chkpt_notifier,
	                       (void *)&log) != 0) {
	   // fprintf(stderr, "Could not create heartbeat thread!\n");

	    exit(0);
	  }

	  // Creating thd to take care of dictionary cache drop when alter/drop happended for a table.




//	  pthread_t tid;
//	  pthread_create(&tid, NULL, aur_chkpt_notifier , (void*) &log);

	  //sys_gen_var.ckpt_notifyer=&tid;
/*
	  pthread redo_reader;
	  pthread_create(&redo_reader, NULL, aur_redo_reader, (void*) &log);
*/
	  return (DB_SUCCESS);

}
/* ******************* END **********************/






