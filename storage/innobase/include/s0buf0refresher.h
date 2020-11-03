/*
 * Purpose: refresh buffer pool pages by applying latest XLOG content.
 */
#ifndef STORAGE_INNOBASE_INCLUDE_S0BUF0REFRESHER_H_
#define STORAGE_INNOBASE_INCLUDE_S0BUF0REFRESHER_H_

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

#include <list>
#include <set>
#include <unordered_map>
#include <pthread.h>
#include <fstream>


class sbuf_struct_gen_var_t{

        public:

		sbuf_struct_com_var_t(){
        }

        my_thread_handle redo_reader;
        my_thread_handle  ckpt_notifyer;

        dd::cache::Dictionary_client * dd_client;

        std::ofstream logfile;

    using UndoHdr = std::unordered_map<ulint, trx_id_t, std::hash<ulint>, std::equal_to<ulint>>;

    UndoHdr * m_undohdr;
    mem_heap_t *m_heap;

    std::vector<space_id_t> m_undo_space;

};



MY_ATTRIBUTE((warn_unused_result))
dberr_t sbuf_start_bufpool_refresher(log_t &log, lsn_t flush_lsn);

void sbuf_recv_recover_page( bool just_read_in,  buf_block_t *block) ;

#endif /* STORAGE_INNOBASE_INCLUDE_S0BUF0REFRESHER_H_ */



