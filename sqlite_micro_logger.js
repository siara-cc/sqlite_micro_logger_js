// Constants
const LEN_OF_REC_LEN = 3;
const LEN_OF_HDR_LEN = 2;
const CHKSUM_LEN = 3;

// Datatypes
DBLOG_TYPE_INT = 1;
DBLOG_TYPE_REAL = 2;
DBLOG_TYPE_BLOB = 3;
DBLOG_TYPE_TEXT = 4;

// Error codes
DBLOG_RES_OK = 0;
DBLOG_RES_ERR = -1;
DBLOG_RES_INV_PAGE_SZ = -2;
DBLOG_RES_TOO_LONG = -3;
DBLOG_RES_WRITE_ERR = -4;
DBLOG_RES_FLUSH_ERR = -5;
DBLOG_RES_SEEK_ERR = -6;
DBLOG_RES_READ_ERR = -7;
DBLOG_RES_INVALID_SIG = -8;
DBLOG_RES_MALFORMED = -9;
DBLOG_RES_NOT_FOUND = -10;
DBLOG_RES_NOT_FINALIZED = -11;
DBLOG_RES_TYPE_MISMATCH = -12;
DBLOG_RES_INV_CHKSUM = -13;

// Returns how many bytes the given integer will
// occupy if stored as a variable integer
function get_vlen(vint) {
   return vint > 268435455 ? 5 : (vint > 2097151 ? 4 
            : (vint > 16383 ? 3 : (vint > 127 ? 2 : 1)));
}

// Stores the given byte in the given location
// in big-endian sequence
function write_uint8(array, pos, input) {
  array[pos] = input;
}
 
// Stores the given uint16_t in the given location
// in big-endian sequence
function write_uint16(array, pos, input) {
  array[pos] = input >> 8;
  array[pos + 1] = input & 0xFF;
}
 
// Stores the given uint32_t in the given location
// in big-endian sequence
function write_uint32(array, pos, input) {
   array[pos++] = Math.floor(input / 0x1000000) & 0xFF;
   array[pos++] = Math.floor(input / 0x10000) & 0xFF;
   array[pos++] = Math.floor(input / 0x100) & 0xFF;
   array[pos] = input & 0xFF;
}
 
// Stores the given uint64_t in the given location
// in big-endian sequence
function write_uint64(array, pos, input) {
   array[pos++] = 0; // out of bounds for Javascript
   array[pos++] = Math.floor(input / 0x1000000000000) & 0xFF;
   array[pos++] = Math.floor(input / 0x10000000000) & 0xFF;
   array[pos++] = Math.floor(input / 0x100000000) & 0xFF;
   array[pos++] = Math.floor(input / 0x1000000) & 0xFF;
   array[pos++] = Math.floor(input / 0x10000) & 0xFF;
   array[pos++] = Math.floor(input / 0x100) & 0xFF;
   array[pos] = input & 0xFF;
}
 
// Stores the given number in the given location
// in variable integer format
function write_vint(array, pos, vint) {
   var len = get_vlen(vint);
   var divisors = new Array(0x80, 0x4000, 0x200000, 0x10000000);
   for (var i = len - 1; i > 0; i--)
     array[pos++] = 0x80 + (Math.floor(vint / divisors[i - 1]) & 0xFF);
   array[pos] = vint & 0x7F;
   return len;
}

// Reads and returns big-endian uint8_t
// at a given memory location
function read_uint8(array, pos) {
  return array[pos];
}
 
// Reads and returns big-endian uint16_t
// at a given memory location
function read_uint16(array, pos) {
  return (array[pos] << 8) + array[pos + 1];
}
 
// Reads and returns big-endian uint32_t
// at a given memory location
function read_uint32(array, pos) {
   var ret;
   ret = array[pos++] * 0x1000000;
   ret += array[pos++] * 0x10000;
   ret += array[pos++] * 0x100;
   ret += array[pos];
   return ret;
}
 
// Reads and returns big-endian uint64_t
// at a given memory location
function read_uint64(array, pos) {
   var ret;
   pos++; // ignore first byte - out of bounds for Javascript
   ret = array[pos++] * 0x1000000000000;
   ret += array[pos++] * 0x10000000000;
   ret += array[pos++] * 0x100000000;
   ret += array[pos++] * 0x1000000;
   ret += array[pos++] * 0x10000;
   ret += array[pos++] * 0x100;
   ret += array[pos];
   return ret;
}
 
// Reads and returns variable integer
// from given location as uint16_t
// Also returns the length of the varint
function read_vint(array, pos) {
   var ret = 0;
   var len = 5; // read max 5 bytes
   do {
     ret *= 0x80;
     ret += (array[pos++] & 0x7F);
     len--;
   } while ((array[pos++] & 0x80) == 0x80 && len);
   if (len)
     len = 5 - len;
   return [ret, len];
}
 
// Returns position of last record.
// Creates one, if no record found.
function acquire_last_pos = function(array, pos) {
  var last_pos = read_uint16(array, pos + 5);
  if (last_pos == 0) {
    this.append_empty_row();
    last_pos = read_uint16(array, pos + 5);
  }
  return last_pos;
}

// Attempts to locate a column using given index
// Returns position of column in header area, position of column
// in data area, record length and header length
// See https://www.sqlite.org/fileformat.html#record_format
function locate_column(array, rec_pos, col_idx, limit) {
   var hdr_pos = rec_pos;
   var vint = read_vint(array, hdr_pos);
   var rec_len = vint[0];
   hdr_pos += vint[1];
   var vint1 = read_vint(array, hdr_pos);
   hdr_pos += vint1[1];
   if (rec_len + (hdr_pos - rec_pos) > limit)
     return null; // corruption
   vint = read_vint(array, hdr_pos);
   hdr_len = vint[0];
   if (hdr_len > limit)
     return null; // corruption
   var data_pos = hdr_pos + hdr_len;
   data_start_pos = data_pos; // re-position to check for corruption below
   hdr_pos += vint[1];
   for (var i = 0; i < col_idx; i++) {
     vint = read_vint(array, hdr_pos);
     var col_type_or_len = vint[0];
     hdr_pos += vint[1];
     data_pos += dblog_derive_data_len(col_type_or_len);
     if (hdr_pos >= data_start_pos)
       return null; // corruption or column not found
     if (data_pos - rec_pos > limit)
       return null; // corruption
   }
   return [hdr_pos, data_pos, rec_len_pos, hdr_len_pos];
} 

// Returns type of column based on given value and length
// See https://www.sqlite.org/fileformat.html#record_format
function derive_col_type_or_len(type, val, len) {
   var col_type_or_len = 0;
   if (val != null) {
     switch (type) {
       case DBLOG_TYPE_INT:
         col_type_or_len = (len == 1 ? 1 : (len == 2 ? 2 : (len == 4 ? 4 : 6)));
         //if (len == 1) {
         //  int8_t *typed_val = (int8_t *) val;
         //  col_type_or_len = (*typed_val == 0 ? 8 : (*typed_val == 1 ? 9 : 0));
         //} else
         //  col_type_or_len = (len == 2 ? 2 : (len == 4 ? 4 : 6));
         break;
       case DBLOG_TYPE_REAL:
         col_type_or_len = 7;
         break;
       case DBLOG_TYPE_BLOB:
         col_type_or_len = len * 2 + 12;
         break;
       case DBLOG_TYPE_TEXT:
         col_type_or_len = len * 2 + 13;
     }
   }
   return col_type_or_len;    
 }
 
var c1, c2, c3;
function saveChecksumBytes(array, pos, last_pos) {
   pos += last_pos;
   pos--;
   c1 = array[ptr--];
   c2 = array[ptr--];
   c3 = array[ptr];
}
 
function restoreChecksumBytes(array, pos, last_pos) {
   pos += last_pos;
   pos--;
   array[pos--] = c1;
   array[pos--] = c2;
   array[ptr] = c3;
}

// Initializes the buffer as a B-Tree Leaf table
function init_bt_tbl_leaf(array, pos) {
   pos = 13; // Leaf table b-tree page
   write_uint16(array, pos + 1, 0); // No freeblocks
   write_uint16(array, pos + 3, 0); // No records yet
   write_uint16(array, pos + 5, 0); // No records yet
   write_uint8(array, ptr + 7, 0); // Fragmented free bytes
}
 
// Initializes the buffer as a B-Tree Interior table
function init_bt_tbl_inner(array, pos) {
   array[pos] = 5; // Interior table b-tree page
   write_uint16(array, pos + 1, 0); // No freeblocks
   write_uint16(array, pos + 3, 0); // No records yet
   write_uint16(array, pos + 5, 0); // No records yet
   write_uint8(array, pos + 7, 0); // Fragmented free bytes
}

// Writes Record length, Row ID and Header length
// at given location
// No corruption checking because no unreliable source
function write_rec_len_rowid_hdr_len(array, pos, rec_len, rowid, hdr_len) {
   // write record len
   array[pos++] = 0x80 + (rec_len >> 14);
   array[pos++] = 0x80 + ((rec_len >> 7) & 0x7F);
   array[pos++] = rec_len & 0x7F;
   // write row id
   pos += write_vint(array, pos, rowid);
   // write header len
   array[pos++] = 0x80 + (hdr_len >> 7);
   array[pos] = hdr_len & 0x7F;
}
 
// Checks or calculates 3 checksums:
// 1. Header checksum, which is for page header and last rowid
// 2. Checksum of first record
// 3. Checksum of entire page
// Checksum is simply a 8 bit sum of byte values, ignoring overflows
// calc_or_check == 0 means calculate all three checksums
// calc_or_check == 1 means check header checksum
// calc_or_check == 2 means check first record checksum
// calc_or_check == 3 means check page checksum
function check_sums(buf, page_size, calc_or_check) {
   if (buf[0] == 5) // no need checksum for internal pages
     return DBLOG_RES_OK;
   if (buf[0] == 13) {
     var vlen;
     var chk_sum = 0;
     var i = 0;
     var end = 8;
     while (i < end) // Header checksum
       chk_sum += buf[i++];
     var last_pos = read_uint16(buf, 5);
     i = last_pos;
     end = i + LEN_OF_REC_LEN;
     var vint = read_vint(buf, end);
     end += vint[1];
     while (i < end) // Header checksum
       chk_sum += buf[i++];
     if (calc_or_check == 0)
       buf[last_pos - 1] = chk_sum;
     else if (calc_or_check == 1) {
       if (buf[last_pos - 1] != chk_sum)
         return DBLOG_RES_INV_CHKSUM;
       return DBLOG_RES_OK;
     }
     i = end;
     vint = read_vint(buf, end - vlen - LEN_OF_REC_LEN);
     end += vint[0];
     while (i < end) // First record checksum
       chk_sum += buf[i++];
     if (calc_or_check == 0)
       buf[last_pos - 2] = chk_sum;
     else if (calc_or_check == 2) {
       if (buf[last_pos - 2] != chk_sum)
         return DBLOG_RES_INV_CHKSUM;
       return DBLOG_RES_OK;
     }
     i = end;
     end = page_size;
     while (i < end) // Page checksum
       chk_sum += buf[i++];
     i = 8;
     end = i + read_uint16(buf, 3) * 2;
     while (i < end) // Page checksum
       chk_sum += buf[i++];
     if (calc_or_check == 0)
       buf[last_pos - 3] = chk_sum;
     else {
       if (buf[last_pos - 3] != chk_sum)
         return DBLOG_RES_INV_CHKSUM;
     }
   } else { // Assume first page
     var i = 0;
     var chk_sum = 0;
     while (i < page_size)
       chk_sum += buf[i++];
     chk_sum -= buf[69];
     if (calc_or_check)
       buf[69] = chk_sum;
     else {
       if (buf[69] != chk_sum)
         return DBLOG_RES_ERR;
     }
   }
   return DBLOG_RES_OK;
}

// Adds record to B-Tree inner table
int add_rec_to_inner_tbl(struct dblog_write_context *wctx, byte *parent_buf, 
       uint32_t rowid, uint32_t cur_level_pos) {
 
   int32_t page_size = get_pagesize(wctx->page_size_exp);
   uint16_t last_pos = read_uint16(parent_buf + 5);
   int rec_count = read_uint16(parent_buf + 3) + 1;
   byte rec_len = 4 + get_vlen_of_uint32(rowid);
 
   if (last_pos == 0)
     last_pos = page_size - rec_len;
   else {
     // 3 is for checksum
     if (last_pos - rec_len < 12 + rec_count * 2 + get_vlen_of_uint32(rowid) + 3)
       last_pos = 0;
     else
       last_pos -= rec_len;
   }
 
   cur_level_pos++;
   if (last_pos && rowid) {
     write_uint32(parent_buf + last_pos, cur_level_pos);
     write_vint32(parent_buf + last_pos + 4, rowid);
     write_uint16(parent_buf + 3, rec_count--);
     write_uint16(parent_buf + 12 + rec_count * 2, last_pos);
     write_uint16(parent_buf + 5, last_pos);
   } else {
     write_uint32(parent_buf + 8, cur_level_pos);
     rec_count--;
     write_vint32(parent_buf + 12 + rec_count * 2, rowid);
     return 1;
   }
 
   // No corruption checking because no unreliable source
   return DBLOG_RES_OK;
 
 }
 
 const char sqlite_sig[] = "SQLite format 3";
 const char dblog_sig[]  = "SQLite3 uLogger";
 char default_table_name[] = "t1";
 
 // Writes data into buffer to form first page of Sqlite db
 int form_page1(struct dblog_write_context *wctx, char *table_name, char *table_script) {
 
   if (wctx->page_size_exp < 9 || wctx->page_size_exp > 16)
     return DBLOG_RES_INV_PAGE_SZ;
   byte *buf = (byte *) wctx->buf;
   int32_t page_size = get_pagesize(wctx->page_size_exp);
   wctx->cur_write_rowid = 0;
 
   // 100 byte header - refer https://www.sqlite.org/fileformat.html
   memcpy(buf, dblog_sig, 16);
   //memcpy(buf, "SQLite format 3\0", 16);
   write_uint16(buf + 16, page_size == 65536 ? 1 : (uint16_t) page_size);
   buf[18] = 1;
   buf[19] = 1;
   buf[20] = wctx->page_resv_bytes;
   buf[21] = 64;
   buf[22] = 32;
   buf[23] = 32;
   //write_uint32(buf + 24, 0);
   //write_uint32(buf + 28, 0);
   //write_uint32(buf + 32, 0);
   //write_uint32(buf + 36, 0);
   //write_uint32(buf + 40, 0);
   memset(buf + 24, '\0', 20); // Set to zero, above 5
   write_uint32(buf + 28, 2); // TODO: Update during finalize
   write_uint32(buf + 44, 4);
   //write_uint16(buf + 48, 0);
   //write_uint16(buf + 52, 0);
   memset(buf + 48, '\0', 8); // Set to zero, above 2
   write_uint32(buf + 56, 1);
   // User version initially 0, set to table leaf count
   // used to locate last leaf page for binary search
   // and move to last page.
   write_uint32(buf + 60, 0);
   write_uint32(buf + 64, 0);
   // App ID - set to 0xA5xxxxxx where A5 is signature
   // last 5 bits = wctx->max_pages_exp - set to 0 currently
   // till it is implemented
   write_uint32(buf + 68, 0xA5000000);
   memset(buf + 72, '\0', 20); // reserved space
   write_uint32(buf + 92, 105);
   write_uint32(buf + 96, 3016000);
   memset(buf + 100, '\0', page_size - 100); // Set remaing page to zero
 
   // master table b-tree
   init_bt_tbl_leaf(buf + 100);
 
   // write table script record
   int orig_col_count = wctx->col_count;
   wctx->cur_write_page = 0;
   wctx->col_count = 5;
   dblog_append_empty_row(wctx);
   dblog_set_col_val(wctx, 0, DBLOG_TYPE_TEXT, "table", 5);
   if (table_name == NULL)
     table_name = default_table_name;
   dblog_set_col_val(wctx, 1, DBLOG_TYPE_TEXT, table_name, strlen(table_name));
   dblog_set_col_val(wctx, 2, DBLOG_TYPE_TEXT, table_name, strlen(table_name));
   int32_t root_page = 2;
   dblog_set_col_val(wctx, 3, DBLOG_TYPE_INT, &root_page, 4);
   if (table_script) {
     uint16_t script_len = strlen(table_script);
     if (script_len > page_size - 100 - wctx->page_resv_bytes - 8 - 10)
       return DBLOG_RES_TOO_LONG;
     dblog_set_col_val(wctx, 4, DBLOG_TYPE_TEXT, table_script, script_len);
   } else {
     int table_name_len = strlen(table_name);
     int script_len = (13 + table_name_len + 2 + 5 * orig_col_count);
     if (script_len > page_size - 100 - wctx->page_resv_bytes - 8 - 10)
       return DBLOG_RES_TOO_LONG;
     dblog_set_col_val(wctx, 4, DBLOG_TYPE_TEXT, buf + 110, script_len);
     byte *script_pos = buf + page_size - buf[20] - script_len;
     memcpy(script_pos, "CREATE TABLE ", 13);
     script_pos += 13;
     memcpy(script_pos, table_name, table_name_len);
     script_pos += table_name_len;
     *script_pos++ = ' ';
     *script_pos++ = '(';
     for (int i = 0; i < orig_col_count; ) {
       i++;
       *script_pos++ = 'c';
       *script_pos++ = '0' + (i < 100 ? 0 : (i / 100));
       *script_pos++ = '0' + (i < 10 ? 0 : ((i < 100 ? i : i - 100) / 10));
       *script_pos++ = '0' + (i % 10);
       *script_pos++ = (i == orig_col_count ? ')' : ',');
     }
   }
   int res = write_page(wctx, 0, page_size);
   if (res)
     return res;
   wctx->col_count = orig_col_count;
   wctx->cur_write_page = 1;
   wctx->cur_write_rowid = 0;
   init_bt_tbl_leaf(wctx->buf);
   wctx->state = DBLOG_ST_WRITE_PENDING;
 
   return DBLOG_RES_OK;
 
 }
 
 // Returns the Row ID of the last record stored in the given buffer
 // Reads the buffer part by part to avoid reading entire buffer into memory
 // to support low memory systems (2kb ram)
 // The underlying callback function hopefully optimizes repeated IO
 int get_last_rowid(struct dblog_write_context *wctx, uint32_t pos,
            int32_t page_size, uint32_t *out_rowid) {
   byte src_buf[12];
   int res = read_bytes_wctx(wctx, src_buf, pos * page_size, 12);
   if (res)
     return res;
   uint16_t last_pos = read_uint16(src_buf + 5);
   if (!last_pos && *src_buf == 5) {
     *out_rowid = 0;
     return DBLOG_RES_OK;
   }
   if (last_pos > page_size - 12)
     return DBLOG_RES_MALFORMED;
   uint8_t page_type = *src_buf;
   uint16_t remaining = page_size - wctx->page_resv_bytes - last_pos;
   uint8_t chk_sum = 0;
   for (int i = 0; i < 8; i++)
     chk_sum += src_buf[i];
   res = read_bytes_wctx(wctx, src_buf,
     pos * page_size + (page_type == 13 ? last_pos - 1 : (12 + read_uint16(src_buf + 3) * 2)),
     (page_type == 5 || remaining > 12 ? 12 : remaining));
   if (res)
     return res;
   int8_t vint_len;
   *out_rowid = read_vint32(src_buf + (page_type == 13 ? 4 : 0), &vint_len);
   for (int i = 1; i < 4 + vint_len; i++)
     chk_sum += src_buf[i];
   if (page_type == 13) {
     if (chk_sum != *src_buf)
       return DBLOG_RES_INV_CHKSUM;
   }
   return DBLOG_RES_OK;
 }
 
 // Returns pointer to data of given column index
 // Also returns type of column according to record format
 // See https://www.sqlite.org/fileformat.html#record_format
 const void *get_col_val(byte *buf, uint16_t rec_data_pos,
         int col_idx, uint32_t *out_col_type, uint16_t limit) {
   byte *data_ptr;
   uint16_t rec_len;
   uint16_t hdr_len;
   byte *hdr_ptr = locate_column(buf + rec_data_pos, col_idx, 
           &data_ptr, &rec_len, &hdr_len, limit);
   if (!hdr_ptr)
     return NULL;
   int8_t cur_len_of_len;
   *out_col_type = read_vint32(hdr_ptr, &cur_len_of_len);
   return data_ptr;
 }
 
 // Checks possible signatures that a file can have
 int check_signature(buf) {
   if (memcmp(buf, dblog_sig, 16) && memcmp(buf, sqlite_sig, 16))
     return DBLOG_RES_INVALID_SIG;
   if (buf[68] != 0xA5)
     return DBLOG_RES_INVALID_SIG;
   return DBLOG_RES_OK;
 }
 
 byte *locate_col_root_page(byte *buf, int32_t page_size) {
   byte *data_ptr;
   uint16_t rec_len;
   uint16_t hdr_len;
   uint16_t last_pos = read_uint16(buf + 105);
   if (!locate_column(buf + last_pos, 3,
          &data_ptr, &rec_len, &hdr_len, page_size - last_pos))
     return NULL;
   return data_ptr;
 }
 
 // See .h file for API description
 int dblog_write_init_with_script(struct dblog_write_context *wctx, 
       char *table_name, char *table_script) {
   return form_page1(wctx, table_name, table_script);
 }
 
 // See .h file for API description
 int dblog_write_init(struct dblog_write_context *wctx) {
   return dblog_write_init_with_script(wctx, 0, 0);
 }
 
 // Checks space for appending new row
 // If space not available, writes current buffer to disk and
 // initializes buffer as new page
 uint16_t make_space_for_new_row(struct dblog_write_context *wctx, int32_t page_size,
            uint16_t len_of_rec_len_rowid, uint16_t new_rec_len) {
   byte *ptr = wctx->buf + (wctx->buf[0] == 13 ? 0 : 100);
   uint16_t last_pos = read_uint16(ptr + 5);
   if (last_pos && last_pos > page_size - wctx->page_resv_bytes - 7)
     return 0; // corruption
   int rec_count = read_uint16(ptr + 3) + 1;
   if (last_pos && rec_count * 2 + 8 >= last_pos)
     return 0; // corruption
   if (last_pos == 0)
     last_pos = page_size - wctx->page_resv_bytes;
   if (last_pos && last_pos < ((ptr - wctx->buf) + 9 + CHKSUM_LEN
        + (rec_count * 2) + new_rec_len + len_of_rec_len_rowid)) {
     int res = write_page(wctx, wctx->cur_write_page, page_size);
     if (res)
       return res;
     wctx->cur_write_page++;
     init_bt_tbl_leaf(wctx->buf);
     last_pos = page_size - wctx->page_resv_bytes - new_rec_len - len_of_rec_len_rowid;
   } else {
     last_pos -= new_rec_len;
     last_pos -= len_of_rec_len_rowid;
   }
   return last_pos;
 }
 
 // Writes given value at given pointer in Sqlite format
 uint16_t write_data(byte *data_ptr, int type, const void *val, uint16_t len) {
   if (val == NULL)
     return 0;
   if (type == DBLOG_TYPE_INT) {
     switch (len) {
       case 1:
         write_uint8(data_ptr, *((int8_t *) val));
         break;
       case 2:
         write_uint16(data_ptr, *((int16_t *) val));
         break;
       case 4:
         write_uint32(data_ptr, *((int32_t *) val));
         break;
       case 8:
         write_uint64(data_ptr, *((int64_t *) val));
         break;
     }
   } else
   if (type == DBLOG_TYPE_REAL && len == 4) {
     // Assumes float is represented in IEEE-754 format
     uint64_t bytes64 = float_to_double(val);
     write_uint64(data_ptr, bytes64);
     len = 8;
   } else
   if (type == DBLOG_TYPE_REAL && len == 8) {
     // Assumes double is represented in IEEE-754 format
     uint64_t bytes = *((uint64_t *) val);
     write_uint64(data_ptr, bytes);
   } else
     memcpy(data_ptr, val, len);
   return len;
 }
 
 // See .h file for API description
 int dblog_append_row_with_values(struct dblog_write_context *wctx,
       uint8_t types[], const void *values[], uint16_t lengths[]) {
 
   wctx->cur_write_rowid++;
   byte *ptr = wctx->buf + (wctx->buf[0] == 13 ? 0 : 100);
   int32_t page_size = get_pagesize(wctx->page_size_exp);
   uint16_t len_of_rec_len_rowid = LEN_OF_REC_LEN + get_vlen_of_uint32(wctx->cur_write_rowid);
   uint16_t new_rec_len = 0;
   uint16_t hdr_len = LEN_OF_HDR_LEN;
   for (int i = 0; i < wctx->col_count; i++) {
     if (values[i] != NULL)
       new_rec_len += (types[i] == DBLOG_TYPE_REAL ? 8 : lengths[i]);
     uint32_t col_type = derive_col_type_or_len(types[i], values[i], lengths[i]);
     hdr_len += get_vlen_of_uint32(col_type);
   }
   new_rec_len += hdr_len;
   uint16_t last_pos = make_space_for_new_row(wctx, page_size,
                         len_of_rec_len_rowid, new_rec_len);
   if (!last_pos)
     return DBLOG_RES_MALFORMED;
   int rec_count = read_uint16(ptr + 3) + 1;
   if (rec_count * 2 + 8 >= last_pos)
     return DBLOG_RES_MALFORMED;
 
   write_rec_len_rowid_hdr_len(wctx->buf + last_pos, new_rec_len, 
                     wctx->cur_write_rowid, hdr_len);
   byte *rec_ptr = wctx->buf + last_pos + len_of_rec_len_rowid + LEN_OF_HDR_LEN;
   for (int i = 0; i < wctx->col_count; i++) {
     uint32_t col_type = derive_col_type_or_len(types[i], values[i], lengths[i]);
     int8_t vint_len = write_vint32(rec_ptr, col_type);
     rec_ptr += vint_len;
   }
   for (int i = 0; i < wctx->col_count; i++) {
     if (values[i] != NULL)
       rec_ptr += write_data(rec_ptr, types[i], values[i], lengths[i]);
   }
   write_uint16(ptr + 3, rec_count);
   write_uint16(ptr + 5, last_pos);
   write_uint16(ptr + 8 - 2 + (rec_count * 2), last_pos);
   wctx->state = DBLOG_ST_WRITE_PENDING;
 
   return DBLOG_RES_OK;
 }
 
 // See .h file for API description
 int dblog_append_empty_row(struct dblog_write_context *wctx) {
 
   wctx->cur_write_rowid++;
   byte *ptr = wctx->buf + (wctx->buf[0] == 13 ? 0 : 100);
   int32_t page_size = get_pagesize(wctx->page_size_exp);
   uint16_t len_of_rec_len_rowid = LEN_OF_REC_LEN + get_vlen_of_uint32(wctx->cur_write_rowid);
   uint16_t new_rec_len = wctx->col_count;
   new_rec_len += LEN_OF_HDR_LEN;
   uint16_t last_pos = make_space_for_new_row(wctx, page_size,
                         len_of_rec_len_rowid, new_rec_len);
   if (!last_pos)
     return DBLOG_RES_MALFORMED;
   int rec_count = read_uint16(ptr + 3) + 1;
   if (rec_count * 2 + 8 >= last_pos)
     return DBLOG_RES_MALFORMED;
 
   memset(wctx->buf + last_pos, '\0', new_rec_len + len_of_rec_len_rowid);
   write_rec_len_rowid_hdr_len(wctx->buf + last_pos, new_rec_len, 
                     wctx->cur_write_rowid, wctx->col_count + LEN_OF_HDR_LEN);
   write_uint16(ptr + 3, rec_count);
   write_uint16(ptr + 5, last_pos);
   write_uint16(ptr + 8 - 2 + (rec_count * 2), last_pos);
   wctx->state = DBLOG_ST_WRITE_PENDING;
 
   return DBLOG_RES_OK;
 }
 
 // See .h file for API description
 int dblog_set_col_val(struct dblog_write_context *wctx,
               int col_idx, int type, const void *val, uint16_t len) {
 
   byte *ptr = wctx->buf + (wctx->buf[0] == 13 ? 0 : 100);
   int32_t page_size = get_pagesize(wctx->page_size_exp);
   uint16_t last_pos = acquire_last_pos(wctx, ptr);
   int rec_count = read_uint16(ptr + 3);
   byte *data_ptr;
   uint16_t rec_len;
   uint16_t hdr_len;
   byte *hdr_ptr = locate_column(wctx->buf + last_pos, col_idx, 
                         &data_ptr, &rec_len, &hdr_len, page_size - last_pos);
   if (hdr_ptr == NULL)
     return DBLOG_RES_MALFORMED;
   int8_t cur_len_of_len;
   uint16_t cur_len = dblog_derive_data_len(read_vint32(hdr_ptr, &cur_len_of_len));
   uint16_t new_len = val == NULL ? 0 : (type == DBLOG_TYPE_REAL ? 8 : len);
   int32_t diff = new_len - cur_len;
   if (rec_len + diff + 2 > page_size - wctx->page_resv_bytes)
     return DBLOG_RES_TOO_LONG;
   uint16_t new_last_pos = last_pos + cur_len - new_len - LEN_OF_HDR_LEN;
   if (new_last_pos < (ptr - wctx->buf) + 9 + CHKSUM_LEN + rec_count * 2) {
     uint16_t prev_last_pos = read_uint16(ptr + 8 + (rec_count - 2) * 2);
     write_uint16(ptr + 3, rec_count - 1);
     write_uint16(ptr + 5, prev_last_pos);
     saveChecksumBytes(ptr, prev_last_pos);
     int res = write_page(wctx, wctx->cur_write_page, page_size);
     if (res)
       return res;
     restoreChecksumBytes(ptr, prev_last_pos);
     wctx->cur_write_page++;
     init_bt_tbl_leaf(wctx->buf);
     int8_t len_of_rowid;
     read_vint32(wctx->buf + last_pos + 3, &len_of_rowid);
     memmove(wctx->buf + page_size - wctx->page_resv_bytes 
             - len_of_rowid - rec_len - LEN_OF_REC_LEN,
             wctx->buf + last_pos, len_of_rowid + rec_len + LEN_OF_REC_LEN);
     hdr_ptr -= last_pos;
     data_ptr -= last_pos;
     last_pos = page_size - wctx->page_resv_bytes - len_of_rowid - rec_len - LEN_OF_REC_LEN;
     hdr_ptr += last_pos;
     data_ptr += last_pos;
     rec_count = 1;
     write_uint16(ptr + 3, rec_count);
     write_uint16(ptr + 5, last_pos);
   }
 
   // make (or reduce) space and copy data
   new_last_pos = last_pos - diff;
   memmove(wctx->buf + new_last_pos, wctx->buf + last_pos,
           data_ptr - wctx->buf - last_pos);
   data_ptr -= diff;
   write_data(data_ptr, type, val, len);
 
   // make (or reduce) space and copy len
   uint32_t new_type_or_len = derive_col_type_or_len(type, val, new_len);
   int8_t new_len_of_len = get_vlen_of_uint32(new_type_or_len);
   int8_t hdr_diff = new_len_of_len -  cur_len_of_len;
   diff += hdr_diff;
   if (hdr_diff) {
     memmove(wctx->buf + new_last_pos - hdr_diff, wctx->buf + new_last_pos,
           hdr_ptr - wctx->buf - last_pos);
   }
   write_vint32(hdr_ptr - diff, new_type_or_len);
 
   new_last_pos -= hdr_diff;
   write_rec_len_rowid_hdr_len(wctx->buf + new_last_pos, rec_len + diff,
                               wctx->cur_write_rowid, hdr_len + hdr_diff);
   write_uint16(ptr + 5, new_last_pos);
   rec_count--;
   write_uint16(ptr + 8 + rec_count * 2, new_last_pos);
   wctx->state = DBLOG_ST_WRITE_PENDING;
 
s   return DBLOG_RES_OK;
 }
 
 // See .h file for API description
 const void *dblog_get_col_val(struct dblog_write_context *wctx,
         int col_idx, uint32_t *out_col_type) {
   int32_t page_size = get_pagesize(wctx->page_size_exp);
   uint16_t last_pos = read_uint16(wctx->buf + 5);
   if (last_pos == 0)
     return NULL;
   if (last_pos > page_size - wctx->page_resv_bytes - 7)
     return NULL;
   return get_col_val(wctx->buf, last_pos, col_idx, 
            out_col_type, page_size - wctx->page_resv_bytes - last_pos);
 }
 
 // See .h file for API description
 int dblog_flush(struct dblog_write_context *wctx) {
   int32_t page_size = get_pagesize(wctx->page_size_exp);
   int res = write_page(wctx, wctx->cur_write_page, page_size);
   if (res)
     return res;
   int ret = wctx->flush_fn(wctx);
   if (!ret)
     wctx->state = DBLOG_ST_WRITE_NOT_PENDING;
   return ret;
 }
 
 // See .h file for API description
 int dblog_partial_finalize(struct dblog_write_context *wctx) {
   int res;
   if (wctx->state == DBLOG_ST_WRITE_PENDING) {
     res = dblog_flush(wctx);
     if (res)
       return res;
   }
   int32_t page_size = get_pagesize(wctx->page_size_exp);
   res = read_bytes_wctx(wctx, wctx->buf, 0, page_size);
   if (res)
     return res;
   if (memcmp(wctx->buf, sqlite_sig, 16) == 0)
     return DBLOG_RES_OK;
   uint32_t last_leaf_page = read_uint32(wctx->buf + 60);
   // Update the last page no. in first page
   if (last_leaf_page == 0) {
     if (!wctx->cur_write_page) {
       byte head_buf[8];
       do {
         res = read_bytes_wctx(wctx, head_buf, (wctx->cur_write_page + 1) * page_size, 8);
         if (res)
           break;
         if (head_buf[0] == 13)
           wctx->cur_write_page++;
       } while (head_buf[0] == 13);
     }
     if (wctx->cur_write_page) {
       write_uint32(wctx->buf + 60, wctx->cur_write_page);
       res = write_page(wctx, 0, page_size);
       if (res)
         return res;
     } else
       return DBLOG_RES_MALFORMED;
   }
   return DBLOG_RES_OK;
 }
 
 // See .h file for API description
 int dblog_finalize(struct dblog_write_context *wctx) {
 
   int res = dblog_partial_finalize(wctx);
   if (res)
     return res;
 
   if (memcmp(wctx->buf, sqlite_sig, 16) == 0)
     return DBLOG_RES_OK;
 
   int32_t page_size = get_pagesize(wctx->page_size_exp);
   uint32_t next_level_cur_pos = wctx->cur_write_page + 1;
   uint32_t next_level_begin_pos = next_level_cur_pos;
   uint32_t cur_level_pos = 1;
   uint32_t rowid;
   while (wctx->cur_write_page != 1) {
     init_bt_tbl_inner(wctx->buf);
     while (cur_level_pos < next_level_begin_pos) {
       res = get_last_rowid(wctx, cur_level_pos, page_size, &rowid);
       if (res) {
         cur_level_pos++;
         if (res == DBLOG_RES_INV_CHKSUM)
           continue;
         else
           break;
       }
       if (add_rec_to_inner_tbl(wctx, wctx->buf, rowid, cur_level_pos)) {
         res = write_page(wctx, next_level_cur_pos, page_size);
         if (res)
           return res;
         next_level_cur_pos++;
         init_bt_tbl_inner(wctx->buf);
       }
       cur_level_pos++;
     }
     uint16_t rec_count = read_uint16(wctx->buf + 3);
     if (rec_count) { // remove last row and write as right most pointer
       write_uint32(wctx->buf + 8, cur_level_pos);
       rec_count--;
       write_vint32(wctx->buf + 12 + rec_count * 2, rowid);
       write_uint16(wctx->buf + 3, rec_count);
       if (rec_count) {
         write_uint16(wctx->buf + 5,
           read_uint16(wctx->buf + 12 + (rec_count - 1) * 2));
       } else
         write_uint16(wctx->buf + 5, 0);
       res = write_page(wctx, next_level_cur_pos, page_size);
       if (res)
         return res;
       next_level_cur_pos++;
     }
     if (next_level_begin_pos == next_level_cur_pos - 1)
       break;
     else {
       cur_level_pos = next_level_begin_pos;
       next_level_begin_pos = next_level_cur_pos;
     }
   }
 
   res = read_bytes_wctx(wctx, wctx->buf, 0, page_size);
   if (res)
     return res;
   byte *data_ptr = locate_col_root_page(wctx->buf, page_size - wctx->page_resv_bytes);
   if (data_ptr == NULL)
     return DBLOG_RES_MALFORMED;
   write_uint32(data_ptr, next_level_cur_pos); // update root_page
   write_uint32(wctx->buf + 28, next_level_cur_pos); // update page_count
   memcpy(wctx->buf, sqlite_sig, 16);
   res = write_page(wctx, 0, page_size);
   if (res)
     return res;
 
   return DBLOG_RES_OK;
 }
 
 // See .h file for API description
 int dblog_not_finalized(struct dblog_write_context *wctx) {
   int res = read_bytes_wctx(wctx, wctx->buf, 0, 72);
   if (res)
     return res;
   if (memcmp(wctx->buf, sqlite_sig, 16) == 0)
     return DBLOG_RES_OK;
   return DBLOG_RES_NOT_FINALIZED;
 }
 
 // See .h file for API description
 int dblog_init_for_append(struct dblog_write_context *wctx) {
   int res = read_bytes_wctx(wctx, wctx->buf, 0, 72);
   if (res)
     return res;
   if (check_signature(wctx->buf))
     return DBLOG_RES_INVALID_SIG;
   int32_t page_size = read_uint16(wctx->buf + 16);
   if (page_size == 1)
     page_size = 65536;
   wctx->page_size_exp = get_page_size_exp(page_size);
   if (!wctx->page_size_exp)
     return DBLOG_RES_MALFORMED;
   res = read_bytes_wctx(wctx, wctx->buf, 0, page_size);
   if (res)
     return res;
   wctx->cur_write_page = read_uint32(wctx->buf + 60);
   if (wctx->cur_write_page == 0)
     return DBLOG_RES_NOT_FINALIZED;
   memcpy(wctx->buf, dblog_sig, 16);
   write_uint32(wctx->buf + 60, 0);
   res = write_page(wctx, 0, page_size);
   if (res)
     return res;
   res = get_last_rowid(wctx, wctx->cur_write_page, page_size, &wctx->cur_write_rowid);
   if (res)
     return res;
   res = read_bytes_wctx(wctx, wctx->buf, wctx->cur_write_page * page_size, page_size);
   if (res)
     return res;
   wctx->state = DBLOG_ST_WRITE_NOT_PENDING;
   return DBLOG_RES_OK;
 }
 
var SQLite_uLogger = function (file_name, col_count, page_size, max_pages, page_resv_bytes, table_name, table_script) {
   this.col_count = col_count;
   this.page_size = page_size;
   this.max_pages = max_pages;
   this.page_resv_bytes = page_resv_bytes;
   this.table_name = table_name;
   this.table_script = table_script;
   this.DBLOG_ST_WRITE_NOT_PENDING = 0xA4;
   this.DBLOG_ST_WRITE_PENDING = 0xA5;
   this.DBLOG_ST_TO_RECOVER = 0xA6;
   this.DBLOG_ST_FINAL = 0xA7;
   this.cur_write_page = 0;
   this.cur_write_rowid = 0;
   this.state = 0;
   this.abuf = new ArrayBuffer(page_size);
   this.buf = new Uint8Array(abuf);
   this.err_no = 0;
   this.fd = fs.open()
   return this;
}

SQLite_uLogger.prototype.append_empty_row = function() {
}
SQLite_uLogger.prototype.append_row_with_values = function(types, values, lengths) {
}
SQLite_uLogger.prototype.set_col_val = function(col_idx, type, val, len) {
}
SQLite_uLogger.prototype.get_col_val = function(col_idx, out_col_type) {
}
SQLite_uLogger.prototype.flush = function() {
}
SQLite_uLogger.prototype.partial_finalize = function() {
}
SQLite_uLogger.prototype.finalize = function() {
}
SQLite_uLogger.prototype.not_finalized = function() {
}
SQLite_uLogger.prototype.read_bytes(offset, pos, length) {
  var bytesRead = fs.readSync(this.fd, this.buf, offset, length, pos);
  if (bytesRead != length)
    return this.DBLOG_RES_READ_ERR;
}
// Writes a page to disk using the given callback function
SQLite_uLogger.prototype.write_page = function(page_no, page_size) {
  check_sums(this.buf, page_size, 0);
  var bytesWritten = fs.writeSync(this.fd, this.buf, 0, page_size, page_no * page_size);
  if (bytesWritten != page_size)
    return DBLOG_RES_READ_ERR;
  return DBLOG_RES_OK;
}
SQLite_uLogger.prototype.read_page_size = function() {
  var res = read_bytes(0, 0, 72);
  if (res)
    return res;
  if (check_signature())
    return DBLOG_RES_INVALID_SIG;
  this.page_size = read_uint16(this.buf + 16);
  if (this.page_size == 1)
    this.page_size = 65536;
  return this.page_size;
}
SQLite_uLogger.prototype.recover = function() {
  this.state = DBLOG_ST_TO_RECOVER;
  this.cur_write_page = 0;
  var res = finalize();
  if (res)
    return res;
  return DBLOG_RES_OK;
}

module.exports = {
   SQLite_uLogger: SQLite_uLogger,
   DBLOG_TYPE_INT: DBLOG_TYPE_INT,
   DBLOG_TYPE_REAL: DBLOG_TYPE_REAL,
   DBLOG_TYPE_BLOB: DBLOG_TYPE_BLOB,
   DBLOG_TYPE_TEXT: DBLOG_TYPE_TEXT,
   DBLOG_RES_OK: DBLOG_RES_OK,
   DBLOG_RES_ERR: DBLOG_RES_ERR,
   DBLOG_RES_INV_PAGE_SZ: DBLOG_RES_INV_PAGE_SZ,
   DBLOG_RES_TOO_LONG: DBLOG_RES_TOO_LONG,
   DBLOG_RES_WRITE_ERR: DBLOG_RES_WRITE_ERR,
   DBLOG_RES_FLUSH_ERR: DBLOG_RES_FLUSH_ERR,
   DBLOG_RES_SEEK_ERR: DBLOG_RES_SEEK_ERR,
   DBLOG_RES_READ_ERR: DBLOG_RES_READ_ERR,
   DBLOG_RES_INVALID_SIG: DBLOG_RES_INVALID_SIG,
   DBLOG_RES_MALFORMED: DBLOG_RES_MALFORMED,
   DBLOG_RES_NOT_FOUND: DBLOG_RES_NOT_FOUND,
   DBLOG_RES_NOT_FINALIZED: DBLOG_RES_NOT_FINALIZED,
   DBLOG_RES_TYPE_MISMATCH: DBLOG_RES_TYPE_MISMATCH,
   DBLOG_RES_INV_CHKSUM: DBLOG_RES_INV_CHKSUM
}
