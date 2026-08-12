// Problem 015 - File Storage
// Persistent key-value store on disk using a B+ tree with 16 KiB blocks.
// - index: string <= 64 bytes (no whitespace)
// - value: non-negative 32-bit int; same (index,value) never inserted twice
// Commands: insert idx val | delete idx val | find idx
// Data survives across program runs (file kept; judge cleans between cases).
//
// Memory usage is kept small: only an LRU cache of blocks is kept in RAM.

#include <cstdint>
#include <cstring>
#include <cstdlib>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#ifdef DEBUG_MEM
#include <cstdio>
#endif

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef int32_t  i32;
typedef int64_t  i64;

// ---------------- constants ----------------
static const int  BS      = 16384;            // block size
static const u32  MAGIC   = 0x31424B56u;      // "VKB1"
static const int  LEAF    = 1;
static const int  INTERN  = 2;
static const int  KMAX    = 64;               // max index bytes
static const int  SLOTB   = 1 + KMAX + 4;     // entry: len(1)+key(64)+val(4) = 69
static const int  LEAF_HDR = 8;
static const int  LEAF_CAP = (BS - LEAF_HDR) / SLOTB;            // 237
static const int  INT_CAP  = (BS - 8 - 4) / (SLOTB + 4);         // 224
static const int  INT_KEYBASE = 4 + 4 * (INT_CAP + 1);           // 904
static const int  NSLOT   = 40;               // cache slots (~640 KiB)
static const char *DBFILE = "kvdb.dat";

// ---------------- globals ----------------
static int fd = -1;
static i32 root_id = -1;
static i32 nblocks = 1;          // block 0 = meta

// cache
struct Slot { i32 id; u32 last; bool dirty; };
static Slot slots[NSLOT];
static u8  *cmem = nullptr;      // NSLOT * BS
static u32 clk = 0;
static int root_slot = -1;

// scratch
static u8  leaf_tmp[(LEAF_CAP + 1) * SLOTB];   // 238*69
static u8  int_ktmp[(INT_CAP + 1) * SLOTB];    // 225*69
static i32 int_ctmp[INT_CAP + 2];              // 226

// descent path
static i32 path_nodes[16];
static int path_child[16];
static int path_depth = 0;

// ---------------- small helpers ----------------
static inline u16 rd16(const u8 *p){ u16 v; memcpy(&v,p,2); return v; }
static inline i32 rd32(const u8 *p){ i32 v; memcpy(&v,p,4); return v; }
static inline void wr32(u8 *p, i32 v){ memcpy(p,&v,4); }

static inline int  ntype(const u8 *b){ return b[0]; }
static inline int  ncount(const u8 *b){ return rd16(b + 1); }
static inline void set_ncount(u8 *b, int c){ b[1] = (u8)(c & 255); b[2] = (u8)(c >> 8); }

static inline i32  leaf_next(const u8 *b){ return rd32(b + 4); }
static inline void set_leaf_next(u8 *b, i32 v){ wr32(b + 4, v); }
static inline u8*  leaf_ent(u8 *b, int i){ return b + LEAF_HDR + i * SLOTB; }

static inline u8*  ikey(u8 *b, int i){ return b + INT_KEYBASE + i * SLOTB; }
static inline i32  ichild(const u8 *b, int i){ return rd32(b + 4 + 4 * i); }
static inline void set_ichild(u8 *b, int i, i32 v){ wr32((u8*)b + 4 + 4 * i, v); }

static inline int  ent_len(const u8 *e){ return e[0]; }
static inline u32  ent_val(const u8 *e){ u32 v; memcpy(&v, e + 1 + KMAX, 4); return v; }
static inline void set_ent_val(u8 *e, u32 v){ memcpy(e + 1 + KMAX, &v, 4); }

// compare full keys (index bytes, then value)
static int cmp_raw(const u8 *ka, int la, u32 va, const u8 *kb, int lb, u32 vb){
    int m = la < lb ? la : lb;
    int c = memcmp(ka, kb, m);
    if (c) return c;
    if (la != lb) return la < lb ? -1 : 1;
    if (va != vb) return va < vb ? -1 : 1;
    return 0;
}
// compare entry/key-slot e (layout len,key,val) against raw key
static inline int cmp_ent(const u8 *e, const u8 *ka, int la, u32 va){
    return cmp_raw(e + 1, e[0], ent_val(e), ka, la, va);
}
// compare only the index part
static inline int cmp_idx(const u8 *e, const u8 *ka, int la){
    int el = e[0];
    int m = el < la ? el : la;
    int c = memcmp(e + 1, ka, m);
    if (c) return c;
    if (el != la) return el < la ? -1 : 1;
    return 0;
}

static void write_full(int f, const void *buf, size_t n, off_t off){
    const u8 *p = (const u8*)buf;
    while (n > 0){
        ssize_t w = pwrite(f, p, n, off);
        if (w <= 0) _exit(1);
        p += w; n -= (size_t)w; off += w;
    }
}

static void read_full(int f, void *buf, size_t n, off_t off){
    u8 *p = (u8*)buf;
    while (n > 0){
        ssize_t r = pread(f, p, n, off);
        if (r <= 0) _exit(1);
        p += r; n -= (size_t)r; off += r;
    }
}

// ---------------- cache ----------------
static inline Slot* slot_of(u8 *p){ return &slots[(size_t)(p - cmem) / BS]; }
static inline void mark_dirty(u8 *p){ slot_of(p)->dirty = true; }

static int pick_victim(){
    int vic = -1;
    u32 oldest = ~0u;
    for (int i = 0; i < NSLOT; i++){
        if (slots[i].id == -1) return i;
        if (i == root_slot) continue;
        if (slots[i].last < oldest){ oldest = slots[i].last; vic = i; }
    }
    return vic;
}

static u8* fetch(i32 id){
    for (int i = 0; i < NSLOT; i++){
        if (slots[i].id == id){
            slots[i].last = ++clk;
            return cmem + (size_t)i * BS;
        }
    }
    int v = pick_victim();
    Slot &s = slots[v];
    if (s.id != -1 && s.dirty){
        write_full(fd, cmem + (size_t)v * BS, BS, (off_t)s.id * BS);
        s.dirty = false;
    }
    s.id = id; s.last = ++clk;
    read_full(fd, cmem + (size_t)v * BS, BS, (off_t)id * BS);
    return cmem + (size_t)v * BS;
}

// allocate a fresh block, returned zero-initialized in cache (dirty)
static u8* alloc_block(i32 *out_id){
    i32 id = nblocks++;
    int v = pick_victim();
    Slot &s = slots[v];
    if (s.id != -1 && s.dirty){
        write_full(fd, cmem + (size_t)v * BS, BS, (off_t)s.id * BS);
    }
    s.id = id; s.last = ++clk; s.dirty = true;
    memset(cmem + (size_t)v * BS, 0, BS);
    *out_id = id;
    return cmem + (size_t)v * BS;
}

static void flush_cache(){
    for (int i = 0; i < NSLOT; i++){
        if (slots[i].id != -1 && slots[i].dirty){
            write_full(fd, cmem + (size_t)i * BS, BS, (off_t)slots[i].id * BS);
            slots[i].dirty = false;
        }
    }
}

// ---------------- meta ----------------
alignas(4096) static u8 metabuf[4096];

static void save_meta(){
    memset(metabuf, 0, 4096);
    wr32(metabuf, (i32)MAGIC);
    wr32(metabuf + 4, root_id);
    wr32(metabuf + 8, nblocks);
    wr32(metabuf + 12, 0);
    write_full(fd, metabuf, 4096, 0);
}

static void load_or_init(){
    memset(metabuf, 0, 4096);
    ssize_t r = pread(fd, metabuf, 4096, 0);
    if (r >= 16 && rd32(metabuf) == (i32)MAGIC){
        root_id = rd32(metabuf + 4);
        nblocks = rd32(metabuf + 8);
        u8 *b = fetch(root_id);
        root_slot = (int)(slot_of(b) - slots);
        return;
    }
    // fresh database: empty root leaf
    nblocks = 1;
    i32 rid;
    u8 *b = alloc_block(&rid);
    b[0] = LEAF;
    set_ncount(b, 0);
    set_leaf_next(b, -1);
    root_id = rid;
    root_slot = (int)(slot_of(b) - slots);
    save_meta();
}

static void set_root(i32 id, u8 *ptr){
    root_id = id;
    root_slot = (int)(slot_of(ptr) - slots);
}

// ---------------- descent ----------------
// returns leaf block id; fills path_nodes[0..depth-1] with internal nodes and
// path_child[i] = child index taken inside path_nodes[i]
static i32 descend(const u8 *ka, int la, u32 va){
    i32 cur = root_id;
    path_depth = 0;
    for (;;){
        u8 *b = fetch(cur);
        if (ntype(b) == LEAF) return cur;
        int c = ncount(b);
        int lo = 0, hi = c;
        while (lo < hi){
            int mid = (lo + hi) >> 1;
            if (cmp_ent(ikey(b, mid), ka, la, va) <= 0) lo = mid + 1;
            else hi = mid;
        }
        path_nodes[path_depth] = cur;
        path_child[path_depth] = lo;
        path_depth++;
        cur = ichild(b, lo);
    }
}

// first entry >= key inside leaf
static int leaf_lb(const u8 *b, const u8 *ka, int la, u32 va){
    int lo = 0, hi = ncount(b);
    while (lo < hi){
        int mid = (lo + hi) >> 1;
        if (cmp_ent(leaf_ent((u8*)b, mid), ka, la, va) < 0) lo = mid + 1;
        else hi = mid;
    }
    return lo;
}

// ---------------- insert ----------------
static void insert_into_parent(int depth, i32 left_id, const u8 *sep, i32 right_id){
    u8 sepbuf[SLOTB];
    memcpy(sepbuf, sep, SLOTB);
    if (depth == 0){
        // root (leaf) was split: create new root
        i32 nid;
        u8 *N = alloc_block(&nid);
        N[0] = INTERN;
        set_ncount(N, 1);
        set_ichild(N, 0, root_id);
        set_ichild(N, 1, right_id);
        memcpy(ikey(N, 0), sepbuf, SLOTB);
        set_root(nid, N);
        return;
    }
    i32 pid = path_nodes[depth - 1];
    int j = path_child[depth - 1];
    u8 *P = fetch(pid);
    int c = ncount(P);
    if (c < INT_CAP){
        memmove(ikey(P, j + 1), ikey(P, j), (size_t)(c - j) * SLOTB);
        memcpy(ikey(P, j), sepbuf, SLOTB);
        memmove((u8*)P + 4 + 4 * (j + 2), (u8*)P + 4 + 4 * (j + 1), (size_t)(c - j) * 4);
        set_ichild(P, j + 1, right_id);
        set_ncount(P, c + 1);
        mark_dirty(P);
        return;
    }
    // split internal node: gather INT_CAP+1 keys and INT_CAP+2 children
    for (int i = 0; i < j; i++) memcpy(int_ktmp + (size_t)i * SLOTB, ikey(P, i), SLOTB);
    memcpy(int_ktmp + (size_t)j * SLOTB, sepbuf, SLOTB);
    for (int i = j; i < c; i++) memcpy(int_ktmp + (size_t)(i + 1) * SLOTB, ikey(P, i), SLOTB);
    for (int i = 0; i <= j; i++) int_ctmp[i] = ichild(P, i);
    int_ctmp[j + 1] = right_id;
    for (int i = j + 1; i <= c; i++) int_ctmp[i + 1] = ichild(P, i);
    const int LK = INT_CAP / 2;              // 112 keys left
    const int UP = LK;                       // key index going up
    i32 rid;
    u8 *R = alloc_block(&rid);
    R[0] = INTERN;
    set_ncount(R, INT_CAP - UP);             // 112
    for (int i = 0; i <= INT_CAP - UP; i++) set_ichild(R, i, int_ctmp[UP + 1 + i]);
    for (int i = 0; i < INT_CAP - UP; i++)
        memcpy(ikey(R, i), int_ktmp + (size_t)(UP + 1 + i) * SLOTB, SLOTB);
    set_ncount(P, LK);
    for (int i = 0; i <= LK; i++) set_ichild(P, i, int_ctmp[i]);
    mark_dirty(P);
    insert_into_parent(depth - 1, pid, int_ktmp + (size_t)UP * SLOTB, rid);
}

static void do_insert(const u8 *ka, int la, u32 va){
    i32 lid = descend(ka, la, va);
    u8 *L = fetch(lid);
    int c = ncount(L);
    int pos = leaf_lb(L, ka, la, va);
    if (pos < c && cmp_ent(leaf_ent(L, pos), ka, la, va) == 0) return; // dup guard
    if (c < LEAF_CAP){
        memmove(leaf_ent(L, pos + 1), leaf_ent(L, pos), (size_t)(c - pos) * SLOTB);
        u8 *e = leaf_ent(L, pos);
        e[0] = (u8)la;
        memcpy(e + 1, ka, la);
        set_ent_val(e, va);
        set_ncount(L, c + 1);
        mark_dirty(L);
        return;
    }
    // leaf full: gather LEAF_CAP+1 entries into tmp
    memcpy(leaf_tmp, L + LEAF_HDR, (size_t)pos * SLOTB);
    u8 *ne = leaf_tmp + (size_t)pos * SLOTB;
    ne[0] = (u8)la;
    memcpy(ne + 1, ka, la);
    memset(ne + 1 + la, 0, KMAX - la);
    set_ent_val(ne, va);
    memcpy(leaf_tmp + (size_t)(pos + 1) * SLOTB, L + LEAF_HDR + (size_t)pos * SLOTB,
           (size_t)(c - pos) * SLOTB);
    const int LN = (LEAF_CAP + 1) / 2;       // 119 left, 119 right
    i32 rid;
    u8 *R = alloc_block(&rid);
    R[0] = LEAF;
    set_ncount(R, LEAF_CAP + 1 - LN);
    set_leaf_next(R, leaf_next(L));
    memcpy(R + LEAF_HDR, leaf_tmp + (size_t)LN * SLOTB, (size_t)(LEAF_CAP + 1 - LN) * SLOTB);
    set_ncount(L, LN);
    set_leaf_next(L, rid);
    memcpy(L + LEAF_HDR, leaf_tmp, (size_t)LN * SLOTB);
    mark_dirty(L);
    mark_dirty(R);
    insert_into_parent(path_depth, lid, R + LEAF_HDR, rid);
}

// ---------------- delete ----------------
static void do_delete(const u8 *ka, int la, u32 va){
    i32 lid = descend(ka, la, va);
    u8 *L = fetch(lid);
    int c = ncount(L);
    int pos = leaf_lb(L, ka, la, va);
    if (pos < c && cmp_ent(leaf_ent(L, pos), ka, la, va) == 0){
        memmove(leaf_ent(L, pos), leaf_ent(L, pos + 1), (size_t)(c - 1 - pos) * SLOTB);
        set_ncount(L, c - 1);
        mark_dirty(L);
    }
}

// ---------------- output ----------------
static const int OUTSZ = 64 * 1024;          // 64 KiB
static char outbuf[OUTSZ];
static int outpos = 0;

static void flush_out(){
    int done = 0;
    while (done < outpos){
        ssize_t w = write(1, outbuf + done, outpos - done);
        if (w <= 0) _exit(1);
        done += w;
    }
    outpos = 0;
}
static inline void out_reserve(int n){
    if (outpos + n > OUTSZ - 16) flush_out();
}
static inline void out_char(char ch){ outbuf[outpos++] = ch; }
static void out_u32(u32 v){
    char t[10];
    int n = 0;
    do { t[n++] = (char)('0' + v % 10); v /= 10; } while (v);
    out_reserve(n + 2);
    while (n) outbuf[outpos++] = t[--n];
}

// ---------------- find ----------------
static void do_find(const u8 *ka, int la){
    i32 lid = descend(ka, la, 0);
    i64 cnt = 0;
    int start = outpos;
    while (lid != -1){
        u8 *L = fetch(lid);
        int c = ncount(L);
        int pos = leaf_lb(L, ka, la, 0);
        bool stop = false;
        for (int i = pos; i < c; i++){
            u8 *e = leaf_ent(L, i);
            int cc = cmp_idx(e, ka, la);
            if (cc > 0){ stop = true; break; }
            if (cnt > 0) out_char(' ');
            out_u32(ent_val(e));
            cnt++;
            if (outpos > OUTSZ - 64) flush_out(); // cnt>0 here, safe
        }
        if (stop) break;
        lid = leaf_next(L);
    }
    if (cnt == 0){
        outpos = start;
        out_reserve(5);
        memcpy(outbuf + outpos, "null\n", 5);
        outpos += 5;
    } else {
        out_reserve(1);
        out_char('\n');
    }
}

// ---------------- input ----------------
static const int INSZ = 1 << 14;
static u8 inbuf[INSZ];
static size_t inpos = 0, inlen = 0;

static inline int gc(){
    if (inpos >= inlen){
        ssize_t r = read(0, inbuf, INSZ);
        if (r <= 0) return -1;
        inlen = (size_t)r;
        inpos = 0;
    }
    return inbuf[inpos++];
}
static inline int isws(int c){ return c == ' ' || c == '\n' || c == '\r' || c == '\t'; }
static int skipws(){
    int c;
    do { c = gc(); } while (c != -1 && isws(c));
    return c;
}
static int read_word(u8 *dst){
    int c = skipws();
    int n = 0;
    while (c != -1 && !isws(c)){
        dst[n++] = (u8)c;
        c = gc();
    }
    return n;
}
static u32 read_u32(){
    int c = skipws();
    u32 v = 0;
    while (c >= '0' && c <= '9'){
        v = v * 10 + (u32)(c - '0');
        c = gc();
    }
    return v;
}

// ---------------- main ----------------
static bool use_dio = false;

int main(){
    fd = open(DBFILE, O_RDWR | O_CREAT | O_DIRECT, 0644);
    if (fd >= 0){
        // probe: some filesystems accept the flag but reject IO.
        // Use a read probe for non-empty files so we never clobber data.
        struct stat st;
        if (fstat(fd, &st) == 0){
            ssize_t io;
            if (st.st_size > 0) io = pread(fd, metabuf, 4096, 0);
            else                io = pwrite(fd, metabuf, 4096, 0);
            if (io == 4096) use_dio = true;
            else { close(fd); fd = -1; }
        } else { close(fd); fd = -1; }
    }
    if (fd < 0) fd = open(DBFILE, O_RDWR | O_CREAT, 0644);
    if (fd < 0) return 1;
    cmem = (u8*)aligned_alloc(4096, (size_t)NSLOT * BS);
    if (!cmem) return 1;
    for (int i = 0; i < NSLOT; i++){ slots[i].id = -1; slots[i].last = 0; slots[i].dirty = false; }

    load_or_init();

    i64 n = (i64)read_u32();
    static u8 word[KMAX + 16];
    static u8 idx[KMAX + 4];
    for (i64 k = 0; k < n; k++){
        int wl = read_word(word);
        if (wl <= 0) break;
        if (word[0] == 'i'){          // insert
            int il = read_word(idx);
            u32 v = read_u32();
            do_insert(idx, il, v);
        } else if (word[0] == 'd'){   // delete
            int il = read_word(idx);
            u32 v = read_u32();
            do_delete(idx, il, v);
        } else {                      // find
            int il = read_word(idx);
            do_find(idx, il);
        }
        if ((k & 0x3FFF) == 0x3FFF){
            flush_cache();
            save_meta();
        }
    }
    flush_out();
    flush_cache();
    save_meta();
    fsync(fd);
    if (!use_dio) posix_fadvise(fd, 0, 0, POSIX_FADV_DONTNEED); // drop page cache
    close(fd);
    free(cmem);
#ifdef DEBUG_MEM
    {
        FILE *f = fopen("/proc/self/status", "r");
        char line[128];
        while (fgets(line, 128, f)) if (line[0]=='V' && line[1]=='m' && line[2]=='H') fputs(line, stderr);
        fclose(f);
    }
#endif
    return 0;
}
