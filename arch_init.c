/*
 * QEMU System Emulator
 *
 * Copyright (c) 2003-2008 Fabrice Bellard
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
#include <stdint.h>
#include <stdarg.h>
#ifndef _WIN32
#include <sys/types.h>
#include <sys/mman.h>
#endif
#include <assert.h>
#include "config.h"
#include "monitor.h"
#include "sysemu.h"
#include "arch_init.h"
#include "audio/audio.h"
#include "hw/pc.h"
#include "hw/pci.h"
#include "hw/audiodev.h"
#include "kvm.h"
#include "migration.h"
#include "net.h"
#include "gdbstub.h"
#include "hw/smbios.h"

//#define DEBUG_ARCH_INIT
//#define DEBUG_ARCH_INIT_CKSUM
#ifdef DEBUG_ARCH_INIT
#define dprintf(fmt, ...) \
    do { fprintf(stdout, "arch_init: " fmt, ## __VA_ARGS__); } while (0)
#else
#define dprintf(fmt, ...) \
    do { } while (0)
#endif

#ifdef DEBUG_ARCH_INIT_CKSUM
#define PAGE_LOG(addr, pdata, fmt, ...) \
    do { page_log(addr, pdata, fmt, ## __VA_ARGS__); } while (0)
#else
#define PAGE_LOG(addr, pdata, fmt, ...) \
    do { } while (0)
#endif

#ifdef TARGET_SPARC
int graphic_width = 1024;
int graphic_height = 768;
int graphic_depth = 8;
#else
int graphic_width = 800;
int graphic_height = 600;
int graphic_depth = 15;
#endif

const char arch_config_name[] = CONFIG_QEMU_CONFDIR "/target-" TARGET_ARCH ".conf";

#if defined(TARGET_ALPHA)
#define QEMU_ARCH QEMU_ARCH_ALPHA
#elif defined(TARGET_ARM)
#define QEMU_ARCH QEMU_ARCH_ARM
#elif defined(TARGET_CRIS)
#define QEMU_ARCH QEMU_ARCH_CRIS
#elif defined(TARGET_I386)
#define QEMU_ARCH QEMU_ARCH_I386
#elif defined(TARGET_M68K)
#define QEMU_ARCH QEMU_ARCH_M68K
#elif defined(TARGET_MICROBLAZE)
#define QEMU_ARCH QEMU_ARCH_MICROBLAZE
#elif defined(TARGET_MIPS)
#define QEMU_ARCH QEMU_ARCH_MIPS
#elif defined(TARGET_PPC)
#define QEMU_ARCH QEMU_ARCH_PPC
#elif defined(TARGET_S390X)
#define QEMU_ARCH QEMU_ARCH_S390X
#elif defined(TARGET_SH4)
#define QEMU_ARCH QEMU_ARCH_SH4
#elif defined(TARGET_SPARC)
#define QEMU_ARCH QEMU_ARCH_SPARC
#endif

const uint32_t arch_type = QEMU_ARCH;

/***********************************************************/
/* ram save/restore */

#define RAM_SAVE_FLAG_FULL  0x01 /* Obsolete, not used anymore */
#define RAM_SAVE_FLAG_COMPRESS  0x02
#define RAM_SAVE_FLAG_MEM_SIZE  0x04
#define RAM_SAVE_FLAG_PAGE  0x08
#define RAM_SAVE_FLAG_EOS   0x10
#define RAM_SAVE_FLAG_CONTINUE  0x20
#define RAM_SAVE_FLAG_XBRLE 0x40

/***********************************************************/
/* Page cache for storing previous pages as basis for XBRLE compression */
#define DEFAULT_CACHE_SIZE 0x8000000 /* 256 MB size) */
#define CACHE_N_WAY 2 /* 2-way assossiative cache */

typedef struct cache_item_t {
    ram_addr_t it_addr;
    unsigned long it_age;
    uint8_t *it_data;
} cache_item_t;

typedef struct cache_bucket_t {
    cache_item_t bkt_item[CACHE_N_WAY];
} cache_bucket_t;

static cache_bucket_t *page_cache;
static int64_t cache_num_buckets = 0;
static uint64_t cache_max_item_age = 1;

static void cache_init(int64_t num_buckets);
static void cache_fini(void);
static int cache_is_cached(ram_addr_t addr);
static int cache_get_oldest(cache_bucket_t *buck);
static int cache_get_newest(cache_bucket_t *buck, ram_addr_t addr);
static void cache_insert(ram_addr_t id, uint8_t *pdata);
static unsigned long cache_get_cache_pos(ram_addr_t address);
static cache_item_t *cache_item_get(unsigned long pos, int item);

/***********************************************************/
/* XBRLE (Xor Based Run-Length Encoding) */
typedef struct xbrle_hdr_t {
    uint8_t xb_compress;
    uint16_t xb_len;
#ifdef DEBUG_ARCH_INIT_CKSUM
    uint32_t xb_cksum;
#endif
} xbrle_hdr_t;

static int rle_encode(uint8_t *src, int slen, uint8_t *dst, int dlen);
static int rle_decode(uint8_t *src, int slen, uint8_t *dst, int dlen);
#ifdef DEBUG_ARCH_INIT_CKSUM
static uint32_t page_cksum(uint8_t* buf);
static void page_log(ram_addr_t addr, uint8_t *pdata, const char *fmt, ...);
#endif

static uint8_t *save_xor_buf, *save_xbrle_buf;

static void save_xbrle_alloc(void)
{
    save_xor_buf = (uint8_t*) qemu_mallocz(TARGET_PAGE_SIZE);
    save_xbrle_buf = (uint8_t*) qemu_mallocz(TARGET_PAGE_SIZE);
}

static void save_xbrle_free(void)
{
    qemu_free(save_xor_buf);
    qemu_free(save_xbrle_buf);
}

static uint8_t *load_xor_buf, *load_xbrle_buf;

static void load_xbrle_alloc(void)
{
    load_xor_buf = (uint8_t*) qemu_mallocz(TARGET_PAGE_SIZE);
    load_xbrle_buf = (uint8_t*) qemu_mallocz(TARGET_PAGE_SIZE);
}

static void load_xbrle_free(void)
{
    qemu_free(load_xor_buf);
    qemu_free(load_xbrle_buf);
}

/***********************************************************/
/* benchmarking */
typedef struct bench_t {
    uint64_t normal_pages;
    uint64_t xbrle_pages;
    uint64_t xbrle_pages_aborted;
    uint64_t dup_pages;
    uint64_t iterations;
    uint64_t xbrle_bytes;
} bench_t;

static bench_t bench;

/***********************************************************/
/* XBRLE page cache implementation */
cache_item_t *cache_item_get(unsigned long pos, int item)
{
    assert(page_cache);
    return &page_cache[pos].bkt_item[item];
}

void cache_init(int64_t size)
{
    int i;

    cache_num_buckets = size / (TARGET_PAGE_SIZE * CACHE_N_WAY);
    assert(cache_num_buckets);
    dprintf("Setting cache buckets to %ld\n", cache_num_buckets);

    assert(!page_cache);
    page_cache = (cache_bucket_t*)qemu_mallocz((cache_num_buckets) * 
            sizeof(cache_bucket_t));

    for (i=0;i<cache_num_buckets;i++) {
        int j;
        for (j = 0; j < CACHE_N_WAY; j++) {
            cache_item_t *it = cache_item_get(i, j);
            it->it_data = NULL;
            it->it_age = 0;
            it->it_addr = -1;
        }
    }

    /* reset cache_max_item_age */
    cache_max_item_age = 1;
}

void cache_fini(void)
{
    int i;

    assert(page_cache);

    for (i=0;i<cache_num_buckets;i++) {
        int j;
        for (j = 0; j < CACHE_N_WAY; j++) {
            cache_item_t *it = cache_item_get(i, j);
            qemu_free(it->it_data);
            it->it_data = 0;
        }
    }

    qemu_free(page_cache);
    page_cache = NULL;
}

unsigned long cache_get_cache_pos(ram_addr_t address)
{
    unsigned long pos;

    assert(cache_num_buckets);
    pos = (address/TARGET_PAGE_SIZE) & (cache_num_buckets - 1);
    return pos;
}

int cache_get_newest(cache_bucket_t *buck, ram_addr_t addr)
{
    unsigned long big = 0;
    int big_pos = -1;
    int j;

    assert(page_cache);

    for (j = 0; j < CACHE_N_WAY; j++) {
        cache_item_t *it = &buck->bkt_item[j];

        if (it->it_addr != addr)
            continue;

        if (!j || it->it_age > big) {
            big = it->it_age;
            big_pos = j;
        }
    }

    return big_pos;
}

int cache_get_oldest(cache_bucket_t *buck)
{
    unsigned long small = 0;
    int small_pos = -1;
    int j;

    assert(page_cache);

    for (j = 0; j < CACHE_N_WAY; j++) {
        cache_item_t *it = &buck->bkt_item[j];

        if (!j || it->it_age <  small) {
            small = it->it_age;
            small_pos = j;
        }
    }

    return small_pos;
}

int cache_is_cached(ram_addr_t addr) 
{
    unsigned long pos = cache_get_cache_pos(addr);

    assert(page_cache);
    cache_bucket_t *bucket = &page_cache[pos];
    return cache_get_newest(bucket, addr);
}

void cache_insert(unsigned long addr, uint8_t *pdata)
{
    unsigned long pos;
    int slot = -1;
    cache_bucket_t *bucket;

    pos = cache_get_cache_pos(addr);
    assert(page_cache);
    bucket = &page_cache[pos];
    slot = cache_get_oldest(bucket); /* evict LRU */

    /* actual update of entry */
    cache_item_t *it = cache_item_get(pos, slot);
    qemu_free(it->it_data);
    it->it_data = pdata;
    it->it_age = cache_max_item_age++;
    it->it_addr = addr;
}

/* XBRLE (Xor Based Run-Length Encoding) */
int rle_encode(uint8_t *src, int slen, uint8_t *dst, int dlen)
{
    int d = 0, ch_run = 0, i;
    uint8_t prev, ch;

    for (i = 0; i <= slen; i++) {
        if (i != slen)
            ch = src[i];

        if (!i || (i != slen && ch == prev && ch_run < 255)) {
            ch_run++;
        } else {
            if (d+2 > dlen)
                return -1;
            *dst++ = ch_run;
            *dst++ = prev;
            d += 2;
            ch_run = 1;
        }

        prev = ch;
    }
    return d;
}

int rle_decode(uint8_t *src, int slen, uint8_t *dst, int dlen)
{
    int d = 0, s;

    for (s = 0; s < slen-1; s += 2) {
        uint8_t ch_run = src[s];
        uint8_t ch = src[s+1];
        while (ch_run--) {
            if (d == dlen)
                return -1;
            dst[d] = ch;
            d++;
        }
    }
    return d;
}

#define PAGE_SAMPLE_PERCENT 0.01
#define PAGE_SAMPLE_SIZE (TARGET_PAGE_SIZE * PAGE_SAMPLE_PERCENT)
#define BYTES_CHANGED_PERCENT 0.30

static int is_page_good_for_xbrle(uint8_t *old, uint8_t *new)
{
    int i, bytes_changed = 0;

    srand(time(NULL)+getpid()+getpid()*987654+rand());

    for (i = 0; i < PAGE_SAMPLE_SIZE; i++) {
        unsigned long pos = (int) (rand() * TARGET_PAGE_SIZE / (RAND_MAX+1.0));

         if (old[pos] != new[pos])
             bytes_changed++;
    }

    return (((float) bytes_changed) / PAGE_SAMPLE_SIZE) < BYTES_CHANGED_PERCENT;
}

static void xor_encode(uint8_t *dst, uint8_t *src1, uint8_t *src2)
{
    int i;

    for (i = 0; i < TARGET_PAGE_SIZE; i++)
        dst[i] = src1[i] ^ src2[i];
}

static void save_block_hdr(QEMUFile *f, 
        RAMBlock *block, ram_addr_t offset, int cont, int flag)
{
        qemu_put_be64(f, offset | cont | flag);
        if (!cont) {
                qemu_put_byte(f, strlen(block->idstr));
                qemu_put_buffer(f, (uint8_t *)block->idstr,
                                strlen(block->idstr));
        }
}

#define COMP_TYPE_NONE 0x0
#define COMP_TYPE_XBRLE 0x1

static int save_xbrle_page(QEMUFile *f, uint8_t *current_data, 
        ram_addr_t current_addr,
        RAMBlock *block, ram_addr_t offset, int cont)
{
    int cache_location = -1, slot = -1, encoded_len = 0;
    xbrle_hdr_t hdr = {0};
    cache_item_t *it;
    int bytes_sent;

    /* get location */
    if ((slot = cache_is_cached(current_addr)) == -1) {
        goto failed;
    }
    cache_location = cache_get_cache_pos(current_addr);

    /* abort if page changed too much */
    it = cache_item_get(cache_location, slot);
    if (!is_page_good_for_xbrle(it->it_data, current_data)) {
        dprintf("Page changed too much! Aborting XBRLE.\n");
        bench.xbrle_pages_aborted++;
        goto failed;
    }

    /* XBRLE (XOR+RLE) delta encoding */
    xor_encode(save_xor_buf, it->it_data, current_data);
    encoded_len = rle_encode(save_xor_buf, TARGET_PAGE_SIZE, save_xbrle_buf,
            TARGET_PAGE_SIZE);
    
    if (encoded_len < 0) {
        dprintf("XBRLE encoding oeverflow - sending uncompressed\n");
        goto failed;
    }

    hdr.xb_compress = COMP_TYPE_XBRLE;
    hdr.xb_len = encoded_len;
#ifdef DEBUG_ARCH_INIT_CKSUM
    hdr.xb_cksum = page_cksum(current_data);
#endif

    /* Send RLE compressed page */
    save_block_hdr(f, block, offset, cont, RAM_SAVE_FLAG_XBRLE);
    qemu_put_buffer(f, (uint8_t *) &hdr, sizeof (hdr));
    qemu_put_buffer(f, save_xbrle_buf, encoded_len);
    PAGE_LOG(current_addr, current_data, 
            "XBRLE page (enc len %d)\n", encoded_len);
    bench.xbrle_pages++;
    bytes_sent = encoded_len + sizeof (hdr);
    bench.xbrle_bytes += bytes_sent;
    return bytes_sent;

failed:
    return 0;
}

#ifdef DEBUG_ARCH_INIT_CKSUM
static uint32_t page_cksum(uint8_t* buf)
{
    uint32_t res = 0;
    int i;

    for (i = 0; i < TARGET_PAGE_SIZE; i++)
        res += buf[i];

    return res;
}

static void page_log(ram_addr_t addr, uint8_t *pdata, const char *fmt, ...)
{
    va_list arg_ptr;
    static FILE *fp;
    static uint32_t page_seq;

    va_start(arg_ptr, fmt);
    if (!fp)
        fp = fopen("mig.log", "w");
    page_seq++;
    fprintf(fp, "[seq %d addr 0x%lX cksum 0x%X] ", page_seq,
            (unsigned long) addr, page_cksum(pdata));
    vfprintf(fp, fmt, arg_ptr);
    va_end(arg_ptr);
}
#endif /* DEBUG_ARCH_INIT_CKSUM */

static int is_dup_page(uint8_t *page, uint8_t ch)
{
    uint32_t val = ch << 24 | ch << 16 | ch << 8 | ch;
    uint32_t *array = (uint32_t *)page;
    int i;

    for (i = 0; i < (TARGET_PAGE_SIZE / 4); i++) {
        if (array[i] != val) {
            return 0;
        }
    }

    return 1;
}

static RAMBlock *last_block;
static ram_addr_t last_offset;

static int ram_save_block(QEMUFile *f, int stage)
{
    RAMBlock *block = last_block;
    ram_addr_t offset = last_offset;
    ram_addr_t current_addr;
    int bytes_sent = 0;

    if (!block)
        block = QLIST_FIRST(&ram_list.blocks);

    current_addr = block->offset + offset;

    do {
        if (cpu_physical_memory_get_dirty(current_addr, MIGRATION_DIRTY_FLAG)) {
            uint8_t *p;
            int cont = (block == last_block) ? RAM_SAVE_FLAG_CONTINUE : 0;

            cpu_physical_memory_reset_dirty(current_addr,
                                            current_addr + TARGET_PAGE_SIZE,
                                            MIGRATION_DIRTY_FLAG);

            p = qemu_mallocz(TARGET_PAGE_SIZE);
            memcpy(p, block->host + offset, TARGET_PAGE_SIZE);

            if (is_dup_page(p, *p)) {
                save_block_hdr(f, block, offset, cont, RAM_SAVE_FLAG_COMPRESS);
                qemu_put_byte(f, *p);
                bytes_sent = 1;
                bench.dup_pages++;
                PAGE_LOG(current_addr, p, "DUP page\n");
            } else if (stage == 2 && is_migrate_xbrle && 
                (bytes_sent = save_xbrle_page(f, p, current_addr, block,
                        offset, cont))) {
                    /* if success - page was handled - do nothing */
            } else {
                save_block_hdr(f, block, offset, cont, RAM_SAVE_FLAG_PAGE);
                qemu_put_buffer(f, p, TARGET_PAGE_SIZE);
                bytes_sent = TARGET_PAGE_SIZE;
                bench.normal_pages++;
                PAGE_LOG(current_addr, p, "NORMAL page\n");
            }

            if (is_migrate_xbrle)
                cache_insert(current_addr, p);
            break;
        }

        offset += TARGET_PAGE_SIZE;
        if (offset >= block->length) {
            offset = 0;
            block = QLIST_NEXT(block, next);
            if (!block)
                block = QLIST_FIRST(&ram_list.blocks);
        }

        current_addr = block->offset + offset;

    } while (current_addr != last_block->offset + last_offset);

    last_block = block;
    last_offset = offset;

    return bytes_sent;
}

static uint64_t bytes_transferred;

static ram_addr_t ram_save_remaining(void)
{
    RAMBlock *block;
    ram_addr_t count = 0;

    QLIST_FOREACH(block, &ram_list.blocks, next) {
        ram_addr_t addr;
        for (addr = block->offset; addr < block->offset + block->length;
             addr += TARGET_PAGE_SIZE) {
            if (cpu_physical_memory_get_dirty(addr, MIGRATION_DIRTY_FLAG)) {
                count++;
            }
        }
    }

    return count;
}

uint64_t ram_bytes_remaining(void)
{
    return ram_save_remaining() * TARGET_PAGE_SIZE;
}

uint64_t ram_bytes_transferred(void)
{
    return bytes_transferred;
}

uint64_t ram_bytes_total(void)
{
    RAMBlock *block;
    uint64_t total = 0;

    QLIST_FOREACH(block, &ram_list.blocks, next)
        total += block->length;

    return total;
}

#ifdef DEBUG_ARCH_INIT_CKSUM
static void dump_percentage(const char *label, unsigned long absolute, 
        unsigned long total )
{
    printf("%s: %ld (%0.2f%%)\n", label, absolute, 
            (100.0 * absolute / total));
}

static void dump_migration_statistics(void) 
{
    unsigned long normal_bytes = bench.normal_pages * TARGET_PAGE_SIZE;
    unsigned long total_pages = bench.normal_pages + bench.xbrle_pages 
        + bench.dup_pages;
    unsigned long total_bytes = normal_bytes + bench.xbrle_bytes
        + bench.dup_pages;

    printf("\n");
    printf("=====================================================\n");
    printf("Save VM Memory Statistics (SUCCESS or FAILURE):\n");
    printf("Iterations: %ld\n", bench.iterations);

    dump_percentage("Normal pages", bench.normal_pages, total_pages);
    dump_percentage("Normal bytes", normal_bytes, total_bytes);

    dump_percentage("Dup pages", bench.dup_pages, total_pages);
    dump_percentage("Dup bytes", bench.dup_pages, total_bytes);

    if (is_migrate_xbrle) {
        dump_percentage("XBRLE pages", bench.xbrle_pages, total_pages);
        dump_percentage("XBRLE bytes", bench.xbrle_bytes, total_bytes);
        dump_percentage("Aborted XBRLE pages from XBRLE", 
            bench.xbrle_pages_aborted, 
            bench.xbrle_pages + bench.xbrle_pages_aborted);
    }

    dump_percentage("Total pages", total_pages, total_pages);
    dump_percentage("Total bytes", total_bytes, total_bytes);
    
    if (is_migrate_xbrle)
        printf("Cache age max value: %ld\n", cache_max_item_age);

    printf("=====================================================\n");
}

static void dump_page_log(FILE *fp, ram_addr_t addr, void *p)
{
    uint32_t cs = page_cksum(p);
    if (cs)
        fprintf(fp, "addr 0x%lX cksum 0x%X\n", (unsigned long) addr, cs);
}

static void dump_page_img(FILE *fp, ram_addr_t addr, void *p)
{
    fwrite(p, TARGET_PAGE_SIZE, 1, fp);
}

static void dump_ram_template(const char *name, const char *mode, 
    void (*page_cb)(FILE *, ram_addr_t, void *))
{
    FILE *fp = NULL;
    RAMBlock *block, *next_block;

    dprintf("Starting dump of %s ... please wait\n", name);
    if (!(fp = fopen(name, mode))) {
        dprintf("Can't open memory dump file\n");
        return;
    }

    QLIST_FOREACH_SAFE(block, &ram_list.blocks, next, next_block) {
        ram_addr_t addr;

        dprintf("Starting block dump idstr=%s block=%p offset=%ld"
            " length=%ld\n", block->idstr, (void *) block, block->offset, 
            block->length);
        for (addr = block->offset; addr < block->offset + block->length;
             addr += TARGET_PAGE_SIZE) {

            uint8_t *p = qemu_get_ram_ptr(addr);
            (*page_cb)(fp, addr, p);
        }
    }

    fclose(fp);
    dprintf("Complete dump\n");
}
#endif /* DEBUG_ARCH_INIT_CKSUM */

static int should_dump_ram = 0;

void dump_ram(void)
{
#ifdef DEBUG_ARCH_INIT_CKSUM
    if (!should_dump_ram)
        return;
    should_dump_ram = 0;

    dump_ram_template("ram.log", "w", dump_page_log);
    dump_ram_template("ram.img", "wb", dump_page_img);
#endif
}

static void ram_save_xbrle_pre(void)
{
    int64_t size = migrate_cache_size ? migrate_cache_size : 
        DEFAULT_CACHE_SIZE;

    cache_init(size);
    save_xbrle_alloc();
}

static void ram_save_xbrle_post(void)
{
    cache_fini();
    save_xbrle_free();
#ifdef DEBUG_ARCH_INIT_CKSUM
    dump_migration_statistics();
#endif
    should_dump_ram = 1;
    dump_ram();
}

int ram_save_live(Monitor *mon, QEMUFile *f, int stage, void *opaque)
{
    ram_addr_t addr;
    uint64_t bytes_transferred_last;
    double bwidth = 0;
    uint64_t expected_time = 0;

    if (stage < 0) {
        cpu_physical_memory_set_dirty_tracking(0);
        return 0;
    }

    if (cpu_physical_sync_dirty_bitmap(0, TARGET_PHYS_ADDR_MAX) != 0) {
        qemu_file_set_error(f);
        return 0;
    }

    if (stage == 1) {
        RAMBlock *block;
        bytes_transferred = 0;
        last_block = NULL;
        last_offset = 0;

        if (is_migrate_xbrle)
            ram_save_xbrle_pre();

        /* Make sure all dirty bits are set */
        QLIST_FOREACH(block, &ram_list.blocks, next) {
            for (addr = block->offset; addr < block->offset + block->length;
                 addr += TARGET_PAGE_SIZE) {
                if (!cpu_physical_memory_get_dirty(addr,
                                                   MIGRATION_DIRTY_FLAG)) {
                    cpu_physical_memory_set_dirty(addr);
                }
            }
        }

        /* Enable dirty memory tracking */
        cpu_physical_memory_set_dirty_tracking(1);

        qemu_put_be64(f, ram_bytes_total() | RAM_SAVE_FLAG_MEM_SIZE);

        QLIST_FOREACH(block, &ram_list.blocks, next) {
            qemu_put_byte(f, strlen(block->idstr));
            qemu_put_buffer(f, (uint8_t *)block->idstr, strlen(block->idstr));
            qemu_put_be64(f, block->length);
        }
    }

    bytes_transferred_last = bytes_transferred;
    bwidth = qemu_get_clock_ns(rt_clock);

    while (!qemu_file_rate_limit(f)) {
        int bytes_sent;

        bytes_sent = ram_save_block(f, stage);
        bytes_transferred += bytes_sent;
        bench.iterations++;
        if (bytes_sent == 0) { /* no more blocks */
            break;
        }
    }

    bwidth = qemu_get_clock_ns(rt_clock) - bwidth;
    bwidth = (bytes_transferred - bytes_transferred_last) / bwidth;

    /* if we haven't transferred anything this round, force expected_time to a
     * a very high value, but without crashing */
    if (bwidth == 0) {
        bwidth = 0.000001;
    }

    /* try transferring iterative blocks of memory */
    if (stage == 3) {
        int bytes_sent;

        /* flush all remaining blocks regardless of rate limiting */
        while ((bytes_sent = ram_save_block(f, stage)) != 0) {
            bytes_transferred += bytes_sent;
        }
        cpu_physical_memory_set_dirty_tracking(0);
        if (is_migrate_xbrle)
            ram_save_xbrle_post();
    }

    qemu_put_be64(f, RAM_SAVE_FLAG_EOS);

    expected_time = ram_save_remaining() * TARGET_PAGE_SIZE / bwidth;

    dprintf("ram_save_live: expected(%ld) <= max(%ld)?\n", expected_time, 
        migrate_max_downtime());

    return (stage == 2) && (expected_time <= migrate_max_downtime());
}

static int load_xbrle(QEMUFile *f, ram_addr_t addr, void *host)
{
    int ret;
    uint8_t *old_page;
    xbrle_hdr_t hdr = {0};

    /* extract RLE header */
    qemu_get_buffer(f, (uint8_t *) &hdr, sizeof(hdr));
    if (! hdr.xb_compress & COMP_TYPE_XBRLE) {
        fprintf(stderr, "Failed to load XBRLE page - wrong compression!\n");
        return -1;
    }

    if (! hdr.xb_len > TARGET_PAGE_SIZE) {
        fprintf(stderr, "Failed to load XBRLE page - len overflow!\n");
        return -1;
    }

    /* load data and decode */
    qemu_get_buffer(f, load_xbrle_buf, hdr.xb_len);

    /* decode RLE */
    ret = rle_decode(load_xbrle_buf, hdr.xb_len, load_xor_buf,
        TARGET_PAGE_SIZE);
    if (ret == -1) {
        fprintf(stderr, "Failed to load XBRLE page - decode error!\n");
        return -1;
    }

    if (ret != TARGET_PAGE_SIZE) {
        fprintf(stderr, "Failed to load XBRLE page - size %d expected %d!\n",
            ret, TARGET_PAGE_SIZE);
        return -1;
    }

    /* decode XOR delta */
    old_page = host;
    xor_encode(old_page, old_page, load_xor_buf);
#ifdef DEBUG_ARCH_INIT_CKSUM
    if (hdr.xb_cksum != page_cksum(old_page)) {
        fprintf(stderr, "Failed to load XBRLE page - bad checksum!\n");
        return -1;
    }
#endif

    PAGE_LOG(addr, old_page, "XBRLE page (enc len %d)\n", hdr.xb_len);
    return 0;
}

static inline void *host_from_stream_offset(QEMUFile *f,
                                            ram_addr_t offset,
                                            int flags)
{
    static RAMBlock *block = NULL;
    char id[256];
    uint8_t len;

    if (flags & RAM_SAVE_FLAG_CONTINUE) {
        if (!block) {
            fprintf(stderr, "Ack, bad migration stream!\n");
            return NULL;
        }

        return block->host + offset;
    }

    len = qemu_get_byte(f);
    qemu_get_buffer(f, (uint8_t *)id, len);
    id[len] = 0;

    QLIST_FOREACH(block, &ram_list.blocks, next) {
        if (!strncmp(id, block->idstr, sizeof(id)))
            return block->host + offset;
    }

    fprintf(stderr, "Can't find block %s!\n", id);
    return NULL;
}

static inline void *host_from_stream_offset_versioned(int version_id,
        QEMUFile *f, ram_addr_t offset, int flags)
{
        void *host;
        if (version_id == 3)
                host = qemu_get_ram_ptr(offset);
        else
                host = host_from_stream_offset(f, offset, flags);
        return host;
}
 
int ram_load(QEMUFile *f, void *opaque, int version_id)
{
    ram_addr_t addr;
    int flags, ret = 0;
    static int num_iter = 0;

    num_iter++;
    load_xbrle_alloc();

    if (version_id < 3 || version_id > 4) {
        ret = -EINVAL;
        goto done;
    }

    do {
        void *host; 
        addr = qemu_get_be64(f);

        flags = addr & ~TARGET_PAGE_MASK;
        addr &= TARGET_PAGE_MASK;

        if (flags & RAM_SAVE_FLAG_MEM_SIZE) {
            if (version_id == 3) {
                if (addr != ram_bytes_total()) {
                    ret = -EINVAL;
                    goto done;
                }
            } else {
                /* Synchronize RAM block list */
                char id[256];
                ram_addr_t length;
                ram_addr_t total_ram_bytes = addr;

                while (total_ram_bytes) {
                    RAMBlock *block;
                    uint8_t len;

                    len = qemu_get_byte(f);
                    qemu_get_buffer(f, (uint8_t *)id, len);
                    id[len] = 0;
                    length = qemu_get_be64(f);

                    QLIST_FOREACH(block, &ram_list.blocks, next) {
                        if (!strncmp(id, block->idstr, sizeof(id))) {
                            if (block->length != length) {
                                ret = -EINVAL;
                                goto done;
                            }
                            break;
                        }
                    }

                    if (!block) {
                        fprintf(stderr, "Unknown ramblock \"%s\", cannot "
                                "accept migration\n", id);
                        ret = -EINVAL;
                        goto done;
                    }

                    total_ram_bytes -= length;
                }
            }
        }

        if (flags & RAM_SAVE_FLAG_COMPRESS) {
            uint8_t ch;

            host = host_from_stream_offset_versioned(version_id,
                            f, addr, flags);
            assert(host);
            ch = qemu_get_byte(f);
            memset(host, ch, TARGET_PAGE_SIZE);
#ifndef _WIN32
            if (ch == 0 &&
                (!kvm_enabled() || kvm_has_sync_mmu())) {
                madvise(host, TARGET_PAGE_SIZE, MADV_DONTNEED);
            }
#endif
            PAGE_LOG(addr, host, "DUP page\n");
        } else if (flags & RAM_SAVE_FLAG_PAGE) {
            host = host_from_stream_offset_versioned(version_id,
                            f, addr, flags);
            assert(host);
            qemu_get_buffer(f, host, TARGET_PAGE_SIZE);
            PAGE_LOG(addr, host, "NORMAL page\n");
        } else if (flags & RAM_SAVE_FLAG_XBRLE) {
            host = host_from_stream_offset_versioned(version_id,
                            f, addr, flags);
            assert(host);
            if (load_xbrle(f, addr, host) < 0) {
                ret = -EINVAL;
                goto done;
            }
        }

        if (qemu_file_has_error(f)) {
            ret = -EIO;
            goto done;
        }
    } while (!(flags & RAM_SAVE_FLAG_EOS));

done:
    dprintf("Completed load of VM with exit code %d num iterations %d\n",
            ret, num_iter);
    load_xbrle_free();
    should_dump_ram = 1;
    return ret;
}

void qemu_service_io(void)
{
    qemu_notify_event();
}

#ifdef HAS_AUDIO
struct soundhw soundhw[] = {
#ifdef HAS_AUDIO_CHOICE
#if defined(TARGET_I386) || defined(TARGET_MIPS)
    {
        "pcspk",
        "PC speaker",
        0,
        1,
        { .init_isa = pcspk_audio_init }
    },
#endif

#ifdef CONFIG_SB16
    {
        "sb16",
        "Creative Sound Blaster 16",
        0,
        1,
        { .init_isa = SB16_init }
    },
#endif

#ifdef CONFIG_CS4231A
    {
        "cs4231a",
        "CS4231A",
        0,
        1,
        { .init_isa = cs4231a_init }
    },
#endif

#ifdef CONFIG_ADLIB
    {
        "adlib",
#ifdef HAS_YMF262
        "Yamaha YMF262 (OPL3)",
#else
        "Yamaha YM3812 (OPL2)",
#endif
        0,
        1,
        { .init_isa = Adlib_init }
    },
#endif

#ifdef CONFIG_GUS
    {
        "gus",
        "Gravis Ultrasound GF1",
        0,
        1,
        { .init_isa = GUS_init }
    },
#endif

#ifdef CONFIG_AC97
    {
        "ac97",
        "Intel 82801AA AC97 Audio",
        0,
        0,
        { .init_pci = ac97_init }
    },
#endif

#ifdef CONFIG_ES1370
    {
        "es1370",
        "ENSONIQ AudioPCI ES1370",
        0,
        0,
        { .init_pci = es1370_init }
    },
#endif

#endif /* HAS_AUDIO_CHOICE */

    { NULL, NULL, 0, 0, { NULL } }
};

void select_soundhw(const char *optarg)
{
    struct soundhw *c;

    if (*optarg == '?') {
    show_valid_cards:

        printf("Valid sound card names (comma separated):\n");
        for (c = soundhw; c->name; ++c) {
            printf ("%-11s %s\n", c->name, c->descr);
        }
        printf("\n-soundhw all will enable all of the above\n");
        exit(*optarg != '?');
    }
    else {
        size_t l;
        const char *p;
        char *e;
        int bad_card = 0;

        if (!strcmp(optarg, "all")) {
            for (c = soundhw; c->name; ++c) {
                c->enabled = 1;
            }
            return;
        }

        p = optarg;
        while (*p) {
            e = strchr(p, ',');
            l = !e ? strlen(p) : (size_t) (e - p);

            for (c = soundhw; c->name; ++c) {
                if (!strncmp(c->name, p, l) && !c->name[l]) {
                    c->enabled = 1;
                    break;
                }
            }

            if (!c->name) {
                if (l > 80) {
                    fprintf(stderr,
                            "Unknown sound card name (too big to show)\n");
                }
                else {
                    fprintf(stderr, "Unknown sound card name `%.*s'\n",
                            (int) l, p);
                }
                bad_card = 1;
            }
            p += l + (e != NULL);
        }

        if (bad_card) {
            goto show_valid_cards;
        }
    }
}
#else
void select_soundhw(const char *optarg)
{
}
#endif

int qemu_uuid_parse(const char *str, uint8_t *uuid)
{
    int ret;

    if (strlen(str) != 36) {
        return -1;
    }

    ret = sscanf(str, UUID_FMT, &uuid[0], &uuid[1], &uuid[2], &uuid[3],
                 &uuid[4], &uuid[5], &uuid[6], &uuid[7], &uuid[8], &uuid[9],
                 &uuid[10], &uuid[11], &uuid[12], &uuid[13], &uuid[14],
                 &uuid[15]);

    if (ret != 16) {
        return -1;
    }
#ifdef TARGET_I386
    smbios_add_field(1, offsetof(struct smbios_type_1, uuid), 16, uuid);
#endif
    return 0;
}

void do_acpitable_option(const char *optarg)
{
#ifdef TARGET_I386
    if (acpi_table_add(optarg) < 0) {
        fprintf(stderr, "Wrong acpi table provided\n");
        exit(1);
    }
#endif
}

void do_smbios_option(const char *optarg)
{
#ifdef TARGET_I386
    if (smbios_entry_add(optarg) < 0) {
        fprintf(stderr, "Wrong smbios provided\n");
        exit(1);
    }
#endif
}

void cpudef_init(void)
{
#if defined(cpudef_setup)
    cpudef_setup(); /* parse cpu definitions in target config file */
#endif
}

int audio_available(void)
{
#ifdef HAS_AUDIO
    return 1;
#else
    return 0;
#endif
}

int kvm_available(void)
{
#ifdef CONFIG_KVM
    return 1;
#else
    return 0;
#endif
}

int xen_available(void)
{
#ifdef CONFIG_XEN
    return 1;
#else
    return 0;
#endif
}
