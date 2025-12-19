/**
 * @file   tm.c
 * @author [...]
 *
 * @section LICENSE
 *
 * [...]
 *
 * @section DESCRIPTION
 *
 * Implementation of your own transaction manager.
 * You can completely rewrite this file (and create more files) as you wish.
 * Only the interface (i.e. exported symbols and semantic) must be preserved.
**/

// Requested features
#define _GNU_SOURCE
#define _POSIX_C_SOURCE   200809L
#ifdef __STDC_NO_ATOMICS__
    #error Current C11 compiler does not support atomic operations
#endif

// External headers

// Internal headers
#include <tm.h>

#include "macros.h"

// C standard headers
#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// -------------------------------------------------------------------------- //
// Internal data structures

typedef struct {
    void*  addr;
    size_t size;
    void*  buf;
} write_entry_t;

typedef struct {
    void*  addr;
    size_t size;
} alloc_entry_t;

typedef struct {
    size_t idx;
    unsigned int version;
} read_entry_t;

typedef struct {
    // Shared region description
    void*        base;
    size_t       root_size;
    size_t       capacity;
    size_t       align;
    atomic_size_t next_offset;
    atomic_uint  gvc;
    atomic_uint* versions; // per-word version
    atomic_uint* locks;    // per-word lock: 0 free, 1 locked
} shared_region_t;

typedef struct {
    bool      is_ro;
    bool      aborted;
    unsigned  rv; // read version snapshot

    read_entry_t*  reads;
    size_t         read_len;
    size_t         read_cap;

    write_entry_t* writes;
    size_t         write_len;
    size_t         write_cap;

    alloc_entry_t* allocs;
    size_t         alloc_len;
    size_t         alloc_cap;
} tx_ctx_t;

// -------------------------------------------------------------------------- //
// Helpers

static inline shared_region_t* as_shared(shared_t shared) {
    return (shared_region_t*)shared;
}

static inline tx_ctx_t* as_tx(tx_t tx) {
    return (tx_ctx_t*)tx;
}

static bool ensure_read_cap(tx_ctx_t* tx, size_t extra) {
    if (tx->read_len + extra <= tx->read_cap) {
        return true;
    }
    size_t new_cap = tx->read_cap ? tx->read_cap * 2 : 8;
    while (new_cap < tx->read_len + extra) {
        new_cap *= 2;
    }
    read_entry_t* nr = realloc(tx->reads, new_cap * sizeof(*nr));
    if (!nr) return false;
    tx->reads = nr;
    tx->read_cap = new_cap;
    return true;
}

static bool ensure_write_cap(tx_ctx_t* tx, size_t extra) {
    if (tx->write_len + extra <= tx->write_cap) {
        return true;
    }
    size_t new_cap = tx->write_cap ? tx->write_cap * 2 : 4;
    while (new_cap < tx->write_len + extra) {
        new_cap *= 2;
    }
    write_entry_t* nw = realloc(tx->writes, new_cap * sizeof(*nw));
    if (!nw) return false;
    tx->writes = nw;
    tx->write_cap = new_cap;
    return true;
}

static bool ensure_alloc_cap(tx_ctx_t* tx, size_t extra) {
    if (tx->alloc_len + extra <= tx->alloc_cap) {
        return true;
    }
    size_t new_cap = tx->alloc_cap ? tx->alloc_cap * 2 : 2;
    while (new_cap < tx->alloc_len + extra) {
        new_cap *= 2;
    }
    alloc_entry_t* na = realloc(tx->allocs, new_cap * sizeof(*na));
    if (!na) return false;
    tx->allocs = na;
    tx->alloc_cap = new_cap;
    return true;
}

static inline size_t word_index(shared_region_t* sh, void* addr) {
    return ((uintptr_t)addr - (uintptr_t)sh->base) / sh->align;
}

static inline bool addr_aligned(shared_region_t* sh, void const* addr) {
    return ((uintptr_t)addr % sh->align) == 0;
}

static inline bool size_aligned(shared_region_t* sh, size_t size) {
    return size > 0 && (size % sh->align) == 0;
}

// -------------------------------------------------------------------------- //

/** Create (i.e. allocate + init) a new shared memory region, with one first non-free-able allocated segment of the requested size and alignment.
 * @param size  Size of the first shared segment of memory to allocate (in bytes), must be a positive multiple of the alignment
 * @param align Alignment (in bytes, must be a power of 2) that the shared memory region must support
 * @return Opaque shared memory region handle, 'invalid_shared' on failure
**/
shared_t tm_create(size_t unused(size), size_t unused(align)) {
    if (align == 0 || (align & (align - 1)) != 0) {
        return invalid_shared;
    }
    if (size == 0 || (size % align) != 0) {
        return invalid_shared;
    }

    // Capacity: allow some headroom for allocations (x4 of root size)
    size_t capacity = size * 4;
    void* full_buffer = NULL;
#if defined(_POSIX_C_SOURCE) && (_POSIX_C_SOURCE >= 200112L)
    if (posix_memalign(&full_buffer, align, capacity) != 0) {
        full_buffer = NULL;
    }
#else
    full_buffer = aligned_alloc(align, capacity);
#endif
    if (!full_buffer) {
        return invalid_shared;
    }
    memset(full_buffer, 0, capacity);

    // Per-word metadata
    size_t word_count = capacity / align;
    atomic_uint* versions = calloc(word_count, sizeof(*versions));
    atomic_uint* locks    = calloc(word_count, sizeof(*locks));
    if (!versions || !locks) {
        free(versions);
        free(locks);
        free(full_buffer);
        return invalid_shared;
    }

    shared_region_t* sh = calloc(1, sizeof(*sh));
    if (!sh) {
        free(versions);
        free(locks);
        free(full_buffer);
        return invalid_shared;
    }

    sh->base       = full_buffer;
    sh->root_size  = size;
    sh->capacity   = capacity;
    sh->align      = align;
    atomic_init(&sh->next_offset, size);
    atomic_init(&sh->gvc, 0u);
    sh->versions   = versions;
    sh->locks      = locks;

    return (shared_t)sh;
}

/** Destroy (i.e. clean-up + free) a given shared memory region.
 * @param shared Shared memory region to destroy, with no running transaction
**/
void tm_destroy(shared_t unused(shared)) {
    shared_region_t* sh = as_shared(shared);
    if (!sh) return;
    free(sh->versions);
    free(sh->locks);
    free(sh->base);
    free(sh);
}

/** [thread-safe] Return the start address of the first allocated segment in the shared memory region.
 * @param shared Shared memory region to query
 * @return Start address of the first allocated segment
**/
void* tm_start(shared_t unused(shared)) {
    shared_region_t* sh = as_shared(shared);
    if (!sh) return NULL;
    return sh->base;
}

/** [thread-safe] Return the size (in bytes) of the first allocated segment of the shared memory region.
 * @param shared Shared memory region to query
 * @return First allocated segment size
**/
size_t tm_size(shared_t unused(shared)) {
    shared_region_t* sh = as_shared(shared);
    if (!sh) return 0;
    return sh->root_size;
}

/** [thread-safe] Return the alignment (in bytes) of the memory accesses on the given shared memory region.
 * @param shared Shared memory region to query
 * @return Alignment used globally
**/
size_t tm_align(shared_t unused(shared)) {
    shared_region_t* sh = as_shared(shared);
    if (!sh) return 0;
    return sh->align;
}

/** [thread-safe] Begin a new transaction on the given shared memory region.
 * @param shared Shared memory region to start a transaction on
 * @param is_ro  Whether the transaction is read-only
 * @return Opaque transaction ID, 'invalid_tx' on failure
**/
tx_t tm_begin(shared_t unused(shared), bool unused(is_ro)) {
    shared_region_t* sh = as_shared(shared);
    if (!sh) return invalid_tx;

    tx_ctx_t* tx = calloc(1, sizeof(*tx));
    if (!tx) return invalid_tx;

    tx->is_ro   = is_ro;
    tx->aborted = false;
    tx->rv      = atomic_load(&sh->gvc);

    return (tx_t)tx;
}

/** [thread-safe] End the given transaction.
 * @param shared Shared memory region associated with the transaction
 * @param tx     Transaction to end
 * @return Whether the whole transaction committed
**/
bool tm_end(shared_t unused(shared), tx_t unused(tx)) {
    shared_region_t* sh = as_shared(shared);
    tx_ctx_t* ctx       = as_tx(tx);
    if (!sh || !ctx) return false;
    if (ctx->aborted) {
        free(ctx->reads);
        free(ctx->writes);
        for (size_t i = 0; i < ctx->write_len; ++i) {
            free(ctx->writes[i].buf);
        }
        free(ctx->allocs);
        free(ctx);
        return false;
    }

    // Read-only transactions: optional validation
    if (ctx->is_ro) {
        unsigned cur = atomic_load(&sh->gvc);
        if (cur != ctx->rv) {
            // quick check: revalidate read set
            for (size_t i = 0; i < ctx->read_len; ++i) {
                size_t idx = ctx->reads[i].idx;
                unsigned v = atomic_load(&sh->versions[idx]);
                if (atomic_load(&sh->locks[idx]) != 0 || v != ctx->reads[i].version) {
                    ctx->aborted = true;
                    break;
                }
            }
        }
        bool committed = !ctx->aborted;
        free(ctx->reads);
        free(ctx->writes);
        for (size_t i = 0; i < ctx->write_len; ++i) {
            free(ctx->writes[i].buf);
        }
        free(ctx->allocs);
        free(ctx);
        return committed;
    }

    // Build set of unique word indices to lock
    size_t max_words = 0;
    for (size_t i = 0; i < ctx->write_len; ++i) {
        max_words += ctx->writes[i].size / sh->align;
    }
    size_t* lock_indices = max_words ? malloc(max_words * sizeof(size_t)) : NULL;
    size_t lock_count = 0;
    if (max_words && !lock_indices) {
        ctx->aborted = true;
    }
    if (!ctx->aborted) {
        for (size_t i = 0; i < ctx->write_len; ++i) {
            write_entry_t* w = &ctx->writes[i];
            size_t words = w->size / sh->align;
            for (size_t j = 0; j < words; ++j) {
                size_t idx = word_index(sh, (char*)w->addr + j * sh->align);
                lock_indices[lock_count++] = idx;
            }
        }
        // sort indices
        for (size_t i = 0; i + 1 < lock_count; ++i) {
            for (size_t j = i + 1; j < lock_count; ++j) {
                if (lock_indices[j] < lock_indices[i]) {
                    size_t tmp = lock_indices[i];
                    lock_indices[i] = lock_indices[j];
                    lock_indices[j] = tmp;
                } else if (lock_indices[j] == lock_indices[i]) {
                    // remove duplicates by marking
                    lock_indices[j] = SIZE_MAX;
                }
            }
        }
        // compact duplicates
        size_t new_count = 0;
        for (size_t i = 0; i < lock_count; ++i) {
            if (lock_indices[i] != SIZE_MAX) {
                lock_indices[new_count++] = lock_indices[i];
            }
        }
        lock_count = new_count;
    }

    // Acquire locks
    if (!ctx->aborted) {
        for (size_t i = 0; i < lock_count; ++i) {
            size_t idx = lock_indices[i];
            if (atomic_exchange(&sh->locks[idx], 1u) != 0u) {
                ctx->aborted = true;
                // release acquired
                for (size_t j = 0; j < i; ++j) {
                    atomic_store(&sh->locks[lock_indices[j]], 0u);
                }
                break;
            }
        }
    }

    // Validate read set
    if (!ctx->aborted) {
        for (size_t i = 0; i < ctx->read_len; ++i) {
            size_t idx = ctx->reads[i].idx;
            if (atomic_load(&sh->locks[idx]) != 0u) {
                ctx->aborted = true;
                break;
            }
            unsigned v = atomic_load(&sh->versions[idx]);
            if (v != ctx->reads[i].version || v > ctx->rv) {
                ctx->aborted = true;
                break;
            }
        }
    }

    bool committed = false;
    if (!ctx->aborted) {
        unsigned wv = atomic_fetch_add(&sh->gvc, 1u) + 1u;
        // Apply writes
        for (size_t i = 0; i < ctx->write_len; ++i) {
            write_entry_t* w = &ctx->writes[i];
            memcpy(w->addr, w->buf, w->size);
            size_t words = w->size / sh->align;
            for (size_t j = 0; j < words; ++j) {
                size_t idx = word_index(sh, (char*)w->addr + j * sh->align);
                atomic_store(&sh->versions[idx], wv);
            }
        }
        // Apply allocs (versions to wv)
        for (size_t i = 0; i < ctx->alloc_len; ++i) {
            alloc_entry_t* a = &ctx->allocs[i];
            size_t words = a->size / sh->align;
            for (size_t j = 0; j < words; ++j) {
                size_t idx = word_index(sh, (char*)a->addr + j * sh->align);
                atomic_store(&sh->versions[idx], wv);
            }
        }
        committed = true;
    }

    // Release locks
    if (lock_indices) {
        for (size_t i = 0; i < lock_count; ++i) {
            atomic_store(&sh->locks[lock_indices[i]], 0u);
        }
        free(lock_indices);
    }

    // Cleanup
    free(ctx->reads);
    for (size_t i = 0; i < ctx->write_len; ++i) {
        free(ctx->writes[i].buf);
    }
    free(ctx->writes);
    free(ctx->allocs);
    free(ctx);

    return committed;
}

/** [thread-safe] Read operation in the given transaction, source in the shared region and target in a private region.
 * @param shared Shared memory region associated with the transaction
 * @param tx     Transaction to use
 * @param source Source start address (in the shared region)
 * @param size   Length to copy (in bytes), must be a positive multiple of the alignment
 * @param target Target start address (in a private region)
 * @return Whether the whole transaction can continue
**/
bool tm_read(shared_t unused(shared), tx_t unused(tx), void const* unused(source), size_t unused(size), void* unused(target)) {
    shared_region_t* sh = as_shared(shared);
    tx_ctx_t* ctx       = as_tx(tx);
    if (!sh || !ctx || !source || !target) return false;
    if (!size_aligned(sh, size) || !addr_aligned(sh, source) || !addr_aligned(sh, target)) {
        ctx->aborted = true;
        return false;
    }
    uintptr_t start = (uintptr_t)source;
    uintptr_t end   = start + size;
    if (end > (uintptr_t)sh->base + sh->capacity) {
        ctx->aborted = true;
        return false;
    }

    size_t words = size / sh->align;
    for (size_t i = 0; i < words; ++i) {
        void* waddr = (void*)(start + i * sh->align);
        // Check if written in this tx
        bool from_write = false;
        for (size_t j = 0; j < ctx->write_len; ++j) {
            write_entry_t* we = &ctx->writes[j];
            uintptr_t wa = (uintptr_t)we->addr;
            uintptr_t wb = wa + we->size;
            if ((uintptr_t)waddr >= wa && (uintptr_t)waddr < wb) {
                size_t offset = (uintptr_t)waddr - wa;
                memcpy((char*)target + i * sh->align, (char*)we->buf + offset, sh->align);
                from_write = true;
                break;
            }
        }
        if (from_write) continue;

        size_t idx = word_index(sh, waddr);
        unsigned v1 = atomic_load(&sh->versions[idx]);
        if (atomic_load(&sh->locks[idx]) != 0u || v1 > ctx->rv) {
            ctx->aborted = true;
            return false;
        }
        memcpy((char*)target + i * sh->align, (char*)waddr, sh->align);
        unsigned v2 = atomic_load(&sh->versions[idx]);
        if (v1 != v2 || atomic_load(&sh->locks[idx]) != 0u) {
            ctx->aborted = true;
            return false;
        }
        if (!ensure_read_cap(ctx, 1)) {
            ctx->aborted = true;
            return false;
        }
        ctx->reads[ctx->read_len++] = (read_entry_t){ .idx = idx, .version = v2 };
    }
    return true;
}

/** [thread-safe] Write operation in the given transaction, source in a private region and target in the shared region.
 * @param shared Shared memory region associated with the transaction
 * @param tx     Transaction to use
 * @param source Source start address (in a private region)
 * @param size   Length to copy (in bytes), must be a positive multiple of the alignment
 * @param target Target start address (in the shared region)
 * @return Whether the whole transaction can continue
**/
bool tm_write(shared_t unused(shared), tx_t unused(tx), void const* unused(source), size_t unused(size), void* unused(target)) {
    shared_region_t* sh = as_shared(shared);
    tx_ctx_t* ctx       = as_tx(tx);
    if (!sh || !ctx || !source || !target) return false;
    if (ctx->is_ro) {
        ctx->aborted = true;
        return false;
    }
    if (!size_aligned(sh, size) || !addr_aligned(sh, source) || !addr_aligned(sh, target)) {
        ctx->aborted = true;
        return false;
    }
    uintptr_t start = (uintptr_t)target;
    uintptr_t end   = start + size;
    if (end > (uintptr_t)sh->base + sh->capacity) {
        ctx->aborted = true;
        return false;
    }

    if (!ensure_write_cap(ctx, 1)) {
        ctx->aborted = true;
        return false;
    }
    void* buf = malloc(size);
    if (!buf) {
        ctx->aborted = true;
        return false;
    }
    memcpy(buf, source, size);
    ctx->writes[ctx->write_len++] = (write_entry_t){
        .addr = (void*)target,
        .size = size,
        .buf  = buf
    };
    return true;
}

/** [thread-safe] Memory allocation in the given transaction.
 * @param shared Shared memory region associated with the transaction
 * @param tx     Transaction to use
 * @param size   Allocation requested size (in bytes), must be a positive multiple of the alignment
 * @param target Pointer in private memory receiving the address of the first byte of the newly allocated, aligned segment
 * @return Whether the whole transaction can continue (success/nomem), or not (abort_alloc)
**/
alloc_t tm_alloc(shared_t unused(shared), tx_t unused(tx), size_t unused(size), void** unused(target)) {
    shared_region_t* sh = as_shared(shared);
    tx_ctx_t* ctx       = as_tx(tx);
    if (!sh || !ctx || !target) return abort_alloc;
    if (ctx->is_ro) {
        ctx->aborted = true;
        return abort_alloc;
    }
    if (!size_aligned(sh, size)) {
        ctx->aborted = true;
        return abort_alloc;
    }
    size_t rounded = size;
    size_t offset = 0;
    while (true) {
        offset = atomic_load(&sh->next_offset);
        if (rounded > sh->capacity - offset) {
            return nomem_alloc;
        }
        if (atomic_compare_exchange_weak(&sh->next_offset, &offset, offset + rounded)) {
            break;
        }
    }
    void* addr = (char*)sh->base + offset;
    memset(addr, 0, rounded);

    if (!ensure_alloc_cap(ctx, 1)) {
        ctx->aborted = true;
        return abort_alloc;
    }
    ctx->allocs[ctx->alloc_len++] = (alloc_entry_t){ .addr = addr, .size = rounded };
    *target = addr;
    if (!*target) {
        ctx->aborted = true;
        return abort_alloc;
    }
    return success_alloc;
}

/** [thread-safe] Memory freeing in the given transaction.
 * @param shared Shared memory region associated with the transaction
 * @param tx     Transaction to use
 * @param target Address of the first byte of the previously allocated segment to deallocate
 * @return Whether the whole transaction can continue
**/
bool tm_free(shared_t unused(shared), tx_t unused(tx), void* unused(target)) {
    // Simplified: not supported; abort on free attempt.
    tx_ctx_t* ctx = as_tx(tx);
    if (ctx) ctx->aborted = true;
    return false;
}
