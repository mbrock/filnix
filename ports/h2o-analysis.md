# H2O Web Server Fil-C Compatibility Analysis

**Date:** November 5, 2025  
**Upstream:** https://github.com/h2o/h2o  
**Status:** ❌ **NOT RECOMMENDED** for Fil-C porting  
**Estimated Effort:** 6-8 weeks (with mruby disabled), **infeasible** (with mruby enabled)

---

## Executive Summary

H2O is **fundamentally incompatible** with Fil-C due to its embedded mruby interpreter, which uses pervasive pointer tagging throughout its value representation system. While H2O's core HTTP server architecture is relatively clean, the mruby integration represents an insurmountable obstacle without a complete rewrite of mruby's memory model.

**Critical Blockers:**

1. ❌ **mruby NaN-boxing** - Stores pointers in 64-bit IEEE floats with tag bits
2. ❌ **mruby function pointer tagging** - Shifts function pointers left by 2 bits, ORs with flags
3. ❌ **Generic pointer storage as `uintptr_t`** - Error reporter and multithread subsystems
4. ⚠️ **Custom memory pools** - Thread-local pools may conflict with Fil-C's heap tracking

**Comparison to Documented Ports:**

- **Worse than:** Python (1551 LOC), Perl (892 LOC), Emacs (588 LOC) - all successfully ported
- **Similar incompatibility level to:** Unported JavaScript engines (V8, JavaScriptCore) - pointer tagging endemic
- **Better core design than:** Expected - event loop architecture is clean

**H2O vs nginx Portability:**

While nginx has not been ported to Fil-C yet, H2O is likely **significantly harder** due to:
- nginx has **no embedded scripting** (configuration is declarative)
- nginx's memory pools are simpler and more isolated
- H2O's mruby integration touches **every request handler**

**Recommendation:** If you need a Fil-C-compatible web server, consider:
1. **lighttpd** - Already ported (see `lighttpd-filc.patch` in this repo)
2. **nginx** - No embedded language, cleaner separation of concerns
3. **Apache httpd** - In upstream fil-c ports/ (see `httpd/` in this repo)

---

## Architecture Analysis

### 1. Threading Model: ✅ Compatible

H2O uses **event-loop-per-worker** architecture, which is ideal for Fil-C:

**Event Loop Structure** (`lib/common/socket/evloop.c.h`):
```c
// Platform-specific event loop
#if defined(__APPLE__) || defined(__FreeBSD__)
    kqueue()  // BSD
#elif defined(__linux__)
    epoll()   // Linux with MSG_ZEROCOPY
#else
    poll()    // Portable fallback
#endif
```

**Worker Model** (`src/main.c`):
- Each worker thread runs independent event loop
- No shared mutable state between workers
- Message passing via explicit queues

**Fil-C Impact:** ✅ No changes needed - event loops preserve thread isolation.

---

### 2. Memory Management: ⚠️ Moderate Risk

#### Per-Request Memory Pools

**Structure** (`include/h2o/memory.h`):
```c
typedef struct st_h2o_mem_pool_t {
    union un_h2o_mem_pool_chunk_t *chunks;  // Slab allocator
    size_t chunk_offset;
    struct st_h2o_mem_pool_shared_ref_t *shared_refs;
    struct st_h2o_mem_pool_direct_t *directs;
} h2o_mem_pool_t;

struct st_h2o_req_t {
    h2o_mem_pool_t pool;  // Per-request allocation arena
};
```

**Comparison to Known Ports:**

| Project | Allocator Strategy | Fil-C Solution | Lines Changed |
|---------|-------------------|----------------|---------------|
| **Emacs** | Custom `zmalloc`, GC | Replaced with `zgc_alloc` | 588 |
| **Python** | pymalloc (chunked) | Disabled debug wrapper, GC-allocate frames | 1551 |
| **Zsh** | zhalloc (custom heap) | Forced `malloc`/`free` | 46 |
| **H2O** | Per-request pools | **Unknown** - needs testing | ? |

**Potential Issues:**

1. **Thread-local pools** (`__thread h2o_mem_recycle_t h2o_mem_pool_allocator`):
   - May confuse Fil-C if pointers escape thread lifetime
   - Pattern: See Python's datastack chunk removal (1551 LOC change)

2. **Shared reference counting** (`h2o_mem_pool_shared_entry_t`):
   ```c
   inline void h2o_mem_addref_shared(void *p) {
       struct st_h2o_mem_pool_shared_entry_t *entry = 
           H2O_STRUCT_FROM_MEMBER(struct st_h2o_mem_pool_shared_entry_t, bytes, p);
       ++entry->refcnt;  // ⚠️ Not atomic - assumes single-threaded access
   }
   ```
   - Uses `H2O_STRUCT_FROM_MEMBER` (offsetof-based) - should be safe
   - Non-atomic refcount OK if never shared cross-thread
   - **Risk:** If refs escape to other workers, undefined behavior

**Porting Strategy:**
- Test with Fil-C's allocator tracking first
- If pools cause issues, disable and use `malloc`/`free` (Zsh approach)
- Estimated effort: **2-3 days** if pools work, **1-2 weeks** if full replacement needed

---

### 3. Pointer Usage: ❌ CRITICAL INCOMPATIBILITIES

#### Issue #1: mruby Pointer Tagging (BLOCKING)

mruby uses **three different boxing schemes**, all incompatible with Fil-C:

##### NaN-Boxing (`deps/mruby/include/mruby/boxing_nan.h`)

**Memory Layout:**
```
object: 01111111 11111100 PPPPPPPP ... PPPPPP00
cptr  : 01111111 11111111 PPPPPPPP ... PPPPPPPP
         ↑                ↑               ↑
       NaN tag        Pointer bits      Type tag
```

**Implementation:**
```c
#define SET_OBJ_VALUE(r,v) do {(r).u = (uint64_t)(uintptr_t)(v);} while (0)
//                                     ^^^^^^^^^^^^^^^^^^^^
//                                     Pointer → integer cast destroys capability

#define SET_CPTR_VALUE(mrb,r,v) NANBOX_SET_VALUE(r, MRB_NANBOX_TT_CPTR, \
    (uint64_t)(uintptr_t)(v) & 0x0000ffffffffffffULL)
//                             ^^^^^^^^^^^^^ Bitmask loses provenance
```

**Retrieval:**
```c
return ((struct RBasic*)(uintptr_t)u)->tt;
//      ^^^^^^^^^^^^^^^^ Integer → pointer cast loses bounds
```

**Comparison to Documented Patterns:**

| Pattern | Fil-C Solution | Found in | H2O Equivalent |
|---------|---------------|----------|----------------|
| **Pointer → integer → pointer** | `zptrtable_encode/decode` | Perl, Python, SQLite | mruby boxing |
| **Low-bit tagging** | `zorptr/zandptr/zretagptr` | dhcpcd, libarchive, Python GC | mruby NaN-box |
| **Function pointer tagging** | None - avoid entirely | - | mruby methods ❌ |

##### Word-Boxing (`deps/mruby/include/mruby/boxing_word.h`)

```c
#define WORDBOX_SET_SHIFT_VALUE(o,n,v) \
  ((o).w = (((uintptr_t)(v)) << WORDBOX_##n##_SHIFT) | WORDBOX_##n##_FLAG)
//         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Shift + OR destroys capability
```

##### Function Pointer Tagging (`deps/mruby/include/mruby/proc.h`)

```c
#define MRB_METHOD_FROM_FUNC(m,fn) \
    ((m)=(mrb_method_t)((((uintptr_t)(fn))<<2)|MRB_METHOD_FUNC_FL))
//                      ^^^^^^^^^^^^^^^^^^^ Function pointer shifted 2 bits left!

#define MRB_METHOD_FUNC(m) ((mrb_func_t)((uintptr_t)(m)>>2))
//                                       ^^^^^^^^^^^^^^^^^ Shift right to recover
```

**Why This is Unfixable:**

1. **Pervasive throughout mruby:**
   - Every object allocation
   - Every method call
   - Every GC traversal
   - Embedded in bytecode constants

2. **No Fil-C pattern matches:**
   - `zptrtable`: Only handles pointer→integer→pointer, not bit manipulation
   - `zorptr/zandptr`: Only preserve tags in **existing** pointers, can't reconstruct from integer
   - Function pointer tagging: **No Fil-C solution exists**

3. **Alternative boxing schemes still break:**
   - Even `boxing_word.h` shifts pointers by type-specific amounts
   - `boxing_no.h` (unboxed) exists but is **not actively maintained**

**Documented Comparable Failure:**

None of the 100+ upstream fil-c ports include:
- Ruby (any version)
- Lua with LuaJIT (which uses NaN-boxing)
- JavaScript engines (V8, SpiderMonkey, JavaScriptCore)
- Lisp implementations with tagged pointers (SBCL, CCL)

The closest successful port is **Lua 5.4.7** (21 LOC), which uses a **union-based** value representation:
```c
// lua.h (compatible with Fil-C)
typedef union {
  Value *gc;         // ✅ Real pointer
  void *p;
  lua_Number n;
  lua_Integer i;
} Value;
```

#### Issue #2: Generic Pointer Storage as uintptr_t

**Error Reporter** (`include/h2o/multithread.h`):
```c
typedef struct st_h2o_error_reporter_t {
    uintptr_t data;  // ❌ Generic pointer stored as integer
} h2o_error_reporter_t;

uintptr_t h2o_error_reporter_record_error(
    h2o_loop_t *loop, h2o_error_reporter_t *reporter,
    uint64_t delay_ticks, uintptr_t new_data);
//                       ^^^^^^^^^ Pointer passed as integer
```

**Fil-C Solution:**

From **git** port (524 LOC):
```diff
-static int opt_callback(const struct option *opt, const char *arg, int unset)
+static int opt_callback_int(const struct option *opt, intptr_t arg_int, int unset)
 {
+    const char *arg = (const char *)arg_int;
```

For H2O:
```diff
 typedef struct st_h2o_error_reporter_t {
-    uintptr_t data;
+    void *data;  // ✅ Store actual pointer
 } h2o_error_reporter_t;

-uintptr_t h2o_error_reporter_record_error(..., uintptr_t new_data);
+void *h2o_error_reporter_record_error(..., void *new_data);
```

**Estimated effort:** 50-100 LOC across 5-10 files (2-3 days)

---

### 4. Atomic Operations: ✅ Compatible

H2O uses atomics **only for integers**, never for pointers:

**Initialization** (`include/h2o/multithread.h`):
```c
#define H2O_MULTITHREAD_ONCE(block)                                     \
    do {                                                                \
        static volatile int lock = 0;  // ✅ Integer atomic
        __atomic_load(&lock, &lock_loaded, __ATOMIC_ACQUIRE);
        // ...
        __atomic_store_n(&lock, 1, __ATOMIC_RELEASE);
    } while (0)
```

**Connection IDs** (`lib/core/context.c`):
```c
#ifdef H2O_NO_64BIT_ATOMICS
    pthread_mutex_lock(&h2o_conn_id_mutex);
    conn->id = ++h2o_connection_id;  // Fallback to mutex
#else
    conn->id = __sync_add_and_fetch(&h2o_connection_id, 1);  // ✅ Integer
#endif
```

**Comparison to Documented Patterns:**

| Pattern | Fil-C Solution | Found in | H2O |
|---------|---------------|----------|-----|
| `atomic_uintptr_t` for pointers | `void*_Atomic` | Python (1551 LOC) | ✅ Not used |
| `__sync_*` intrinsics for ints | No change needed | - | ✅ Compatible |

**Fil-C Impact:** ✅ No changes needed.

---

### 5. FFI Boundaries: ❌ BLOCKING (mruby Integration)

H2O embeds mruby for request handlers, configuration, and filters:

**Integration Depth:**
```c
// include/h2o/mruby_.h
typedef struct st_h2o_mruby_shared_context_t {
    h2o_context_t *ctx;
    mrb_state *mrb;              // mruby VM
    mrb_value constants;         // NaN-boxed values
    // ...
} h2o_mruby_shared_context_t;
```

**Every Handler Can Use mruby:**
```c
// lib/handler/mruby.c
h2o_mruby_generator_t *h2o_mruby_get_generator(mrb_state *mrb, mrb_value obj)
{
    h2o_mruby_generator_t *generator = mrb_data_check_get_ptr(mrb, obj, &generator_type);
    //                                 ^^^^^^^^^^^^^^^^^^^^^ Extracts C pointer from NaN-box
    return generator;
}
```

**Pointers crossing C↔mruby boundary:**
1. Request objects (`h2o_req_t *`)
2. Response generators (`h2o_mruby_generator_t *`)
3. Configuration callbacks
4. Custom filter contexts

**Comparison to Successful FFI Ports:**

| Project | FFI Type | Solution | Lines Changed |
|---------|----------|----------|---------------|
| **Perl** | XS (C↔Perl) | `zptrtable` for `PTR2IV`/`INT2PTR` | 892 |
| **Python** | C API | `zptrtable` for code caches | 1551 |
| **SQLite** | TCL test interface | `zptrtable` encode/decode | 473 |
| **libffi** | Foreign function interface | Custom `zclosure`, `FFI_FILC` ABI | 440 |
| **H2O/mruby** | NaN-boxed values | ❌ **No solution exists** | - |

**Why mruby is Different:**

1. **Perl/Python/SQLite:** Pointer↔integer conversion with table lookup
   - Pattern: `uintptr_t id = zptrtable_encode(table, ptr);`
   - Works because no bit manipulation after encoding

2. **mruby:** Pointer→integer→arithmetic→storage
   - Pattern: `u64 = ((uintptr_t)ptr | TAG) + NAN_OFFSET;`
   - Arithmetic on encoded pointer **destroys table association**

3. **libffi:** Custom calling convention for Fil-C
   - Extensive runtime support added to libffi itself
   - mruby would need **equivalent runtime rewrite**

**Workaround: Disable mruby**

H2O can be built without mruby support:
```bash
cmake -DWITH_MRUBY=OFF
```

This removes:
- Dynamic request handlers
- Embedded configuration logic
- HTTP filter scripting

But retains:
- Core HTTP/1.1 and HTTP/2 server
- Static file serving
- Proxy/FastCGI handlers
- WebSocket support

**Estimated effort (without mruby):** 3-4 weeks  
**Estimated effort (with mruby):** ∞ (requires mruby VM rewrite)

---

### 6. Platform-Specific Code: ⚠️ Moderate Risk

#### SIMD in Picotls (`deps/picotls/lib/fusion.c`)

**AES-NI Crypto:**
```c
#include <immintrin.h>  // AVX/AVX2
#include <wmmintrin.h>  // AES-NI

__m128i bits0, bits1, bits2, bits3;
AESECB6_UPDATE(i);
gfmul_nextstep128(&gstate, _mm_loadu_si128(gdata++), --ghash_precompute);
```

**Pointer Arithmetic for Alignment:**
```c
uintptr_t shift = (uintptr_t)p & 15;  // ❌ Pointer → integer for alignment check
__m128i pattern = _mm_loadu_si128((const __m128i *)(loadn_shuffle + shift));
```

**Comparison to Documented Patterns:**

| Pattern | Fil-C Solution | Found in | picotls Equivalent |
|---------|---------------|----------|-------------------|
| SIMD intrinsics | Usually compatible | zstd, simdutf | ✅ Likely OK |
| Pointer→int for alignment | `zmkptr` | xz, grep, bison | ❌ Need fix |

**From xz port** (174 LOC):
```c
// xz/src/liblzma/check/crc_x86_clmul.h
+#include <stdfil.h>

const __m128i *aligned_buf = (const __m128i *)zmkptr(
    buf, (uintptr_t)buf & ~(uintptr_t)15);
```

**Porting Strategy:**
```diff
-uintptr_t shift = (uintptr_t)p & 15;
+uintptr_t shift = (uintptr_t)p & 15;  // Alignment check - OK
+const char *aligned = (const char *)zmkptr(p, (uintptr_t)p & ~15);
-__m128i pattern = _mm_loadu_si128((const __m128i *)(loadn_shuffle + shift));
+__m128i pattern = _mm_loadu_si128((const __m128i *)zmkptr(loadn_shuffle, 
+                                  (uintptr_t)loadn_shuffle + shift));
```

**Estimated effort:** 1-2 days (10-20 LOC)

#### CPU Feature Detection

**simdutf** port (36 LOC) shows the pattern:
```c
// simdutf uses zxgetbv() for CPUID
+#include <stdfil.h>
+#define _xgetbv(x) zxgetbv(x)
```

H2O's dependencies may need similar fixes for:
- picotls CPU detection
- HTTP/2 HPACK Huffman encoder (potential SIMD paths)

**Estimated effort:** 0.5-1 day

---

### 7. Data Structures: ✅ Compatible

#### Intrusive Linked Lists

**Structure** (`include/h2o/linklist.h`):
```c
typedef struct st_h2o_linklist_t {
    struct st_h2o_linklist_t *next;  // ✅ Real pointers
    struct st_h2o_linklist_t *prev;  // ✅ No tagging
} h2o_linklist_t;
```

**Container Recovery** (`include/h2o/memory.h`):
```c
#define H2O_STRUCT_FROM_MEMBER(s, m, p) \
    ((s *)((char *)(p) - offsetof(s, m)))
```

**Comparison to Problematic Patterns:**

| Project | Structure | Issue | H2O Equivalent |
|---------|-----------|-------|----------------|
| **dhcpcd** | RB-tree | `uintptr_t rb_info` with tag bits | None - uses clean pointers |
| **libarchive** | RB-tree | Same as dhcpcd | None |
| **Python** | GC list | `uintptr_t _gc_prev` with flags | None |

**Fil-C Impact:** ✅ No changes needed - intrusive lists are capability-friendly.

#### HTTP/2 Scheduler

**Weighted fair queue** (`include/h2o/http2_scheduler.h`):
```c
typedef struct st_h2o_http2_scheduler_node_t {
    struct st_h2o_http2_scheduler_node_t *_parent;  // ✅ Clean pointer
    h2o_linklist_t _all_refs;
    h2o_http2_scheduler_queue_t *_queue;
} h2o_http2_scheduler_node_t;
```

No bit manipulation, no integer casts, no tagging.

**Fil-C Impact:** ✅ No changes needed.

---

## Porting Roadmap (WITHOUT mruby)

### Phase 1: Build System (1 day)

1. **Configure with Fil-C toolchain:**
   ```bash
   mkdir build-filc
   cd build-filc
   cmake .. \
       -DCMAKE_C_COMPILER=clang-filc \
       -DCMAKE_C_FLAGS="-O2" \
       -DWITH_MRUBY=OFF \
       -DWITH_BUNDLED_SSL=ON
   ```

2. **Disable unsupported features:**
   - mruby handlers
   - Optional SIMD paths if problematic

**Expected issues:** Linker flags, missing Fil-C syscall wrappers

### Phase 2: Pointer Storage Cleanup (1 week)

**Task 1: Error Reporter** (2 days)
- Change `uintptr_t data` → `void *data`
- Update all `h2o_error_reporter_*` functions
- Files: `include/h2o/multithread.h`, `lib/common/multithread.c`
- Estimated: 50 LOC

**Task 2: Audit Custom Allocators** (3 days)
- Test memory pools under Fil-C
- If broken, disable and force `malloc`/`free`
- Files: `lib/common/memory.c`, `include/h2o/memory.h`
- Estimated: 0 LOC (if compatible) or 200-300 LOC (if replacement needed)

**Task 3: Verify Socket Abstractions** (2 days)
- Check `h2o_socket_t` for hidden pointer storage
- Audit multithread message passing
- Files: `lib/common/socket/*.c`
- Estimated: 0-20 LOC

### Phase 3: SIMD and Platform Code (3-5 days)

**Task 1: Picotls Fusion** (2 days)
- Add `zmkptr` for alignment in `deps/picotls/lib/fusion.c`
- Test AES-NI crypto operations
- Estimated: 10-20 LOC

**Task 2: CPU Feature Detection** (1 day)
- Replace `_xgetbv` with `zxgetbv()` if used
- Estimated: 5-10 LOC

**Task 3: Symbol Versioning** (1 day)
- Remove `-Wl,` prefix from linker flags (if present)
- Pattern from 15+ upstream ports
- Estimated: 5-10 LOC

### Phase 4: Testing (1-2 weeks)

1. **Unit tests:**
   ```bash
   make test
   ```

2. **Integration tests:**
   - Static file serving
   - HTTP/2 multiplexing
   - Proxy/FastCGI
   - WebSocket

3. **Stress tests:**
   - h2load benchmark
   - Long-running connections
   - Memory leak detection

**Expected issues:**
- Memory pool lifetime violations
- Interthread pointer sharing
- SIMD alignment edge cases

---

## H2O vs nginx Portability

### nginx Advantages (Likely Easier to Port)

#### 1. No Embedded Scripting

**nginx:**
- Configuration: Declarative (nginx.conf)
- Dynamic logic: C modules only
- Lua support: **Optional** via OpenResty (can be disabled)

**H2O:**
- Configuration: Can use mruby scripts
- Handlers: mruby embedded in core
- Disabling mruby: Loses dynamic features

#### 2. Simpler Memory Model

**nginx:**
```c
// nginx/src/core/ngx_palloc.h
typedef struct ngx_pool_s {
    ngx_pool_data_t       d;
    size_t                max;
    ngx_pool_t           *current;  // ✅ Simple linked list
    // ...
} ngx_pool_t;
```
- Per-request pools similar to H2O
- No thread-local recycling
- Simpler cleanup model

**H2O:**
- Thread-local pool recycler
- Shared reference counting
- More complex lifetime management

#### 3. Fewer Dependencies

**nginx core:**
- PCRE (regex)
- zlib (compression)
- OpenSSL (TLS)

**H2O core:**
- PCRE
- zlib
- OpenSSL
- **mruby** (if enabled)
- **picotls** (alternative TLS with SIMD)
- **wslay** (WebSocket)

#### 4. Mature Codebase

**nginx:**
- 20 years old (2004)
- Fewer experimental features
- More conservative design

**H2O:**
- 11 years old (2014)
- Cutting-edge features (HTTP/3, QUIC)
- More aggressive optimizations

### nginx Challenges (Still Significant)

#### 1. Buffer Management

nginx uses complex buffer chains:
```c
typedef struct ngx_chain_s {
    ngx_buf_t    *buf;
    ngx_chain_t  *next;  // May contain pointer tagging? Need investigation
} ngx_chain_t;
```

#### 2. Shared Memory

nginx workers communicate via shared memory:
```c
ngx_shmtx_t  *mutex;  // Shared across processes
void         *addr;   // mmap'd region
```

Fil-C's capability model assumes per-process heaps - shared memory needs careful handling.

#### 3. Process Model

nginx uses **prefork** (master + workers), not threads:
- Shared memory for statistics
- Shared sockets via SO_REUSEPORT
- Potential capability transfer issues

### Portability Ranking

| Feature | nginx | H2O (no mruby) | H2O (with mruby) |
|---------|-------|----------------|------------------|
| Pointer Tagging | ✅ Unlikely | ✅ None found | ❌ Pervasive |
| Memory Pools | ⚠️ Complex | ⚠️ Complex | ⚠️ Complex |
| FFI Boundaries | ✅ None | ✅ None | ❌ mruby NaN-boxing |
| SIMD Usage | ⚠️ Possible | ⚠️ picotls | ⚠️ picotls |
| Shared Memory | ⚠️ Heavy use | ✅ Minimal | ✅ Minimal |
| Process Model | ⚠️ Prefork | ✅ Threads | ✅ Threads |
| **Overall** | **6/10** | **7/10** | **1/10** |

### Recommendation

**For Fil-C Web Server:**

1. **Easiest:** lighttpd (already ported - see `lighttpd-filc.patch`)
2. **Medium:** nginx (cleaner separation, no embedded language)
3. **Hard:** H2O without mruby (loses key features)
4. **Impossible:** H2O with mruby (requires VM rewrite)

---

## Comparison to Documented Ports

### Categorization by Difficulty

#### Easy Ports (< 100 LOC)

| Project | LOC | Main Changes |
|---------|-----|--------------|
| dash | 13 | `vfork` → `fork` |
| vim | 13 | `sigaction` null check |
| bash | 13 | Flexible array type |
| openssh | 14 | seccomp whitelist |
| tmux | 16 | None |

**H2O comparison:** Not in this category - fundamental architecture issues.

#### Medium Ports (100-500 LOC)

| Project | LOC | Main Changes |
|---------|-----|--------------|
| grep | 38 | `zmkptr` alignment, disable stack overflow |
| zsh | 46 | Disable custom allocator |
| libffi | 440 | Custom closure/trampoline |
| systemd | 455 | Symbol versioning, error map inlining |

**H2O comparison:** Could be here if:
- mruby disabled
- Memory pools work without changes
- Only SIMD and `uintptr_t` fixes needed

#### Hard Ports (500-2000 LOC)

| Project | LOC | Main Changes |
|---------|-----|--------------|
| emacs | 588 | Replace allocator with `zgc_alloc` |
| perl | 892 | 20+ `zptrtable` instances |
| Python | 1551 | GC rewrite, atomic pointers, frame allocation |

**H2O comparison (no mruby):** Likely here - estimated 300-500 LOC across:
- Pointer storage cleanup (100)
- Memory pool fixes (200-300)
- SIMD fixes (20)
- Build system (10)

**H2O comparison (with mruby):** **Impossible** - would need:
- mruby VM value representation rewrite (5000+ LOC)
- All mruby C extensions updated
- Bytecode format changes
- GC algorithm modifications
- Similar effort to porting V8 or JavaScriptCore

### Pattern Match Analysis

#### ✅ Patterns H2O Avoids

1. **Pointer Tagging in Data Structures**
   - dhcpcd (203 LOC): RB-tree with tagged parent pointers
   - libarchive (98 LOC): RB-tree with tagged pointers
   - H2O: Uses clean intrusive lists

2. **Atomic Pointer Storage**
   - Python (1551 LOC): `atomic_uintptr_t` → `void*_Atomic`
   - H2O: No atomic pointers found

3. **Inline Assembly**
   - zstd (102 LOC): Disabled loop alignment
   - icu (77 LOC): Disabled assembly generation
   - H2O: None in core (only SIMD intrinsics)

#### ❌ Patterns H2O Shares with Hard Ports

1. **Embedded Language Runtime**
   - Python (1551 LOC): CPython bytecode + GC
   - perl (892 LOC): Perl XS + threading
   - H2O: mruby NaN-boxing (worse than both)

2. **Custom Memory Allocators**
   - emacs (588 LOC): Replaced with `zgc_alloc`
   - zsh (46 LOC): Disabled `zhalloc`
   - H2O: Thread-local recycling pools

3. **FFI Pointer Encoding**
   - Perl (892 LOC): `PTR2IV`/`INT2PTR` → `zptrtable`
   - SQLite (473 LOC): TCL test pointers → `zptrtable`
   - H2O: mruby NaN-boxing (no `zptrtable` solution)

---

## Conclusion

### Feasibility Assessment

**WITHOUT mruby:**
- **Feasible:** Yes
- **Effort:** 3-4 weeks
- **Risk:** Medium (memory pools may need rework)
- **Value:** Limited (loses dynamic handlers)

**WITH mruby:**
- **Feasible:** No
- **Effort:** 6-12 months (VM rewrite)
- **Risk:** Extreme (fundamental architecture change)
- **Value:** High (preserves all features)

### Recommendation

**Do NOT port H2O for Fil-C.** Instead:

1. **Use lighttpd** (already ported):
   ```bash
   # See lighttpd-filc.patch in this repo
   ```

2. **Port nginx** (cleaner architecture):
   - Estimated effort: 2-4 weeks
   - No embedded language
   - Simpler memory model
   - Industry-standard server

3. **Use Apache httpd** (already in upstream fil-c):
   ```bash
   # See httpd/ directory
   ```

### If You Must Port H2O

**Phase 1: Disable mruby (1 day)**
```bash
cmake -DWITH_MRUBY=OFF
```

**Phase 2: Minimal viable port (3-4 weeks)**
- Fix `uintptr_t` pointer storage
- Test memory pools
- Fix SIMD alignment
- Verify socket abstractions

**Phase 3: Full testing (2 weeks)**
- HTTP/1.1 compliance
- HTTP/2 multiplexing
- Proxy/FastCGI
- Performance benchmarks

**Total effort:** 5-6 weeks for limited functionality

---

## Appendix: Code Patterns

### Pattern 1: Clean Linked Lists (Compatible)

**H2O's approach:**
```c
typedef struct st_h2o_linklist_t {
    struct st_h2o_linklist_t *next;  // ✅ Capability preserved
    struct st_h2o_linklist_t *prev;
} h2o_linklist_t;

#define H2O_STRUCT_FROM_MEMBER(s, m, p) \
    ((s *)((char *)(p) - offsetof(s, m)))  // ✅ Standard offsetof
```

### Pattern 2: mruby NaN-Boxing (Incompatible)

**What NOT to do:**
```c
// deps/mruby/include/mruby/boxing_nan.h
typedef struct mrb_value {
    union {
        mrb_float f;
        void *p;
        mrb_int i;
        mrb_sym sym;
        uint64_t u;  // ❌ Pointer stored here with bit manipulation
    } value;
} mrb_value;

#define SET_OBJ_VALUE(r,v) do {
    (r).u = (uint64_t)(uintptr_t)(v);  // ❌ Destroys capability
} while (0)
```

**Fil-C compatible alternative (Lua's approach):**
```c
// Lua 5.4 uses union without bit tricks
typedef union Value {
    GCObject *gc;    // ✅ Real pointer
    void *p;         // ✅ Real pointer
    lua_Integer i;   // Integer
    lua_Number n;    // Float
} Value;

typedef struct TValue {
    Value value_;
    lu_byte tt_;     // ✅ Separate tag field
} TValue;
```

### Pattern 3: Pointer Alignment (SIMD)

**Problematic pattern:**
```c
// deps/picotls/lib/fusion.c
uintptr_t shift = (uintptr_t)p & 15;  // Extract alignment
__m128i data = _mm_loadu_si128((const __m128i *)(buffer + shift));
//                              ^^^^^^^^^^^^^^^^^ Lost provenance
```

**Fil-C fix:**
```c
+#include <stdfil.h>

uintptr_t shift = (uintptr_t)p & 15;  // OK - just testing bits
+const char *aligned = (const char *)zmkptr(buffer, (uintptr_t)buffer + shift);
-__m128i data = _mm_loadu_si128((const __m128i *)(buffer + shift));
+__m128i data = _mm_loadu_si128((const __m128i *)aligned);
```

### Pattern 4: Generic Pointer Storage

**Problematic:**
```c
typedef struct st_h2o_error_reporter_t {
    uintptr_t data;  // ❌ Pointer as integer
} h2o_error_reporter_t;
```

**Fixed:**
```c
typedef struct st_h2o_error_reporter_t {
    void *data;  // ✅ Typed pointer
} h2o_error_reporter_t;
```
