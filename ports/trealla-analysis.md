# Trealla Prolog Fil-C Porting Analysis

**Date:** November 4, 2025  
**Upstream:** https://github.com/trealla-prolog/trealla  
**Status:** Feasibility Analysis Complete  
**Estimated Effort:** 3-4 days (2 days porting + 2 days testing)

---

## Executive Summary

Trealla Prolog is **highly suitable** for fil-c porting due to its clean, capability-friendly design:

- ✅ **No pointer tagging** - uses explicit tag fields instead of low-bit tricks
- ✅ **Index-based frame management** - avoids pointer-to-integer-to-pointer roundtrips  
- ✅ **Standard memory allocation** - no custom allocators or memory pools
- ✅ **Pure portable C** - no inline assembly, no SIMD, no architecture-specific intrinsics
- ✅ **Minimal FFI boundary** - only ~30 functions need pointer table encoding

**Main compatibility challenges:**

1. **FFI handle storage** (15-20 LOC) - `dlopen`/`dlsym` handles stored as integers → requires `zptrtable`
2. **Skiplist pointer comparison** (10 LOC) - slot numbers cast to pointers for ordering → requires custom comparator
3. **Atomic operations** (future-proofing) - currently only uses atomic integers, no changes needed

**Risk Assessment:**

| Category | Risk Level | Notes |
|----------|------------|-------|
| Tagged Pointers | 🟢 None | No pointer tagging used anywhere |
| Pointer Arithmetic | 🟢 Low | Standard array indexing, bounds-safe |
| FFI Boundaries | 🟡 Medium | Requires `zptrtable` for handles (~30 LOC) |
| Memory Allocators | 🟢 Low | Uses standard malloc/calloc exclusively |
| Atomic Operations | 🟢 Low | Only atomic integers, no atomic pointers |
| Assembly/Intrinsics | 🟢 None | Pure portable C, no platform code |
| Alignment Tricks | 🟢 None | No bit masking or alignment dependencies |

**Comparison to other fil-c ports:**
- **Simpler than:** Python (GC rewrite), Perl (20+ pointer tables), Emacs (allocator replacement)
- **Similar to:** Git (type changes), Zsh (allocator bypass), Vim (minimal fixes)
- **Effort:** ~30-50 lines of changes vs 1500+ for Python

---

## Table of Contents

1. [Why Trealla is Fil-C Friendly](#why-trealla-is-fil-c-friendly)
2. [Critical Issue #1: FFI Pointer Management](#critical-issue-1-ffi-pointer-management)
3. [Critical Issue #2: Skiplist Pointer Comparison](#critical-issue-2-skiplist-pointer-comparison)
4. [Term Representation Analysis](#term-representation-analysis)
5. [Memory Management Analysis](#memory-management-analysis)
6. [Threading and Atomics](#threading-and-atomics)
7. [String Representation](#string-representation)
8. [Concrete Porting Roadmap](#concrete-porting-roadmap)
9. [Comparison to Other Prolog Systems](#comparison-to-other-prolog-systems)
10. [Risk Mitigation Strategies](#risk-mitigation-strategies)

---

## Why Trealla is Fil-C Friendly

### Design Decision: Explicit Tags vs Pointer Tagging

Most Prolog systems use **pointer tagging** to pack type information into unused low bits of pointers. This is fundamentally incompatible with fil-c's capability model.

#### Traditional Approach (SWI-Prolog, YAP) - INCOMPATIBLE

```c
// Stores tag in low 3 bits of pointer
typedef uintptr_t word;

#define TAG_MASK     0x7
#define TAG_VAR      0x0
#define TAG_ATOM     0x1
#define TAG_INT      0x2

word make_atom(const char *name) {
    void *ptr = allocate_atom(name);
    return (word)ptr | TAG_ATOM;  // ❌ Destroys capability metadata!
}

bool is_atom(word w) {
    return (w & TAG_MASK) == TAG_ATOM;  // ❌ Bit manipulation
}

void* get_atom_ptr(word w) {
    return (void*)(w & ~TAG_MASK);  // ❌ Reconstructed pointer loses bounds
}
```

**Fil-C problems:**
- Converting pointer to `uintptr_t` strips capability (bounds, type info)
- Bitwise operations destroy capability provenance
- Reconstructing pointer from masked integer has undefined bounds
- **Every term operation** would need `zorptr`/`zandptr`/`zretagptr` wrappers

#### Trealla's Approach - COMPATIBLE

**Source:** `src/internal.h:340-402`

```c
typedef struct cell_ {
    uint8_t tag;              // ✅ Explicit tag byte (not in pointer!)
    uint8_t arity;
    uint16_t flags;
    uint32_t num_cells;
    
    union {
        pl_uint val_uint;     // Integers stored as values
        pl_int val_int;
        pl_flt val_float;
        
        bigint *val_bigint;   // ✅ Normal pointers - untagged!
        blob *val_blob;
        
        struct {
            union {
                predicate *match;
                builtins *bif_ptr;
                cell *tmp_attrs;
                cell *val_ptr;     // Used for TAG_INDIRECT
                cell *val_attrs;
            };
            uint32_t var_num;
            uint32_t val_off;
        };
    };
} cell;
```

**Usage example:**

```c
bool is_atom(const cell *c) {
    return c->tag == TAG_CSTR;  // ✅ Simple field comparison
}

const char* get_atom_str(const cell *c) {
    return c->val_str;  // ✅ Direct pointer access, capability preserved
}
```

**Fil-C impact:** **Zero changes needed** for term representation. All pointers maintain capabilities naturally.

---

### Design Decision: Index-Based Contexts

Trealla uses **array indices** for context/frame references instead of direct pointers. This avoids pointer-to-integer-to-pointer roundtrips that would require `zptrtable` encoding.

#### Trealla's Frame System

**Source:** `src/internal.h:209-222`

```c
typedef uint32_t pl_ctx;  // ✅ Context is an INTEGER INDEX, not a pointer

typedef struct frame_ {
    pl_ctx curr_frame;      // ✅ Parent frame index
    pl_ctx base_frame;      // ✅ Base frame index
    pl_ctx prev_frame;
    unsigned base;          // Slot array offset
    unsigned overflow_sz;
    // ...
} frame;

// Frames stored in growable array
typedef struct {
    frame *frames;          // ✅ Base pointer for array
    size_t frames_size;
    // ...
} query;

// Access via array indexing
#define GET_FRAME(i) (q->frames + (i))  // ✅ Pointer arithmetic from base
#define GET_CURR_FRAME() GET_FRAME(q->st.cur_ctx)
```

**Why this works in fil-c:**
- `q->frames` is a capability pointer with bounds covering entire array
- Array indexing `q->frames + i` maintains capability bounds
- No pointer→integer→pointer conversions needed
- Frame indices are true integers (32-bit), not encoded pointers

#### Bad Alternative (Python's Approach)

**Source:** Python's `pycore_frame.h` (required major refactoring for fil-c)

```c
// Python stores direct frame pointers
typedef struct _PyInterpreterFrame {
    struct _PyInterpreterFrame *f_back;  // ❌ Direct pointer
    PyCodeObject *f_code;
    // ...
} _PyInterpreterFrame;

// Problem: Bytecode embeds frame pointers as integers
static inline void write_frame(uint16_t *p, _PyInterpreterFrame *f) {
    // fil-c requires zptrtable encoding here
    uintptr_t encoded = zptrtable_encode(frame_table, f);  // ❌ Overhead
    memcpy(p, &encoded, sizeof(encoded));
}

static inline _PyInterpreterFrame* read_frame(uint16_t *p) {
    uintptr_t encoded;
    memcpy(&encoded, p, sizeof(encoded));
    return zptrtable_decode(frame_table, encoded);  // ❌ Overhead
}
```

**Trealla avoids this entirely** by using indices that are genuine integers, not encoded pointers.

---

### Design Decision: String Slicing with Explicit Bounds

**Source:** `src/internal.h:192-201`

```c
// Three string representations:

// 1. Small strings (inline in cell)
typedef struct {
    char val_chr[MAX_SMALL_STRING];  // ✅ Inline array
    size_t chr_len;
} small_string;

// 2. Heap-allocated strings
typedef struct {
    strbuf *val_strb;     // ✅ Pointer to refcounted buffer
    uint32_t strb_off;    // Offset into buffer
    uint32_t strb_len;    // Length of slice
} heap_string;

// 3. External string slices
typedef struct {
    char *val_str;        // ✅ Pointer to start of slice
    uint64_t str_len;     // ✅ Explicit length
} string_slice;
```

**Creating a slice (capability-safe):**

```c
cell slice;
slice.tag = TAG_CSTR;
slice.val_str = original.val_str + offset;  // ✅ Pointer arithmetic
slice.str_len = length;                      // ✅ Bounds stored separately
```

**Why this works in fil-c:**
- Pointer arithmetic from `original.val_str` maintains capability
- Capability bounds include entire original string buffer
- Runtime length check via `str_len` prevents overruns
- Fil-C's bounds checker validates every access automatically

**Bad alternative:**

```c
// Storing substring as (base_ptr, offset, length) - requires reconstruction
typedef struct {
    uintptr_t base;   // ❌ Pointer stored as integer
    uint32_t offset;
    uint32_t length;
} substring;

// Accessing requires zmkptr
char *get_substr_ptr(substring *s) {
    char *base = zptrtable_decode(string_table, s->base);  // ❌ Decode
    return zmkptr(base, (uintptr_t)base + s->offset);     // ❌ Reconstruct
}
```

---

## Critical Issue #1: FFI Pointer Management

### The Problem

Trealla's FFI system stores dynamic library handles (from `dlopen`) and function pointers (from `dlsym`) as Prolog integers. This destroys capabilities.

**Location:** `src/bif_ffi.c:110-130`

```c
static bool bif_sys_dlopen_3(query *q)
{
    GET_FIRST_ARG(p1, atom_or_list);     // Library path
    GET_NEXT_ARG(p2, integer);           // Flags (RTLD_LAZY, etc.)
    GET_NEXT_ARG(p3, var);               // Output: handle

    char *filename = C_STR(q, p1);
    void *handle = do_dlopen(filename, get_smallint(p2));
    
    if (!handle)
        return throw_error(q, p3, q->st.m->error_ctx, 
                          "existence_error", "source_sink");

    cell tmp;
    make_uint(&tmp, (pl_int)(size_t)handle);  // ❌ void* → integer
    tmp.flags |= FLAG_INT_HANDLE | FLAG_HANDLE_DLL;
    
    return unify(q, p3, p3_ctx, &tmp, q->st.curr_frame);
}
```

**Why this breaks in fil-c:**

1. `handle` is a capability pointer with bounds covering the entire loaded library
2. Casting to `(size_t)` strips all capability metadata
3. Later retrieval via `get_smalluint()` returns raw integer with no provenance
4. Using this integer as a pointer would **trap** in fil-c

**Retrieval code (also broken):**

```c
static bool bif_sys_dlsym_3(query *q)
{
    GET_FIRST_ARG(p1, integer);          // Handle (should be capability)
    GET_NEXT_ARG(p2, atom);              // Symbol name
    GET_NEXT_ARG(p3, var);

    size_t handle = get_smalluint(p1);   // ❌ Integer, not pointer
    const char *symbol = C_STR(q, p2);
    void *ptr = dlsym((void*)handle, symbol);  // ❌ UB - cast from random integer
    
    // ... more broken pointer storage
}
```

### The Solution: Global FFI Pointer Table

Following the pattern from **perl**, **python**, **sqlite** ports (see `ports/analysis.md`), use `zptrtable` to encode pointers as integers while preserving capabilities in a side table.

#### Implementation

**Step 1: Add global pointer table**

```c
// At top of src/bif_ffi.c
#include <stdfil.h>

static zptrtable *g_ffi_handles = NULL;

static void ensure_ffi_handles(void) {
    if (!g_ffi_handles)
        g_ffi_handles = zptrtable_new_weak();
}
```

**Why `zptrtable_new_weak()`?**
- Weak tables don't prevent GC of stored pointers
- FFI handles are explicitly managed (dlopen/dlclose)
- Avoids memory leaks from unclosed libraries

**Step 2: Encode handles when storing**

```c
static bool bif_sys_dlopen_3(query *q)
{
    GET_FIRST_ARG(p1, atom_or_list);
    GET_NEXT_ARG(p2, integer);
    GET_NEXT_ARG(p3, var);

    char *filename = C_STR(q, p1);
    void *handle = do_dlopen(filename, get_smallint(p2));
    
    if (!handle)
        return throw_error(q, p3, q->st.m->error_ctx, 
                          "existence_error", "source_sink");

    ensure_ffi_handles();
    uintptr_t encoded = zptrtable_encode(g_ffi_handles, handle);  // ✅ Encode
    
    cell tmp;
    make_uint(&tmp, encoded);  // Store index, not raw pointer
    tmp.flags |= FLAG_INT_HANDLE | FLAG_HANDLE_DLL;
    
    return unify(q, p3, p3_ctx, &tmp, q->st.curr_frame);
}
```

**What `zptrtable_encode` does:**
1. Stores `handle` pointer in hash table with unique integer key
2. Returns integer key (safe to store anywhere)
3. Preserves full capability metadata in table entry

**Step 3: Decode handles when retrieving**

```c
static bool bif_sys_dlsym_3(query *q)
{
    GET_FIRST_ARG(p1, integer);
    GET_NEXT_ARG(p2, atom);
    GET_NEXT_ARG(p3, var);

    if (!is_handle(p1))
        return throw_error(q, p1, p1_ctx, "type_error", "handle");

    ensure_ffi_handles();
    uintptr_t encoded = get_smalluint(p1);
    void *handle = zptrtable_decode(g_ffi_handles, encoded);  // ✅ Restore
    
    const char *symbol = C_STR(q, p2);
    void *ptr = dlsym(handle, symbol);
    
    if (!ptr)
        return throw_error(q, p2, p2_ctx, "existence_error", "procedure");

    // Encode function pointer too!
    uintptr_t fn_encoded = zptrtable_encode(g_ffi_handles, ptr);
    
    cell tmp;
    make_uint(&tmp, fn_encoded);
    tmp.flags |= FLAG_INT_HANDLE | FLAG_HANDLE_FN;
    
    return unify(q, p3, p3_ctx, &tmp, q->st.curr_frame);
}
```

**Step 4: Cleanup on dlclose**

```c
static bool bif_sys_dlclose_1(query *q)
{
    GET_FIRST_ARG(p1, integer);
    
    if (!is_handle(p1))
        return throw_error(q, p1, p1_ctx, "type_error", "handle");

    ensure_ffi_handles();
    uintptr_t encoded = get_smalluint(p1);
    void *handle = zptrtable_decode(g_ffi_handles, encoded);
    
    dlclose(handle);
    
    // Optional: Remove from table to free memory
    // (zptrtable API would need to support removal, or use zexact_ptrtable)
    
    return true;
}
```

### Functions Requiring Changes

**Primary FFI functions (~12 total):**

| Function | Location | Change Required |
|----------|----------|-----------------|
| `bif_sys_dlopen_3` | bif_ffi.c:110 | Encode library handle |
| `bif_sys_dlsym_3` | bif_ffi.c:123 | Decode library, encode function ptr |
| `bif_sys_dlclose_1` | bif_ffi.c:137 | Decode handle before close |
| `bif_sys_register_ffi_struct_*` | bif_ffi.c:800+ | Encode struct pointers |
| `bif_sys_call_ffi_*` | bif_ffi.c:2000+ | Decode function pointers before call |

**Supporting utilities:**

```c
// Helper to decode FFI handle with type checking
static void* decode_ffi_handle(query *q, cell *c, pl_ctx ctx, const char *expected_type) {
    if (!is_handle(c)) {
        throw_error(q, c, ctx, "type_error", "handle");
        return NULL;
    }
    
    ensure_ffi_handles();
    return zptrtable_decode(g_ffi_handles, get_smalluint(c));
}
```

### Testing

```prolog
% Test basic FFI handle roundtrip
test_ffi_handles :-
    dlopen('libc.so.6', 2, H),        % RTLD_LAZY
    integer(H),                        % Handle stored as integer
    dlsym(H, 'strlen', StrLen),
    integer(StrLen),                   % Function ptr as integer
    call_ffi(StrLen, [ptr], int, ["hello"], N),
    N =:= 5,
    dlclose(H).

% Test handle type safety
test_ffi_invalid_handle :-
    \+ dlsym(12345, 'strlen', _).     % Should fail with type_error
```

---

## Critical Issue #2: Skiplist Pointer Comparison

### The Problem

Trealla uses skiplists (probabilistic balanced trees) for several data structures. The default comparator treats pointers as integers for ordering, which breaks when "pointers" are actually integers cast to pointer type.

**Location:** `src/skiplist.c:50-56`

```c
static int default_cmpkey(const void *p1, const void *p2, 
                         const void *p, int *depth)
{
    ptrdiff_t i1 = (ptrdiff_t)p1;  // ❌ Pointer → integer conversion
    ptrdiff_t i2 = (ptrdiff_t)p2;  // ❌ Undefined for non-pointers
    
    if (i1 < i2) return -1;        // ❌ Ordering based on raw address
    if (i1 > i2) return 1;
    return 0;
}
```

**Where it's used: Variable slot tracking**

**Location:** `src/heap.c:13-25`

```c
static int accum_slot(const query *q, size_t slot_nbr, unsigned var_num)
{
    if (!q->vars)
        return var_num;

    const void *vnbr;
    
    // ❌ Using slot number (size_t) as skiplist key via pointer cast
    if (sl_get(q->vars, (void*)slot_nbr, &vnbr))
        return (unsigned)(size_t)vnbr;

    // ❌ Both key and value are integers stored as pointers
    sl_app(q->vars, (void*)slot_nbr, (void*)(size_t)var_num);
    return var_num;
}
```

**Why this breaks in fil-c:**

1. `slot_nbr` is a `size_t` integer, not an actual pointer
2. Casting to `void*` creates a capability with undefined bounds
3. Comparing these "pointers" via `ptrdiff_t` cast is undefined behavior
4. Fil-c's capability checker would trap on invalid pointer operations

**Other uses of skiplist:**

```c
// src/query.c - choice point map (genuine pointers - OK)
q->pl->choices = sl_create(default_cmpkey, NULL, NULL);

// src/module.c - predicate map (genuine pointers - OK)  
m->preds = sl_create(default_cmpkey, NULL, NULL);

// src/heap.c - variable tracking (integers-as-pointers - BROKEN)
q->vars = sl_create(default_cmpkey, NULL, NULL);
```

### Solution #1: Custom Integer Comparator (Recommended)

The skiplist implementation already supports custom comparators! Just provide one for integer keys.

**Add to `src/skiplist.c`:**

```c
// Integer key comparator for slot numbers and similar
int sl_int_cmpkey(const void *p1, const void *p2, const void *p, int *depth)
{
    uintptr_t i1 = (uintptr_t)p1;  // ✅ Explicit integer extraction
    uintptr_t i2 = (uintptr_t)p2;
    
    if (i1 < i2) return -1;
    if (i1 > i2) return 1;
    return 0;
}
```

**Export in `src/skiplist.h`:**

```c
extern int sl_int_cmpkey(const void *p1, const void *p2, 
                         const void *p, int *depth);
```

**Update `src/heap.c`:**

```c
// When initializing q->vars
q->vars = sl_create(sl_int_cmpkey, NULL, NULL);  // ✅ Use integer comparator
```

**Why this works:**
- Slot numbers are true integers, not pointers
- Comparator explicitly treats keys as `uintptr_t` values
- No pointer operations involved
- Fil-c sees only integer arithmetic, no capability violations

### Solution #2: Use zexact_ptrtable (Alternative)

If you need true pointer semantics (bijective mapping):

```c
#include <stdfil.h>

static zexact_ptrtable *g_slot_ptrs = NULL;

static int accum_slot(const query *q, size_t slot_nbr, unsigned var_num)
{
    if (!q->vars)
        return var_num;

    if (!g_slot_ptrs)
        g_slot_ptrs = zexact_ptrtable_new();

    // Encode slot number → capability pointer
    void *slot_key = zexact_ptrtable_decode(g_slot_ptrs, slot_nbr);
    
    const void *vnbr;
    if (sl_get(q->vars, slot_key, &vnbr)) {
        // Decode var_num from pointer
        return (unsigned)zexact_ptrtable_encode(g_slot_ptrs, (void*)vnbr);
    }

    void *var_key = zexact_ptrtable_decode(g_slot_ptrs, var_num);
    sl_app(q->vars, slot_key, var_key);
    return var_num;
}
```

**Why Solution #1 is better:**
- Slot numbers are conceptually integers, not pointers
- No encoding overhead
- Simpler code
- No additional data structures

### Impact Assessment

**Files to modify:** 2-3 files

1. `src/skiplist.c` - add `sl_int_cmpkey` function (5 lines)
2. `src/skiplist.h` - export declaration (1 line)
3. `src/heap.c` - use integer comparator (1 line change)

**Testing:**

```prolog
% Test variable slot allocation
test_var_slots :-
    X = 1, Y = 2, Z = 3,
    % Internally allocates slots via accum_slot
    findall([X,Y,Z], (X = 1; X = 2; X = 3), L),
    length(L, 3).

% Stress test: many variables
test_many_slots :-
    length(L, 1000),
    findall(X, member(X, L), L).
```

---

## Term Representation Analysis

### Cell Structure Deep Dive

**Source:** `src/internal.h:340-402`

```c
typedef struct cell_ {
    // 8 bytes of metadata (no pointers)
    uint8_t tag;              // Type: TAG_VAR, TAG_ATOM, TAG_INT, etc.
    uint8_t arity;            // For compound terms
    uint16_t flags;           // Various flags
    uint32_t num_cells;       // Size in cell units
    
    // 8 bytes of data (union)
    union {
        // Small values (stored inline)
        pl_uint val_uint;     // Unsigned integer
        pl_int val_int;       // Signed integer  
        pl_flt val_float;     // Double
        char val_chr[MAX_SMALL_STRING];  // Small string (inline)
        
        // Heap-allocated values (pointers)
        bigint *val_bigint;   // Arbitrary precision integer
        blob *val_blob;       // Binary data
        strbuf *val_strb;     // String buffer
        
        // Variable/indirect reference
        struct {
            union {
                predicate *match;    // Predicate pointer
                builtins *bif_ptr;   // Built-in function
                cell *tmp_attrs;     // Temporary attributes
                cell *val_ptr;       // Indirect cell pointer
                cell *val_attrs;     // Attribute list
            };
            uint32_t var_num;        // Variable number
            uint32_t val_off;        // Offset in cells
        };
    };
} cell;
```

**Total size:** 16 bytes (perfect cache line usage on x86-64)

### Tag Values

**Source:** `src/internal.h:76-96`

```c
enum {
    TAG_VAR = 0,       // Unbound variable
    TAG_INT = 1,       // Small integer
    TAG_ATOM = 2,      // Atom (symbol)
    TAG_CSTR = 3,      // C string
    TAG_FLOAT = 4,     // Floating point
    TAG_BIGINT = 5,    // Big integer (heap)
    TAG_BLOB = 6,      // Binary blob
    TAG_INDIRECT = 7,  // Indirect reference (uses val_ptr)
    TAG_EMPTY = 8,     // Empty list []
    // ... more tags
};
```

### Tag Checking (Capability-Safe)

```c
// All tag checks use field access, no bit manipulation
inline static bool is_var(const cell *c) { 
    return c->tag == TAG_VAR; 
}

inline static bool is_atom(const cell *c) { 
    return c->tag == TAG_ATOM || c->tag == TAG_CSTR; 
}

inline static bool is_indirect(const cell *c) { 
    return c->tag == TAG_INDIRECT; 
}

// Pointer extraction is direct field access
inline static cell* deref_ptr(const cell *c) {
    return c->val_ptr;  // ✅ Returns capability pointer directly
}
```

**Fil-C impact:** ✅ **Zero changes needed** - all operations preserve capabilities.

### Contrast with Tagged Pointer Systems

**WAM (Warren Abstract Machine) style:**

```c
// Traditional Prolog representation
typedef uintptr_t term;

#define TAG_BITS 3
#define TAG_MASK 0x7

#define TAG_REF  0  // Variable reference
#define TAG_STR  1  // Structure
#define TAG_LIS  2  // List
#define TAG_CON  3  // Constant
#define TAG_INT  4  // Integer

// Creating a structure term
term make_structure(functor *f) {
    return (term)f | TAG_STR;  // ❌ Destroys capability
}

// Dereferencing
cell* deref_structure(term t) {
    return (cell*)(t & ~TAG_MASK);  // ❌ Broken bounds
}
```

**Porting to fil-c would require:**
- All `make_*` functions use `zorptr(ptr, TAG_*)`
- All `deref_*` functions use `zandptr(term, ~TAG_MASK)`
- All tag checks use `(uintptr_t)term & TAG_MASK`
- Hundreds of call sites changed
- **Trealla avoids this entirely!**

---

## Memory Management Analysis

### Allocation Strategy

Trealla uses **page-based heap allocation** with standard `malloc`/`calloc`. No custom allocators that would conflict with fil-c's capability tracking.

**Source:** `src/heap.c:339-362`

```c
typedef struct page_ {
    cell *cells;              // ✅ Malloc'd array
    size_t page_size;         // Number of cells
    struct page_ *next;       // Linked list
} page;

cell *alloc_heap(query *q, unsigned num_cells) {
    // Allocate new page if needed
    if (!q->heap_pages || (q->st.hp + num_cells) > q->heap_pages->page_size) {
        unsigned n = (num_cells < q->h_size) ? q->h_size : num_cells;
        page *a = calloc(1, sizeof(page));  // ✅ Standard allocation
        a->cells = calloc(a->page_size = n, sizeof(cell));
        a->next = q->heap_pages;
        q->heap_pages = a;
        q->st.hp = 0;
    }
    
    cell *c = q->heap_pages->cells + q->st.hp;  // ✅ Array indexing
    q->st.hp += num_cells;
    return c;
}
```

**Why this works in fil-c:**
- `calloc` returns capability pointer covering allocated memory
- Pointer arithmetic `cells + offset` maintains capability bounds
- No slab allocators, arena allocators, or object pools
- No assumptions about allocator behavior (unlike gnulib tests that fil-c had to disable)

### Reference Counting

**Source:** `src/internal.h:921-984`

```c
// Reference count type
typedef pl_atomic int64_t pl_refcnt;  // ✅ Atomic integer, not pointer

// Increment reference count
inline static void share_cell_(const cell *c) {
    if (is_strbuf(c))
        c->val_strb->refcnt++;  // ✅ Normal pointer dereference
    else if (is_bigint(c))
        c->val_bigint->refcnt++;
    else if (is_blob(c))
        c->val_blob->refcnt++;
}

// Decrement and free if zero
inline static void unshare_cell_(cell *c) {
    if (is_strbuf(c) && c->val_strb && !c->val_strb->refcnt--) {
        free(c->val_strb);  // ✅ Standard free
        c->val_strb = NULL;
    }
    // ... similar for other types
}
```

**Contrast with Python's approach:**

Python required major GC header refactoring for fil-c because it stored mark bits in pointer low bits:

```c
// Python's GC header (BEFORE fil-c port)
typedef struct {
    uintptr_t _gc_next;  // ❌ Pointer with tag bits
    uintptr_t _gc_prev;  // ❌ Low 2 bits used for flags
} PyGC_Head;

// Extracting prev pointer
#define _PyGCHead_PREV(gc) ((PyGC_Head*)((gc)->_gc_prev & ~_PyGC_PREV_MASK))

// AFTER fil-c port - required zandptr operations
#define _PyGCHead_PREV(gc) ((PyGC_Head*)zandptr((gc)->_gc_prev, _PyGC_PREV_MASK))
```

**Trealla avoids this** - refcounts are plain integers, no GC mark bits in pointers.

### Memory Lifecycle

```c
// Allocation
cell *c = alloc_heap(q, 5);  // ✅ Gets capability pointer

// Initialization
c[0].tag = TAG_ATOM;
c[0].val_str = "hello";
share_cell(&c[0]);           // ✅ Increment refcount

// Usage
const char *s = c->val_str;  // ✅ Capability preserves bounds
size_t len = c->str_len;

// Cleanup
unshare_cell(c);             // ✅ Decrement, free if zero
```

**Fil-C impact:** ✅ **No changes needed** - standard allocator usage throughout.

---

## Threading and Atomics

### Current Atomics Usage

**Source:** `src/internal.h:34-39`

```c
#if (__STDC_VERSION__ >= 201112L) && USE_THREADS
#include <stdatomic.h>
#define pl_atomic _Atomic
#else
#define pl_atomic volatile
#endif
```

**Where it's used:**

```c
typedef pl_atomic int64_t pl_refcnt;  // ✅ Atomic integer for refcounting

typedef struct {
    pl_atomic bool is_active;         // ✅ Atomic bool flag
    pl_atomic uint64_t tot_goals;     // ✅ Atomic counter
    // ...
} thread_info;
```

**Fil-C impact:** ✅ **Already compatible** - only atomic integers, no atomic pointers.

### Future-Proofing: Atomic Pointers

If Trealla ever needs atomic pointer operations:

**Wrong approach (breaks fil-c):**

```c
typedef struct {
    _Atomic uintptr_t next;  // ❌ Atomic integer holding pointer
} lock_free_stack;

void push(lock_free_stack *s, node *n) {
    uintptr_t old = atomic_load(&s->next);
    n->next = (node*)old;  // ❌ Capability lost
    atomic_compare_exchange(&s->next, &old, (uintptr_t)n);
}
```

**Correct approach (fil-c compatible):**

```c
typedef struct {
    _Atomic(void*) next;  // ✅ Atomic capability pointer
    // Or equivalently:
    void* _Atomic next;   // ✅ Same thing
} lock_free_stack;

void push(lock_free_stack *s, node *n) {
    void *old = atomic_load(&s->next);
    n->next = (node*)old;  // ✅ Capability preserved
    atomic_compare_exchange(&s->next, &old, n);
}
```

**Key difference:** Use `void*_Atomic` instead of `atomic_uintptr_t` for pointer atomics.

---

## String Representation

### Three String Types

**Source:** `src/internal.h:175-202`

#### 1. Small Strings (Inline)

```c
typedef struct {
    char val_chr[MAX_SMALL_STRING];  // 8 bytes inline
    size_t chr_len;
} small_string;

// Creating
cell c;
c.tag = TAG_CSTR;
strcpy(c.val_chr, "short");
c.chr_len = 5;
```

**Fil-C impact:** ✅ No pointers involved.

#### 2. String Buffers (Heap)

```c
typedef struct {
    pl_refcnt refcnt;
    size_t len;
    char cstr[];  // ✅ Flexible array member
} strbuf;

typedef struct {
    strbuf *val_strb;   // ✅ Pointer to buffer
    uint32_t strb_off;  // Offset into buffer
    uint32_t strb_len;  // Length of this slice
} heap_string;

// Creating
strbuf *sb = malloc(sizeof(strbuf) + 100);  // ✅ Standard allocation
sb->refcnt = 1;
sb->len = 100;
strcpy(sb->cstr, "longer string");

cell c;
c.tag = TAG_CSTR;
c.val_strb = sb;    // ✅ Capability pointer
c.strb_off = 0;
c.strb_len = 13;
```

**Slicing:**

```c
// Create substring without copying
cell slice;
slice.tag = TAG_CSTR;
slice.val_strb = c.val_strb;      // ✅ Share same buffer
slice.strb_off = c.strb_off + 3;  // Offset into buffer
slice.strb_len = 5;                // New length
share_cell(&slice);                // Increment refcount
```

**Fil-C impact:** ✅ Perfect - slicing via offset+length is bounds-safe.

#### 3. External Slices

```c
typedef struct {
    char *val_str;      // ✅ Pointer to external memory
    uint64_t str_len;   // Length
} string_slice;

// Creating from C string
cell c;
c.tag = TAG_CSTR;
c.val_str = some_c_string;  // ✅ Capability with bounds
c.str_len = strlen(some_c_string);

// Creating substring
cell sub;
sub.tag = TAG_CSTR;
sub.val_str = c.val_str + 5;  // ✅ Pointer arithmetic preserves capability
sub.str_len = 10;
```

**Fil-C behavior:**
- Original `c.val_str` has capability covering entire C string
- `c.val_str + 5` maintains same capability bounds
- Runtime access checks via `str_len` prevent buffer overruns
- Fil-C's bounds checker validates every `val_str[i]` access

---

## Concrete Porting Roadmap

### Phase 1: FFI Handle Management (1 day)

**Estimated effort:** 6 hours coding + 2 hours testing

#### Tasks

1. **Add zptrtable infrastructure**
   ```diff
   --- a/src/bif_ffi.c
   +++ b/src/bif_ffi.c
   @@ -1,6 +1,11 @@
    #include <dlfcn.h>
    #include <ffi.h>
   +#include <stdfil.h>
    
   +static zptrtable *g_ffi_handles = NULL;
   +
   +static void ensure_ffi_handles(void) {
   +    if (!g_ffi_handles)
   +        g_ffi_handles = zptrtable_new_weak();
   +}
   ```

2. **Update dlopen** (src/bif_ffi.c:110)
   ```diff
   @@ -115,7 +120,9 @@ static bool bif_sys_dlopen_3(query *q)
        if (!handle)
            return throw_error(q, p3, q->st.m->error_ctx, "existence_error", "source_sink");
    
   +    ensure_ffi_handles();
   +    uintptr_t encoded = zptrtable_encode(g_ffi_handles, handle);
        cell tmp;
   -    make_uint(&tmp, (pl_int)(size_t)handle);
   +    make_uint(&tmp, encoded);
        tmp.flags |= FLAG_INT_HANDLE | FLAG_HANDLE_DLL;
   ```

3. **Update dlsym** (src/bif_ffi.c:123)
4. **Update dlclose** (src/bif_ffi.c:137)
5. **Update FFI struct registration** (4 functions)
6. **Update FFI call wrappers** (5 functions)

**Files modified:** 1 file (`src/bif_ffi.c`)  
**Lines changed:** ~30 additions, ~15 modifications

#### Testing

```bash
# Run FFI test suite
cd trealla
make test-ffi

# Specific tests
tpl tests/ffi_basic.pl
tpl tests/ffi_structs.pl
tpl tests/ffi_callbacks.pl
```

### Phase 2: Skiplist Integer Comparator (0.5 days)

**Estimated effort:** 2 hours coding + 2 hours testing

#### Tasks

1. **Add integer comparator**
   ```diff
   --- a/src/skiplist.c
   +++ b/src/skiplist.c
   @@ -54,6 +54,15 @@ static int default_cmpkey(const void *p1, const void *p2, const void *p, int *d
        return 0;
    }
    
   +int sl_int_cmpkey(const void *p1, const void *p2, const void *p, int *depth)
   +{
   +    uintptr_t i1 = (uintptr_t)p1;
   +    uintptr_t i2 = (uintptr_t)p2;
   +    if (i1 < i2) return -1;
   +    if (i1 > i2) return 1;
   +    return 0;
   +}
   +
   ```

2. **Export in header**
   ```diff
   --- a/src/skiplist.h
   +++ b/src/skiplist.h
   @@ -15,6 +15,7 @@ extern sl_iter *sl_findkey(skiplist *l, const void *key);
    // ...
    
   +extern int sl_int_cmpkey(const void *p1, const void *p2, const void *p, int *depth);
   ```

3. **Use in heap.c**
   ```diff
   --- a/src/heap.c
   +++ b/src/heap.c
   @@ -50,7 +50,7 @@ void init_queues(query *q)
        q->trails = calloc(1, sizeof(trail) * q->max_trails);
        q->choices = calloc(1, sizeof(choice) * q->max_choices);
   -    q->vars = sl_create(default_cmpkey, NULL, NULL);
   +    q->vars = sl_create(sl_int_cmpkey, NULL, NULL);
    }
   ```

**Files modified:** 3 files  
**Lines changed:** ~10 additions

#### Testing

```bash
# Variable-heavy tests
tpl tests/tests/test_findall.pl
tpl tests/tests/test_bagof.pl
tpl tests/tests/test_setof.pl

# Stress test
tpl -g "length(L, 10000), findall(X, member(X, L), _), halt"
```

### Phase 3: Build with Fil-C (0.5 days)

**Estimated effort:** 2 hours initial build + 2 hours fixing issues

#### Tasks

1. **Configure for fil-c**
   ```bash
   export CC=/path/to/fil-c/build/bin/clang
   export CFLAGS="-O2 -g"
   make clean
   make
   ```

2. **Fix any build errors**
   - Likely candidates: missing headers, type mismatches
   - Use `__FILC__` guard if needed:
     ```c
     #ifdef __FILC__
     #include <stdfil.h>
     #endif
     ```

3. **Run basic tests**
   ```bash
   make test
   ```

**Expected issues:**
- Compiler warnings about pointer casts (should be benign)
- Possible linker flag adjustments (like `-Wl,--version-script`)

### Phase 4: Integration Testing (1-2 days)

**Estimated effort:** Full day of testing + fixing edge cases

#### Test Categories

**1. Core functionality**
```bash
make test                    # Full test suite
make test-iso                # ISO Prolog compliance
```

**2. FFI-specific tests**
```prolog
% Test dlopen/dlsym/dlclose
test_ffi_lifecycle :-
    dlopen('libm.so.6', 2, H),
    dlsym(H, 'sqrt', Sqrt),
    call_ffi(Sqrt, [double], double, [4.0], R),
    R =:= 2.0,
    dlclose(H).

% Test struct marshalling
test_ffi_struct :-
    register_ffi_struct('point', [int, int]),
    dlopen('libexample.so', 2, H),
    dlsym(H, 'distance', Dist),
    call_ffi(Dist, [ptr, ptr], double, [struct([10,20]), struct([30,40])], D),
    D =:= 50.0,
    dlclose(H).
```

**3. Variable management**
```prolog
% Stress test slot allocation
test_many_vars :-
    length(L, 1000),
    findall(X-Y-Z, (member(X,L), Y=X, Z=Y), Triples),
    length(Triples, 1000).
```

**4. Memory safety**
```prolog
% Should NOT crash with bounds violations
test_string_bounds :-
    atom_chars(hello, Chars),
    append(Chars, [world], _),
    string_concat("foo", "bar", _).
```

**5. Concurrent operations** (if USE_THREADS enabled)
```prolog
test_threading :-
    thread_create(write('A'), A),
    thread_create(write('B'), B),
    thread_join(A),
    thread_join(B).
```

#### Success Criteria

- ✅ All core tests pass (make test)
- ✅ No capability violations (no fil-c traps)
- ✅ FFI roundtrips work correctly
- ✅ No memory leaks (valgrind or fil-c leak checker)
- ✅ Performance within 2x of native (acceptable for fil-c)

---

## Comparison to Other Prolog Systems

### SWI-Prolog

**Architecture:** Tagged pointers with NaN-boxing for floats

```c
// SWI-Prolog term representation
typedef uintptr_t word;

#define TAG_VAR      0x00
#define TAG_ATTVAR   0x01
#define TAG_FLOAT    0x02  // NaN-boxed double
#define TAG_INTEGER  0x03
#define TAG_ATOM     0x05
#define TAG_STRING   0x06
#define TAG_COMPOUND 0x07

// Every term operation manipulates pointer bits
#define valPtr(w)   ((Word)((w) & ~TAG_MASK))
#define tagEx(w)    ((w) & TAG_MASK)
```

**Fil-C porting difficulty:** 🔴 **Very Hard**

- Every term operation needs `zorptr`/`zandptr`/`zretagptr`
- NaN-boxing requires special float encoding (possible with `zptrtable` but slow)
- Estimated effort: 2-3 weeks

### YAP (Yet Another Prolog)

**Architecture:** Similar to SWI, tagged pointers

```c
typedef CELL Term;

#define MkAtomTerm(a)    (((CELL)(a)) << TAG_SHIFT | TAG_ATOM)
#define AtomOfTerm(t)    ((Atom)((t) >> TAG_SHIFT))
```

**Fil-C porting difficulty:** 🔴 **Very Hard**

- Similar issues to SWI-Prolog
- Heavy use of pointer tagging throughout
- Estimated effort: 2-3 weeks

### GNU Prolog

**Architecture:** Tagged pointers with compile-time tag configuration

```c
#define TAG_SIZE_LOW  2
#define TAG_MASK_LOW  0x3

#define Tag_Of(w)     ((w) & TAG_MASK_LOW)
#define UnTag_INT(w)  ((w) >> TAG_SIZE_LOW)
```

**Fil-C porting difficulty:** 🟡 **Hard**

- Simpler tagging scheme than SWI/YAP
- Still requires pointer bit manipulation throughout
- Estimated effort: 1-2 weeks

### Trealla Prolog

**Architecture:** Explicit tags, untagged pointers

```c
typedef struct cell_ {
    uint8_t tag;              // ✅ No bit manipulation
    union {
        void *ptr;            // ✅ Clean pointers
        int64_t integer;
    };
} cell;
```

**Fil-C porting difficulty:** 🟢 **Easy**

- No pointer tagging
- Standard memory allocation
- Only FFI boundary needs attention
- Estimated effort: 3-4 days

### Comparison Table

| System | Tagging | Allocator | FFI | Fil-C Effort |
|--------|---------|-----------|-----|--------------|
| **SWI-Prolog** | NaN-boxed pointers | Stacks + global heap | Complex | 2-3 weeks |
| **YAP** | Tagged pointers | Custom allocator | Medium | 2-3 weeks |
| **GNU Prolog** | Tagged pointers | WAM stacks | Medium | 1-2 weeks |
| **Trealla** | Explicit tags | Standard malloc | Simple | **3-4 days** |

---

## Risk Mitigation Strategies

### Risk #1: Performance Overhead

**Concern:** Pointer table lookups add overhead to FFI calls

**Mitigation:**

1. **Benchmark FFI performance**
   ```c
   // Measure encode/decode overhead
   clock_t start = clock();
   for (int i = 0; i < 1000000; i++) {
       uintptr_t enc = zptrtable_encode(table, ptr);
       void *dec = zptrtable_decode(table, enc);
   }
   clock_t end = clock();
   // Expected: ~50ns per encode/decode on modern CPU
   ```

2. **FFI calls are infrequent**
   - Typical Prolog program: <1% time in FFI
   - Encode/decode overhead: ~100ns total
   - Function call overhead: microseconds to milliseconds
   - Overhead ratio: <0.01%

3. **Overall fil-c overhead acceptable**
   - Measured fil-c overhead: 1.5x - 4x (from upstream docs)
   - Primarily from bounds checks, not pointer tables
   - Trealla's clean design minimizes additional overhead

**Validation:**

```bash
# Benchmark native vs fil-c
time tpl benchmarks/queens.pl          # Native
time tpl-filc benchmarks/queens.pl     # Fil-C version

# FFI-heavy benchmark
time tpl benchmarks/ffi_stress.pl
time tpl-filc benchmarks/ffi_stress.pl
```

### Risk #2: Pointer Table Growth

**Concern:** `g_ffi_handles` grows unbounded if libraries never closed

**Mitigation:**

1. **Use weak pointer table**
   ```c
   g_ffi_handles = zptrtable_new_weak();  // ✅ Already planned
   ```
   - Weak tables don't prevent GC
   - Handles are explicitly managed (dlopen/dlclose)

2. **Add table cleanup on dlclose**
   ```c
   static bool bif_sys_dlclose_1(query *q) {
       ensure_ffi_handles();
       uintptr_t encoded = get_smalluint(p1);
       void *handle = zptrtable_decode(g_ffi_handles, encoded);
       dlclose(handle);
       
       // Remove from table (if API supports it)
       zptrtable_remove(g_ffi_handles, encoded);
       
       return true;
   }
   ```

3. **Monitor table size**
   ```c
   #ifdef DEBUG_FFI
   size_t table_size = zptrtable_size(g_ffi_handles);
   if (table_size > 1000)
       fprintf(stderr, "Warning: FFI handle table has %zu entries\n", table_size);
   #endif
   ```

**Typical usage:**
- Small programs: 1-5 libraries loaded
- Large programs: 10-50 libraries
- Table size: <1KB even for large programs

### Risk #3: Skiplist Performance

**Concern:** Custom comparator slower than default

**Mitigation:**

1. **Benchmark skiplist operations**
   ```c
   skiplist *sl_default = sl_create(default_cmpkey, NULL, NULL);
   skiplist *sl_int = sl_create(sl_int_cmpkey, NULL, NULL);
   
   // Insert 1M entries
   clock_t start = clock();
   for (int i = 0; i < 1000000; i++)
       sl_app(sl_int, (void*)(uintptr_t)i, (void*)(uintptr_t)i);
   clock_t end = clock();
   // Expected: <1% difference from default
   ```

2. **Compiler optimization**
   - Comparator function is small (3 lines)
   - Modern compilers inline it automatically
   - No performance difference in practice

3. **Alternative data structure**
   - If skiplist proves problematic, Trealla also has:
     - Hash tables (`src/hashtable.c`)
     - Red-black trees (could be added)
   - For slot tracking, hash table might be better anyway

**Expected outcome:** No measurable performance difference.

### Risk #4: Unforeseen Capability Violations

**Concern:** Other pointer operations might break that we haven't identified

**Mitigation:**

1. **Comprehensive testing**
   ```bash
   # Run full test suite under fil-c
   make test
   make test-iso
   make test-ffi
   make test-threads
   ```

2. **Enable fil-c diagnostics**
   ```bash
   export FILC_TRAP_ON_BOUNDS=1        # Trap on bounds violations
   export FILC_TRAP_ON_TYPE=1          # Trap on type errors
   export FILC_VERBOSE_TRAPS=1         # Detailed error messages
   ```

3. **Code review checklist**
   - [ ] No `(uintptr_t)ptr` → `(void*)int` roundtrips
   - [ ] No pointer bit manipulation (`ptr & ~0x7`)
   - [ ] No pointer comparison for ordering (except via comparator)
   - [ ] No assumptions about pointer representation
   - [ ] All pointer tables use `zptrtable` API

4. **Static analysis**
   ```bash
   # Scan for problematic patterns
   git grep -n '(void\s*\*)\s*(' src/*.c  # Pointer casts
   git grep -n 'uintptr_t' src/*.c        # Integer-pointer conversions
   git grep -n '\s&\s~' src/*.c           # Bit masking
   ```

**Validation process:**
1. Fix all identified issues
2. Run test suite → note any failures
3. Investigate failures → identify pattern
4. Apply fix → re-test
5. Repeat until clean

### Risk #5: Upstream Changes

**Concern:** New Trealla versions might introduce incompatible code

**Mitigation:**

1. **Document all changes**
   - Create detailed `ports/trealla-analysis.md` (this document)
   - Maintain `ports/patch/trealla.patch` with inline comments
   - Track rationale for each change

2. **Minimal patch surface**
   - Only ~30-50 lines of changes
   - Changes localized to 2-3 files
   - Easy to forward-port to new versions

3. **Automated testing**
   - CI pipeline runs test suite on every Trealla update
   - Failures indicate new incompatible code
   - Review new code for fil-c patterns

4. **Upstream collaboration**
   - Submit patches upstream with `#ifdef __FILC__` guards
   - Example:
     ```c
     #ifdef __FILC__
         ensure_ffi_handles();
         uintptr_t encoded = zptrtable_encode(g_ffi_handles, handle);
         make_uint(&tmp, encoded);
     #else
         make_uint(&tmp, (pl_int)(size_t)handle);
     #endif
     ```
   - If accepted, reduces maintenance burden

**Expected maintenance:** ~1 hour per Trealla release to forward-port patches.

---

## Conclusion

Trealla Prolog is **exceptionally well-suited** for fil-c porting due to its:

1. ✅ **Clean architecture** - no pointer tagging, no custom allocators
2. ✅ **Standard C practices** - portable, no assembly, no intrinsics  
3. ✅ **Minimal FFI boundary** - only ~12 functions need pointer tables
4. ✅ **Index-based design** - frames/contexts use integers, not encoded pointers
5. ✅ **Explicit bounds tracking** - strings store length separately

**Total porting effort:** 3-4 days
- FFI pointer tables: 1 day
- Skiplist comparator: 0.5 days
- Build integration: 0.5 days
- Testing/validation: 1-2 days

**Maintenance effort:** ~1 hour per upstream release

**Risk level:** 🟢 Low - cleanest Prolog implementation for capability-based C

**Next steps:**
1. Clone Trealla and build with fil-c compiler
2. Apply FFI pointer table changes
3. Add skiplist integer comparator
4. Run test suite and fix any issues
5. Create Nix package in filnix/ports/

---

## References

- **Trealla Prolog:** https://github.com/trealla-prolog/trealla
- **Fil-C:** https://github.com/pizlonator/fil-c
- **Fil-C Porting Patterns:** `ports/analysis.md` (this repository)
- **Fil-C Port Details:** `ports/details.md` (this repository)

## Appendix: Patch Preview

**Estimated patch size:** ~80 lines (additions + modifications)

```diff
diff --git a/src/bif_ffi.c b/src/bif_ffi.c
index abc1234..def5678 100644
--- a/src/bif_ffi.c
+++ b/src/bif_ffi.c
@@ -1,6 +1,11 @@
 #include <dlfcn.h>
 #include <ffi.h>
+#include <stdfil.h>
 
+static zptrtable *g_ffi_handles = NULL;
+
+static void ensure_ffi_handles(void) {
+    if (!g_ffi_handles) g_ffi_handles = zptrtable_new_weak();
+}
 
 static bool bif_sys_dlopen_3(query *q)
 {
@@ -115,7 +120,9 @@ static bool bif_sys_dlopen_3(query *q)
     if (!handle)
         return throw_error(q, p3, q->st.m->error_ctx, "existence_error", "source_sink");
 
+    ensure_ffi_handles();
+    uintptr_t encoded = zptrtable_encode(g_ffi_handles, handle);
     cell tmp;
-    make_uint(&tmp, (pl_int)(size_t)handle);
+    make_uint(&tmp, encoded);
     tmp.flags |= FLAG_INT_HANDLE | FLAG_HANDLE_DLL;
     
     return unify(q, p3, p3_ctx, &tmp, q->st.curr_frame);

diff --git a/src/skiplist.c b/src/skiplist.c
index abc1234..def5678 100644
--- a/src/skiplist.c
+++ b/src/skiplist.c
@@ -54,6 +54,13 @@ static int default_cmpkey(const void *p1, const void *p2, const void *p, int *d
     return 0;
 }
 
+int sl_int_cmpkey(const void *p1, const void *p2, const void *p, int *depth)
+{
+    uintptr_t i1 = (uintptr_t)p1, i2 = (uintptr_t)p2;
+    if (i1 < i2) return -1;
+    if (i1 > i2) return 1;
+    return 0;
+}

diff --git a/src/skiplist.h b/src/skiplist.h
index abc1234..def5678 100644
--- a/src/skiplist.h
+++ b/src/skiplist.h
@@ -15,6 +15,7 @@ extern sl_iter *sl_findkey(skiplist *l, const void *key);
 extern int sl_set(skiplist *l, const void *key, const void *val);
 // ...
 
+extern int sl_int_cmpkey(const void *p1, const void *p2, const void *p, int *depth);

diff --git a/src/heap.c b/src/heap.c
index abc1234..def5678 100644
--- a/src/heap.c
+++ b/src/heap.c
@@ -50,7 +50,7 @@ void init_queues(query *q)
     q->trails = calloc(1, sizeof(trail) * q->max_trails);
     q->choices = calloc(1, sizeof(choice) * q->max_choices);
-    q->vars = sl_create(default_cmpkey, NULL, NULL);
+    q->vars = sl_create(sl_int_cmpkey, NULL, NULL);
 }
```

**Total:** ~30 additions, ~15 modifications, 3 files touched.
