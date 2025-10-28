# libpas: Phil's Awesome System

## Overview

**libpas** (Phil's Awesome System) is a configurable memory allocator toolkit designed by Filip Pizlo for WebKit. It serves as the foundation for both WebKit's memory management and Fil-C's garbage collection runtime.

- **WebKit repository**: https://github.com/WebKit/WebKit/tree/main/Source/bmalloc/libpas
- **Author**: Filip Pizlo (led WebKit's GC and compiler development at Apple)
- **Purpose**: Highly configurable, efficient memory allocation with security features

## libpas in WebKit

### Purpose

In WebKit, libpas replaced bmalloc and provides:
- **fastMalloc API**: General-purpose memory allocation
- **IsoHeap<>**: Type-isolated heaps for security (prevents type confusion)
- **Gigacage API**: Memory cages for sandboxing
- **JIT heap**: Executable memory allocation for JavaScriptCore

Performance impact: ~2% Speedometer2 speed-up, ~8% memory improvement.

### Architecture: Three Core Allocator Types

#### 1. Segregated Heap (Fast Path)

- **Simple segregated storage**: Each size class has pages containing only objects of that size
- **Extremely fast**: No atomic operations or fences in typical allocation/deallocation
- **Thread-Local Caches (TLCs)**: Lock-free operation per thread
- **Use case**: isoheaps and frequent allocations

**How it works:**
- Objects grouped by size class
- Per-thread caches eliminate contention
- When TLC runs out, refill from shared page
- Deallocation logs batched for efficiency (~1000 objects)

#### 2. Bitfit Heap (Space-Efficient)

- **First-fit allocation**: Uses bit-per-minalign-granule
- **Space-efficient but slower** than segregated
- **Bitmaps**: `free_bits` and `object_end_bits` track allocations
- **Use case**: "marge" allocations (medium-large sizes, hundreds of KB)

**How it works:**
- Scans free_bits to find contiguous free region
- Sets object_end_bits at allocation boundary
- More compact than segregated for variable sizes
- Good middle ground between speed and space

#### 3. Large Heap (Flexible)

- **Cartesian-tree-based first-fit** allocator
- **Handles arbitrary-sized objects**
- **Type information tracking** for safety
- **Large map** for object metadata
- **Use case**: Very large allocations and type safety guarantees

### Key Architectural Features

#### Memory Efficiency

- **Physical page sharing**: Returns empty pages to OS via decommit (usually after 300ms)
- **Scavenger thread**: Periodic cleanup runs every 100ms
- **Deferred decommit**: Coalesces adjacent page returns into single syscalls
- **Compact pointers**: 24-bit pointers for metadata (128MB compact reservation)

#### Performance

- **Fine-grained locking**: Intricate lock dancing to minimize contention
- **Lock-free structures**: Megapage tables and page header tables for fast lookups
- **TLC deallocation log**: Amortizes lock acquisition across ~1000 objects
- **View caches**: Thread-local caches reduce global heap access

#### Configurability

- **Heap configs** (`pas_heap_config`): Control page sizes, minalign, security-performance trade-offs
- **C template programming**: Uses `always_inline` for specialization without C++
- **Multiple page configs**: small/medium segregated, small/medium/marge bitfit
- **Runtime tuning**: Adjust behavior based on workload

#### Type Safety & Security

- **External metadata**: Never stores free object info inside the object (prevents use-after-free exploits)
- **Type awareness**: Prevents type confusion in memory reuse
- **Isoheaping**: Supports thousands of separate type-isolated heaps efficiently
- **PGM (Probabilistic Guard Malloc)**: Optional guard pages for catching bugs

## libpas in Fil-C

Fil-C extends libpas to create **FUGC** (Fil's Unbelievable Garbage Collector), transforming it from a manual memory manager into a complete memory-safety runtime.

### Major Extensions

#### 1. Verse Heap Configuration

Fil-C adds a completely new heap configuration called `verse_heap` designed specifically for garbage collection:

**Key parameters:**
```c
// 16-byte alignment for InvisiCaps
#define VERSE_HEAP_MIN_ALIGN_SHIFT 4u

// Chunk sizes for mark bit organization
#define VERSE_HEAP_CHUNK_SIZE_SHIFT (PAGE_SIZE_SHIFT + MIN_ALIGN_SHIFT + 3u)
#define VERSE_HEAP_SMALL_SEGREGATED_PAGE_SIZE 16384
#define VERSE_HEAP_MEDIUM_SEGREGATED_PAGE_SIZE CHUNK_SIZE
```

**Features:**
- **Mark bits integration**: First page of each chunk stores mark bits for the entire chunk
- **Object set tracking**: `verse_heap_object_set` for tracking objects needing finalization
- **Live bytes tracking**: `verse_heap_live_bytes` triggers garbage collection
- **Sweep support**: Parallel sweeping with `verse_heap_sweep_range()`
- **Black allocation modes**: Objects allocated during GC are pre-marked

#### 2. FUGC Garbage Collector

The runtime adds an accurate concurrent garbage collector built on verse_heap:

**Collector characteristics:**
- **Parallel concurrent marking**: Multiple GC threads mark in parallel with mutators
- **On-the-fly/incremental**: No global stop-the-world pauses
- **Grey-stack Dijkstra**: Store barrier only (no load barrier needed)
- **Soft handshakes**: Threads scan stacks asynchronously
- **Accurate/precise**: Compiler tracks all pointer locations exactly
- **Non-moving**: Simplifies concurrent access (no relocation)

**GC heaps:**
```c
extern pas_heap* fugc_default_heap;       // Normal allocations
extern pas_heap* fugc_destructor_heap;    // Objects with destructors
extern pas_heap* fugc_census_heap;        // Census-tracked objects
extern pas_heap* fugc_finalizer_heap;     // Objects needing finalization
extern verse_heap_object_set* fugc_destructor_set;
```

#### 3. InvisiCaps Support

Every allocation in Fil-C carries invisible capabilities:

- **Auxiliary allocation**: Metadata stored separately via `object->aux`
- **Bounds and permissions**: Upper/lower bounds checked on every access
- **Free tracking**: `FILC_OBJECT_FLAG_GLOBAL` flag prevents premature GC
- **Capability repointing**: Freed object capabilities redirected to free singleton
- **Shadow memory**: Capabilities stored separately from pointer values

#### 4. The Sandwich Architecture

Fil-C layers on top of libpas:

```
[User Code & Libraries - Fil-C compiled]
    ↓
[libc.so - musl/glibc compiled with Fil-C]
    ↓
[libpizlo.so - Runtime (includes libpas + FUGC)]
    ↓
[libyoloc.so - musl/glibc compiled with normal C]
    ↓
[Linux Kernel]
```

**libpizlo.so contains:**
- libpas with verse_heap configuration
- FUGC garbage collector
- Safepoint infrastructure (pollchecks)
- Capability checking (bounds validation)
- Signal handling (fault recovery)
- System call wrappers (validation)

### Comparison: WebKit vs Fil-C Usage

| Aspect | WebKit libpas | Fil-C libpas |
|--------|---------------|--------------|
| **Primary goal** | Fast malloc/isoheap replacement | Garbage collection foundation |
| **Heap config** | bmalloc_heap, iso_heap, jit_heap | verse_heap (new) |
| **Memory reclamation** | Manual free + scavenger | Accurate concurrent GC |
| **Metadata** | External for free safety | InvisiCaps for complete safety |
| **Object tracking** | Per-heap statistics | GC mark bits, object sets |
| **Concurrency** | Lock-free TLCs | GC threads + store barriers |
| **Type safety** | Isoheaps prevent type confusion | Capabilities prevent all memory errors |
| **Performance goal** | Minimize allocation overhead | Guarantee memory safety |
| **Use case** | Browser engine | Memory-safe C/C++ execution |

### What Fil-C Retains from libpas

- Segregated/bitfit/large heap algorithms
- TLC (thread-local cache) architecture
- Scavenger for returning memory to OS
- Page sharing and decommit infrastructure
- Megapage and page header tables
- Fine-grained locking mechanisms
- External metadata storage
- Compact pointer representation

### What Fil-C Adds to libpas

- **verse_heap**: New heap configuration optimized for GC
- **Mark bit infrastructure**: Chunk-based mark bits for parallel sweep
- **Object sets**: Track objects needing finalization/destruction
- **GC triggers**: Live bytes threshold monitoring
- **Sweep infrastructure**: Parallel sweeping across pages
- **filc_runtime**: Capability checking, safepoints, GC coordination
- **FUGC**: Complete concurrent garbage collector implementation
- **InvisiCap integration**: Shadow memory and capability tracking

## The Genius of the Design

The brilliance is that Fil-C **reuses** libpas's battle-tested allocation infrastructure while **layering** garbage collection on top through the verse_heap configuration. This makes libpas serve an entirely different purpose (complete memory safety) than its original WebKit role (fast manual memory management).

**Why this works:**
1. **Solid foundation**: libpas already handles complex allocation scenarios efficiently
2. **Configurable by design**: libpas was built to support multiple heap configurations
3. **External metadata**: libpas's security features align with capability requirements
4. **Thread-local caching**: TLCs reduce GC coordination overhead
5. **Production-proven**: Years of WebKit usage validate the core algorithms

The result: A memory-safe C/C++ runtime that didn't need to reinvent allocation algorithms, just extend them with GC semantics.

## Key Files in Fil-C's libpas

- `libpas/src/libpas/verse_heap_ue.h` - Verse heap configuration
- `libpas/src/libpas/verse_heap_config_ue.h` - Configuration parameters
- `libpas/src/libpas/fugc.c` - Garbage collector implementation
- `libpas/src/libpas/filc_runtime.c` - Core runtime (unsafe C parts)
- `filc/src/runtime.c` - Memory-safe runtime parts
- `filc/include/stdfil.h` - Fil-C intrinsics and reflection API
- `filc/include/pizlonated_runtime.h` - Internal APIs for libc
- `filc/include/pizlonated_syscalls.h` - Memory-safe syscall wrappers

## Resources

- [libpas ReadMe](https://github.com/WebKit/WebKit/blob/main/Source/bmalloc/libpas/ReadMe.md) - Original WebKit documentation
- [Fil-C repository](https://github.com/pizlonator/fil-c) - Extended libpas with GC
- [WebKit Source](https://github.com/WebKit/WebKit/tree/main/Source/bmalloc/libpas) - Upstream libpas
