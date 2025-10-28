# Fil-C Ports

This directory contains patches and tooling for porting upstream software to Fil-C.

- `patch/` - Patches for 71 projects (3.0MB)
- `extract-patch.sh` - Script to extract patches for a single project
- `Makefile` - Parallel patch generation (`make -j20`)

## What's excluded

To keep patches minimal and maintainable, we exclude:

- Autotools generated files: `configure`, `Makefile.in`, `aclocal.m4`, `config.h.in`
- Build helper directories: `build-aux/*`, `conftools/*`
- Repository infrastructure: `.github/*`, `.gitignore`, CI configs
- Gettext/i18n generated files: `po/Makefile.in.in`, etc.
- Fil-C test files: `fil-tests/*`

## Regenerating patches

If you need to update patches from a newer fil-c commit:

```bash
# Requires ~/fil-c-projects checkout
make clean
make -j20
```

This will regenerate all patches from the git history.

## Applying patches in Nix

### How nixpkgs applies patches

The `stdenv.mkDerivation` patch phase uses GNU patch with these defaults:

- **Strip level**: `-p1` (removes leading directory from patch paths)
- **Fuzz tolerance**: `--fuzz=2` (GNU patch's built-in default)

This means patches can tolerate ~2 lines of shifted context, making them work across minor version changes where line numbers have moved slightly.

### Customizing patch behavior

You can override the default patch flags:

```nix
stdenv.mkDerivation {
  patches = [ ./my-patch.patch ];

  # Disable fuzz for strict matching
  patchFlags = [ "-p1" "--fuzz=0" ];

  # Prevent .orig backup files when fuzzy matching succeeds
  patchFlags = [ "-p1" "--no-backup-if-mismatch" ];
}
```

### Using the patches.nix attrset

The `patches.nix` file provides an attribute set of all ported projects:

```nix
{
  simdutf = { version = "5.5.0"; patches = [./patch/simdutf-5.5.0.patch]; };
  openssl = { version = "3.3.1"; patches = [./patch/openssl-3.3.1.patch]; };
  # ... 76 total projects
}
```

## Common patch patterns

The patches use several patterns to make code Fil-C compatible.
Here are examples from various projects:

### Pointer tables

The most common pattern: using `zptrtable` to convert pointers to integers safely.

**Perl's `builtin.c`** - Storing callback pointers as integers:

```c
+#include <stdfil.h>
+
+static zptrtable* builtin_ptrtable;
+
+static void construct_ptrtable(void) __attribute__((constructor));
+static void construct_ptrtable(void)
+{
+    builtin_ptrtable = zptrtable_new();
+}

 static OP *ck_builtin_const(pTHX_ OP *entersubop, GV *namegv, SV *ckobj)
 {
-    const struct BuiltinFuncDescriptor *builtin = NUM2PTR(..., SvUV(ckobj));
+    const struct BuiltinFuncDescriptor *builtin = zptrtable_decode(builtin_ptrtable, SvUV(ckobj));
```

**Python's `longobject.c`** - Converting C pointers to Python ints:

```c
+#include <stdfil.h>
+
+static zexact_ptrtable* ptrtable;
+
+static void construct_ptrtable(void) __attribute__((constructor));
+static void construct_ptrtable(void)
+{
+    ptrtable = zexact_ptrtable_new();
+}

 PyObject *
 PyLong_FromVoidPtr(void *p)
 {
-    return PyLong_FromUnsignedLong((unsigned long)(uintptr_t)p);
+    return PyLong_FromUnsignedLong((unsigned long)(uintptr_t)zexact_ptrtable_encode(ptrtable, p));
 }

 void *
 PyLong_AsVoidPtr(PyObject *vv)
 {
     long x;
     // ... extract x from Python long ...
-    return (void *)x;
+    return (void *)zexact_ptrtable_decode(ptrtable, x);
 }
```

**Note**: `zptrtable` is for general use, `zexact_ptrtable` preserves exact pointer identity (needed for `==` comparisons).

Sometimes storing as `void*` and casting on access is simpler than pointer tables.

**Git's `parse-options.h`** - Changing defval storage type:

```c
 struct option {
     // ...
     parse_opt_cb *callback;
-    intptr_t defval;
+    void *defval;  // Store as pointer instead of integer
 };

 #define OPT_SET_INT_F(s, l, v, h, i, f) { \
     // ...
-    .defval = (i), \
+    .defval = (void *)(i),  // Cast to void* when initializing
 }
```

**Git's `parse-options.c`** - Casting back to integer:

```c
 case OPTION_SET_INT:
-    *(int *)opt->value = unset ? 0 : opt->defval;
+    *(int *)opt->value = unset ? 0 : (intptr_t)opt->defval;
```

### Symbol versioning

Libraries with symbol versioning need Fil-C-specific directives.

**xz's `common.h`** - Conditional symbol versioning:

```c
+#elif __PIZLONATOR_WAS_HERE__
+    #define LZMA_SYMVER_API(extnamever, type, intname) \
+        __asm__(".filc_symver " #intname "," extnamever); \
+        extern LZMA_API(type) intname
 #else
     #define LZMA_SYMVER_API(extnamever, type, intname) \
         __asm__(".symver " #intname "," extnamever); \
```

**Note**: `__PIZLONATOR_WAS_HERE__` is defined by the Fil-C compiler.

### Alignment fixes

Some types need explicit alignment for Fil-C's capability system.

**xz's `file_io.h`** - Adding alignment attribute:

```c
-typedef union {
+typedef union __attribute__((aligned(16))) {
     uint8_t u8[IO_BUFFER_SIZE];
     uint32_t u32[IO_BUFFER_SIZE / sizeof(uint32_t)];
     uint64_t u64[IO_BUFFER_SIZE / sizeof(uint64_t)];
 } io_buf;
```
