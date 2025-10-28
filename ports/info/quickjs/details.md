# QuickJS (no version in patch)

## Summary
Minimal changes to make QuickJS work with Fil-C: disable threaded dispatch, fix pointer tagging, add qsort_r compatibility.

## Fil-C Compatibility Changes

### Makefile
```make
+CONFIG_CLANG=y
-  HOST_CC=clang
-  CC=$(CROSS_PREFIX)clang
+  HOST_CC=$(PWD)/../../../build/bin/clang
+  CC=$(CROSS_PREFIX)$(PWD)/../../../build/bin/clang
```
**Hardcodes Fil-C compiler path** - should use environment variable instead

### Interpreter Dispatch (quickjs.c)
```c
-#if defined(EMSCRIPTEN)
+#if defined(EMSCRIPTEN) || defined(__PIZLONATOR_WAS_HERE__)
 #define DIRECT_DISPATCH  0
```
**Disables computed goto dispatch** - Fil-C doesn't support `&&label` address-of-label extension

### Property Autoinit (quickjs.c)
**Problem:** `realm_and_id` stored `JSContext*` with 2-bit ID tag in low bits

```c
 typedef struct JSProperty {
     union {
         struct {
-            uintptr_t realm_and_id;
+            void* realm_and_id;
             void *opaque;
         } init;
     } u;
 } JSProperty;
```

**Helper functions:**
```c
 static JSContext *js_autoinit_get_realm(JSProperty *pr) {
-    return (JSContext *)(pr->u.init.realm_and_id & ~3);
+    return (JSContext *)((uintptr_t)pr->u.init.realm_and_id & ~3);
 }
 
 static JSAutoInitIDEnum js_autoinit_get_id(JSProperty *pr) {
-    return pr->u.init.realm_and_id & 3;
+    return (uintptr_t)pr->u.init.realm_and_id & 3;
 }
```

**Setting:**
```c
-    pr->u.init.realm_and_id = (uintptr_t)JS_DupContext(ctx);
-    pr->u.init.realm_and_id |= id;
+    pr->u.init.realm_and_id = JS_DupContext(ctx);
+    pr->u.init.realm_and_id = (void*)((uintptr_t)pr->u.init.realm_and_id | id);
```

**Pattern:** Store as `void*`, cast to `uintptr_t` for bit manipulation, cast back

### qsort_r Compatibility (cutils.c)
```c
+#ifdef __PIZLONATOR_WAS_HERE__
+void rqsort(void *base, size_t nmemb, size_t size,
+            int (*cmp)(const void *, const void *, void *),
+            void *arg)
+{
+    qsort_r(base, nmemb, size, cmp, arg);
+}
```
**Wrapper for BSD-style qsort_r** (used elsewhere in QuickJS)

### Headers
```c
+#include <stdfil.h>
```

## Build Artifact Bloat
None.

## Assessment
- **Patch quality**: Mostly clean, Makefile hack is ugly
- **Actual changes**: Minor (3 functional changes)
- **Correctness**: Pointer tagging approach seems sound
- **Issue**: Hardcoded compiler path in Makefile is non-portable
