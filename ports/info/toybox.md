# Toybox 8.12

## Summary
Toybox is an all-in-one Linux command-line tool suite (like busybox). The Fil-C port disables vfork, adds signal safety checks, and fixes pointer/integer type conversions.

## Fil-C Compatibility Changes

### vfork Replacement

**lib/lib.h:**
```c
 #define XVFORK() xvforkwrap(vfork())
+#define XVFORK() xvforkwrap(({ errno = ENOSYS; -1; }))
```

vfork not available in Fil-C's safe glibc, so XVFORK macro now returns error instead.

**toys/other/oneit.c:**
```c
-  if (!vfork()) reboot(action);
+  if (!fork()) reboot(action);
 
-    pid = XVFORK();
+    pid = fork();
```

Direct vfork calls replaced with fork.

### Signal Handler Safety

**lib/portability.c:**
```c
+#include <stdfil.h>
+
-    if (signames[i].num != SIGKILL) xsignal(signames[i].num, handler);
+    if (signames[i].num != SIGKILL && !zis_unsafe_signal_for_handlers(signames[i].num))
+      xsignal(signames[i].num, handler);
```

Fil-C runtime reserves certain signals. `zis_unsafe_signal_for_handlers()` checks if a signal number is safe to install handlers for.

### Type Conversion in ls.c

**toys/posix/ls.c:**
```c
-static void zprint(int zap, char *pat, int len, unsigned long arg)
+static void zprint(int zap, char *pat, int len, void *arg)
```

Converted format helper from taking `unsigned long` to `void*`. All call sites updated to cast appropriately:

```c
-    if (FLAG(i)) zprint(zap, "lu ", totals[1], st->st_ino);
+    if (FLAG(i)) zprint(zap, "lu ", totals[1], (void*)st->st_ino);

-      zprint(zap, "s ", totals[6], (unsigned long)tmp);
+      zprint(zap, "s ", totals[6], tmp);

-      zprint(zap, "ld", totals[2]+1, st->st_nlink);
+      zprint(zap, "ld", totals[2]+1, (void*)st->st_nlink);
```

## Build Artifacts Filtered

The original 5447-line patch included:
- **kconfig/** directory (5304 lines): GPL'd configuration system from Linux kernel
  - 7 C files implementing `make menuconfig` interface
  - Doesn't go into toybox binary, just build-time editor
- **good-config**: Pre-configured .config file

These are now excluded, reducing patch to 143 lines.

## Assessment
- **Patch quality**: Clean after filtering kconfig bloat
- **Actual changes**: vfork replacement, signal safety, type conversions
- **Complexity**: Straightforward compatibility fixes
