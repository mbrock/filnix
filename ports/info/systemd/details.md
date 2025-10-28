# systemd 256.4

## Summary
Major rework of sd-bus error map infrastructure to avoid ELF section magic, plus signal handling safety and build system fixes.

## Fil-C Compatibility Changes

### Build System (meson.build)
```diff
-                     '-Wl,--version-script=' + libsystemd_sym_path],
+                     '--version-script=' + libsystemd_sym_path],
```
**Repeated 3 times** for libsystemd, libudev, and NSS modules  
**Same as seatd** - removes `-Wl,` prefix

### Signal Handling Safety (src/basic/signal-util.c)
```c
+#include <stdfil.h>

 int reset_all_signal_handlers(void) {
     for (int sig = 1; sig < _NSIG; sig++) {
         if (IN_SET(sig, SIGKILL, SIGSTOP))
             continue;
 
+        if (zis_unsafe_signal_for_handlers(sig))
+            continue;
+
         r = RET_NERRNO(sigaction(sig, &sa, NULL));
```

**Why needed:**
- Some signals may be reserved by Fil-C runtime
- `zis_unsafe_signal_for_handlers` prevents systemd from clobbering them
- Avoids runtime conflicts

### ELF Section Magic Removal

**Original design:**
```c
#define BUS_ERROR_MAP_ELF_REGISTER                                      \
        _section_("SYSTEMD_BUS_ERROR_MAP")                              \
        _used_                                                          \
        _retain_
```
- Error maps placed in special ELF section
- Linker provides `__start_SYSTEMD_BUS_ERROR_MAP` / `__stop_SYSTEMD_BUS_ERROR_MAP`
- Iteration over section at runtime to find all error maps

**Problem with Fil-C:**
- ELF section iteration doesn't preserve pointer capabilities
- Section boundaries are raw addresses, not capability-bearing pointers

**Solution:** Inline all error maps

**src/libsystemd/sd-bus/bus-error.c**
```c
-BUS_ERROR_MAP_ELF_REGISTER const sd_bus_error_map bus_standard_errors[] = {
+const sd_bus_error_map bus_standard_errors[] = {
     SD_BUS_ERROR_MAP(SD_BUS_ERROR_FAILED, EACCES),
     // ... standard errors ...
+
+    // INLINED: All of bus_common_errors
+    SD_BUS_ERROR_MAP(BUS_ERROR_NO_SUCH_UNIT, ENOENT),
+    SD_BUS_ERROR_MAP(BUS_ERROR_NO_UNIT_FOR_PID, ESRCH),
+    // ... 140+ additional error mappings ...
+
     SD_BUS_ERROR_MAP_END
 };
```

**src/libsystemd/sd-bus/bus-common-errors.c**
```c
-BUS_ERROR_MAP_ELF_REGISTER const sd_bus_error_map bus_common_errors[] = {
-    SD_BUS_ERROR_MAP(BUS_ERROR_NO_SUCH_UNIT, ENOENT),
-    // ... deleted ...
-};
+// File is now empty (except includes)
```

**src/libsystemd/sd-bus/bus-common-errors.h**
```c
-BUS_ERROR_MAP_ELF_USE(bus_common_errors);
+//BUS_ERROR_MAP_ELF_USE(bus_common_errors);
```

**Lookup code changes:**
```c
-        m = ALIGN_PTR(__start_SYSTEMD_BUS_ERROR_MAP);
-        while (m < __stop_SYSTEMD_BUS_ERROR_MAP) {
-            if (m->code == BUS_ERROR_MAP_END_MARKER) {
-                m = ALIGN_PTR(m + 1);
-                continue;
-            }
+        m = bus_standard_errors;
+        while (m->code != BUS_ERROR_MAP_END_MARKER) {
             if (streq(m->name, name)) {
                 return m->code;
             }
```

**Impact:**
- Single consolidated error map instead of distributed maps
- Simpler, faster lookup (no section iteration)
- Loses modularity - can't add new error maps via separate compilation units
- Acceptable for systemd's use case (all errors are in libsystemd)

### Macro Definitions (src/libsystemd/sd-bus/bus-error.h)
```c
-#define BUS_ERROR_MAP_ELF_REGISTER ...
-#define BUS_ERROR_MAP_ELF_USE(errors) ...
+//#define BUS_ERROR_MAP_ELF_REGISTER ...
+//#define BUS_ERROR_MAP_ELF_USE(errors) ...
```
**Commented out** - no longer used

## Build Artifact Bloat
None.

## Assessment
- **Patch quality**: Clean refactor
- **Actual changes**: Substantial (error map infrastructure redesign)
- **Correctness**: Appears sound - consolidation is valid for systemd
- **Trade-off**: Loses extensibility of section-based approach
- **Fil-C relevance**: High - demonstrates ELF section incompatibility with capabilities
