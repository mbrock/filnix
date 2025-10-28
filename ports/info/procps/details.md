# procps-ng 4.0.4

## Summary
Single defensive fix for variadic argument handling that could cause undefined behavior.

## Fil-C Compatibility Changes

### library/pids.c - `pids_oldproc_open`
```c
-    int *ids;
+    int *ids = NULL;
     int num = 0;
 
     if (*this == NULL) {
         va_start(vl, flags);
-        ids = va_arg(vl, int*);
+        if (flags & (PROC_PID | PROC_UID)) ids = va_arg(vl, int*);
         if (flags & PROC_UID) num = va_arg(vl, int);
```

**Why this matters:**
- Original code unconditionally read `int*` from varargs
- If `flags` doesn't indicate PID or UID filtering, the `ids` argument may not exist
- Reading non-existent variadic argument is undefined behavior
- Fil-C runtime may trap on invalid va_arg access

**Impact:**
- Defensive programming - prevents reading past end of va_list
- Also initializes `ids = NULL` to avoid uninitialized variable

## Build Artifact Bloat
None - minimal patch.

## Assessment
- **Patch quality**: Minimal, targeted
- **Actual changes**: Minor but correct UB fix
- **Fil-C relevance**: Medium - UB that standard C allows but Fil-C may catch
