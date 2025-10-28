# TCL 8.6.15

## Summary
**Zero actual code changes.** Entire patch is build artifact bloat from development artifacts accidentally included in the patch.

## Fil-C Compatibility Changes
**None.**

## Build Artifact Bloat

### Binary Files (should NEVER be in patches)
**compat/zlib/win32/**
- `zdll.lib`, `zlib1.dll` (Windows builds)

**compat/zlib/win64/**
- `libz.dll.a`, `zdll.lib`, `zlib1.dll` (Windows x64)

**compat/zlib/win64-arm/**
- `libz.dll.a`, `zdll.lib`, `zlib1.dll` (Windows ARM64)

**win/**
- `x86_64-w64-mingw32-nmakehlp.exe` (build helper)
- `tclsh.ico`, `coffbase.txt` (Windows resources)

**Total binary bloat:** ~500KB

### Generated Autotools Files
**compat/zlib/contrib/*/Makefile**
- blast, minizip, puff, untgz modules
- These are generated, not source

**compat/zlib/nintendods/Makefile** (126 lines)
- Nintendo DS cross-compile build system
- Not relevant to Fil-C port

### Duplicated Library Code
**library/tcltest/tcltest.tcl** (3588 lines!)
- Entire TCL test framework
- This file should already exist in TCL distribution
- **pkgIndex.tcl** also duplicated

### Generated Man Pages
**doc/tclsh.1** (149 lines)
- Generated from doctools format
- Should not be in source patch

### Generated Configure Fragments  
**win/tclsh.exe.manifest.in**, **win/tclsh.rc**
- Windows PE resource definitions
- Auto-generated from configure

### Configure Script Fragments
Massive sed script fragment (lines 448-797) embedded in patch:
```bash
# CONFIG_FILES section
# 350+ lines of autoconf-generated shell code
```
**This is generated code** from `autoconf` - should never be patched manually

## Why This Happened
Looks like developer:
1. Extracted TCL tarball
2. Built it (generating Makefiles, configure scripts)
3. Copied some Windows binaries into tree
4. Ran `git diff` without `.gitignore`
5. Committed everything

## What Should Be Here
**Nothing.** TCL 8.6.15 apparently needs no Fil-C patches.

## Assessment
- **Patch quality**: Terrible - 100% bloat
- **Actual changes**: None
- **Recommended action**: Delete this patch file entirely
- **If TCL actually needs changes**: Start over with clean source tree
