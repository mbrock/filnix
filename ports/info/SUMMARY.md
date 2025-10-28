# Fil-C Patch Summary

Analysis of all 71 patches for software ported to Fil-C.

| Project | Changes |
|---------|---------|
| attr | Symbol versioning directives changed from .symver to .filc_symver for Fil-C linker compatibility. |
| bash | Changed flexible array member from char to void* in SAVED_VAR struct for proper pointer table handling. |
| binutils | Converted intptr_t variables to void* pointers throughout, added template instantiations, disabled sbrk, and adjusted linker version script flags. |
| bison | Modified pointer alignment macro in obstack.h to use zmkptr for proper capability preservation. |
| bzip3 | Build system changes to disable pkgconfig and add version file; includes binary shakespeare.txt.bz3 file. |
| cairo | Replaced GLib's gsize-based once initialization with gpointer variants for type system compatibility. |
| cmake | Changed default library directory from lib64 to lib for 64-bit systems. |
| dash | Replaced vfork with fork; patch includes extensive autotools bloat (INSTALL, compile, install-sh, missing scripts). |
| dhcpcd | Extensive red-black tree modifications using Fil-C pointer operations (zretagptr, zorptr, zandptr, zxorptr) for capability-preserving bit manipulation. |
| diffutils | Added Clang diagnostic pragmas to suppress warnings and disabled stack overflow recovery for Fil-C. |
| e2fsprogs | Replaced all sbrk(0) calls with NULL for memory tracking in resource tracking code. |
| elfutils | Added Clang diagnostic pragmas to suppress unused parameter and unused const variable warnings. |
| emacs | Replaces Emacs' custom memory management with Fil-C's zgc_alloc, disables signal handling and garbage collection. |
| expat | Adds generated autoheader config template file (build artifact). |
| gettext | Fixes pointer arithmetic in localealias.c, adds symbol name prefixing, and skips two failing tests. |
| git | Converts intptr_t casts to/from void* in option parsing structures throughout Git codebase. |
| glib | Changes GType from integer typedef to opaque pointer, adds uintptr_t casts throughout, includes CI/build artifacts. |
| grep | Adds zmkptr macro for pointer alignment and disables stack overflow recovery in obstack and sigsegv. |
| icu | Adds early return for timezone, zmkptr for alignment, compiler fence for aliasing, and disables assembly object code generation. |
| jpeg | Changes alignment type from void* to double and removes test binary images. |
| kbd | Removes integer casts from ioctl calls and fixes keymap definitions (mostly keymap data file corrections). |
| keyutils | Replaces raw syscalls with Fil-C syscall wrappers (zsys_*), splits install target, removes unused function. |
| krb5 | Removes -Wl prefix from version script flag and adds Fil-C fences to libev event loop. |
| lfs-bootscripts | Creates /run/user directory at boot and enables unlimited core dumps for debugging. |
| libarchive | Adds Fil-C tagged pointer operations (zretagptr, zorptr, zandptr, zxorptr) to red-black tree implementation and changes pointer-storing deque to use void** instead of size_t*. |
| libdrm | Uses zexact_ptrtable to encode/decode pointers in DRM ioctl structures, with most conversions being one-way since kernel doesn't return pointers. |
| libedit | Adds __linux__ to platforms that don't require __STDC_ISO_10646__ definition. |
| libevdev | Replaces linker section-based test registration with constructor-based linked list and changes -Wl,--version-script to --version-script. |
| libevent | Disables several flaky SSL/HTTPS tests and casts legacy test function pointer to correct signature. |
| libffi | Major Fil-C port with custom closure/trampoline implementation using zclosure, custom calling convention (FFI_FILC), stack-based argument marshaling, and symbol versioning changes; includes test files and documentation updates. |
| libinput | Replaces linker section-based test device and test collection registration with constructor-based linked lists and changes -Wl,--version-script to --version-script. |
| libpng | Adds APNG (Animated PNG) support by defining PNG_APNG_SUPPORTED and implementing frame control chunks (acTL, fcTL, fdAT), animation metadata, and progressive/write APIs. |
| libuev | Massive autotools bloat - deletes .codedocs CI config and adds thousands of lines of generated autotools scripts (ar-lib, compile, ltmain.sh, etc). |
| libuv | Disables io_uring on Fil-C, adds signal safety checks, uses zexact_ptrtable for signal handler communication, fixes process title calculation with zlength, and disables several flaky tests. |
| libxcrypt | Disables SSE/SSE2 in yescrypt and changes .symver to .filc_symver for symbol versioning. |
| libxkbcommon | Changes -Wl,--version-script to --version-script in all meson.build symbol versioning flags. |
| libxml2 | Adds _Atomic qualifier to one struct field for thread safety. |
| linux | Extensive VMware GPU driver refactoring removing dumb buffer surface features and code cleanup. |
| lua | Disables readline library and adds debug flags to makefile. |
| m4 | Disables problematic tests, adds Fil-C compatibility for FPU control, obstack pointer alignment, and sigsegv detection. |
| make | Adds bounds check for environment variable array access. |
| man-db | Removes unsafe cast in ioctl call for FIEMAP file extent mapping. |
| nghttp2 | Massive build artifact bloat (INSTALL file + autotools scripts) with no actual code changes. |
| openssh | Adds sched_yield syscall to seccomp sandbox allow-list. |
| openssl | Removes -Wl prefix from symbol versioning flags and adds extensive assembly function wrappers with bounds checking. |
| p11-kit | Removes -Wl prefix from symbol versioning linker flags. |
| pam | Replaces hardcoded paths with build-time macros and adds Debian-specific features (both PAM 1.6.1 and 1.7.1 patches). |
| pcre2 | Disabled locale test in RunGrepTest; patch bloated with massive autotools artifact files (INSTALL, ar-lib, compile scripts). |
| perl | Extensive zptrtable integration for pointer encoding across XS modules, perl internals, and threading; replaces all PTR2IV/INT2PTR macros with capability-safe encoding. |
| procps | Fixes va_arg undefined behavior in pids_oldproc_open by conditionally reading pointer argument only when flags indicate it's present. |
| python | Major refactor of Python's internal pointer handling: GC linked lists use real pointers, atomic operations use void*_Atomic, interpreter frames use GC allocation, zptrtable for code object caches, and disabled SIMD/atomic intrinsics. |
| quickjs | Disabled direct dispatch, fixed pointer tagging in JSProperty autoinit realm_and_id field, forced rqsort compatibility, added stdfil.h include. |
| seatd | Changed linker version script flag from `-Wl,--version-script` to bare `--version-script` in meson.build. |
| sed | Disabled heap memory mapping checks and malloc size limit tests in gnulib test suite using __FILC__ guards; added capability-aware __BPTR_ALIGN macro to obstack.h. |
| simdutf | Added Fil-C support for CPUID detection and xgetbv instruction via zxgetbv() runtime helper; forced GCC CPUID path. |
| sqlite | Added zptrtable for TCL test pointer encoding, disabled atomic intrinsics, created Makefile.filc build system, extensive test harness pointer safety fixes. |
| systemd | Removed `-Wl,` prefix from version-script linker flags, disabled ELF section-based error map registration, inlined all bus error maps into bus_standard_errors array, added signal safety check via zis_unsafe_signal_for_handlers. |
| tar | Added capability-aware __BPTR_ALIGN macro to gnu/obstack.h using zmkptr for pointer alignment operations (identical to sed patch). |
| tcl | Patch is 99% build artifact bloat: zlib prebuilt binaries, generated configure scripts, tcltest library duplication, Windows resources, and generated man pages; no actual Fil-C compatibility code changes. |
| texinfo | Fixed pointer alignment macro in obstack.h and replaced intptr_t with void* for proper Fil-C pointer tracking. |
| tmux | Patch consists entirely of autotools build artifacts (compile, config.guess, config.sub scripts) with no Fil-C compatibility changes. |
| toybox | Patch consists entirely of build configuration files (good-config, kconfig binaries) with no Fil-C compatibility changes. |
| vim | Fixed sigaction call to pass NULL when func is SIG_ERR to prevent dereferencing invalid pointer. |
| wayland | Replaced ELF section-based test registration with constructor-based dynamic linked list for Fil-C compatibility. |
| weston | Replaced ELF section-based test registration with constructor-based dynamic allocation in three separate test frameworks. |
| XML-Parser | Used zptrtable_decode to properly recover Perl XS pointer from integer representation. |
| xz | Added .filc_symver symbol versioning support, zmkptr for pointer alignment, alignment fix for I/O buffer, disabled optimized decoder, and fixed linker flag syntax. |
| zlib | Disabled ARM CRC32 intrinsics and replaced configure-time detection with hardcoded values, deleted build artifacts. |
| zsh | Disabled zsh's custom heap allocator (zhalloc/hrealloc) by forcing malloc/free and added missing HashNode flags field. |
| zstd | Used standard cpuid.h for CPU feature detection and disabled inline assembly loop alignment optimizations for Fil-C compatibility. |

## Categories

### Major Changes (Substantial refactoring)
- **emacs**: Custom memory management → zgc_alloc
- **perl**: Comprehensive zptrtable integration
- **python**: GC, atomics, frame allocation refactor
- **sqlite**: Test harness pointer encoding
- **libffi**: Custom closure/trampoline implementation
- **systemd**: ELF section magic removal

### Common Patterns
- **Symbol versioning**: .symver → .filc_symver (attr, libxcrypt, xz, openssl)
- **Linker flags**: -Wl,--version-script → --version-script (many projects)
- **Pointer tables**: zptrtable/zexact_ptrtable (perl, python, sqlite, libdrm, libuv, XML-Parser)
- **Pointer alignment**: zmkptr in obstack.h (bison, grep, sed, tar, texinfo, m4)
- **Red-black trees**: Fil-C pointer ops (dhcpcd, libarchive)
- **ELF section removal**: Constructor-based registration (libevdev, libinput, wayland, weston)
- **vfork → fork**: (dash)

### Build Artifact Bloat (>50% bloat)
- **tcl**: 99% bloat (binaries, autotools)
- **pcre2**: 99% autotools
- **nghttp2**: 100% autotools
- **libuev**: 99% autotools
- **tmux**: 100% autotools
- **toybox**: 100% config files
- **expat**: 100% autogen

### Minimal/Trivial Changes
- **cmake**: lib64 → lib path
- **seatd**: Linker flag format
- **vim**: Null check
- **openssh**: Seccomp allow-list
- **libedit**: Platform macro
