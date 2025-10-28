# Keyutils 1.6.3

## Summary
Complete syscall integration with Fil-C's syscall validation layer. All kernel key management syscalls replaced with Fil-C wrappers.

## Fil-C Compatibility Changes

### Syscall wrapper integration (keyutils.c)
- **add_key()**: Changed from `syscall(__NR_add_key, ...)` to `zsys_add_key(...)`
- **request_key()**: Changed to `zsys_request_key(...)`
- **keyctl()**: Major refactoring
  - Removed variadic argument handling (`va_list`, `va_arg`)
  - Changed to: `return *(long*)zcall(zsys_keyctl, zargs());`
  - Uses Fil-C's `zcall` mechanism for syscall validation

### Specialized keyctl operations
All keyctl DH/PKI operations now use dedicated Fil-C wrappers:
- **keyctl_dh_compute()**: → `zsys_keyctl_dh_compute()`
- **keyctl_dh_compute_kdf()**: → `zsys_keyctl_dh_compute_kdf()`
- **keyctl_pkey_query()**: → `zsys_keyctl_pkey_query()`
- **keyctl_pkey_encrypt()**: → `zsys_keyctl_pkey_encrypt()`
- **keyctl_pkey_decrypt()**: → `zsys_keyctl_pkey_decrypt()`
- **keyctl_pkey_sign()**: → `zsys_keyctl_pkey_sign()`
- **keyctl_pkey_verify()**: → `zsys_keyctl_pkey_verify()`

Added `#include <pizlonated_syscalls.h>` for wrapper declarations.

### Build system changes (Makefile)
- **Install target split**:
  - New `install-optfil` target: installs headers/libraries/binaries only
  - Original `install` target: depends on `install-optfil` + installs config files
  - Moved `keyutils.h` installation to `install-optfil` (from `install`)
  - Reason: Allows building without installing system configuration

### Code cleanup (keyctl_watch.c)
- Removed unused `after_eq()` inline function
  - Was defined but never called
  - Dead code removal

## Build Artifact Bloat
None - all changes are code modifications.

## Assessment
- **Patch quality**: Minimal - focused changes only
- **Actual changes**: Substantial integration work
  - Complete syscall wrapper integration required for Fil-C
  - Fil-C validates all syscalls through zsys_* wrappers
  - Prevents malicious syscalls that could bypass memory safety
- **Interesting**: Shows Fil-C's syscall validation architecture
  - Can't call raw syscalls directly
  - All kernel operations must go through validated wrappers
  - Part of "GIMSO" (Garbage In, Memory Safety Out) principle
