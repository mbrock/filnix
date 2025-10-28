# OpenSSL v3.3.1

## Summary
Comprehensive Fil-C adaptation: linker flag fixes and extensive C wrappers for assembly AES functions with bounds checking via Fil-C safety primitives.

## Fil-C Compatibility Changes

### Build System
- **Configurations/shared-info.pl**: Remove `-Wl,` prefix from `--version-script=` linker flags (lines 9, 18)
  - Fil-C linker expects bare `--version-script=` format

### Assembly Function Wrappers (New Files)
Created extensive C wrapper layers for assembly-optimized AES functions:

- **crypto/aes/aes_asm_forward.c**: Wrappers for generic AES assembly
  - `AES_set_encrypt_key()`, `AES_set_decrypt_key()`, `AES_encrypt()`, `AES_decrypt()`, `AES_cbc_encrypt()`
  - Use `zcheck_readonly()`, `zcheck()`, `zunsafe_buf_call()`, `zunsafe_fast_call()`

- **crypto/aes/aesni_asm_forward.c**: Wrappers for AES-NI assembly (181 lines)
  - `aesni_*` functions: set_encrypt_key, encrypt, ecb_encrypt, cbc_encrypt, ocb_encrypt/decrypt, ctr32_encrypt_blocks, xts_encrypt/decrypt, ccm64_*
  - Includes `l_size()` helper for OCB buffer size calculation

- **crypto/aes/aesni_mb_asm_forward.c**: Multi-block AES wrapper
  - `aesni_multi_cbc_encrypt()` with descriptor array validation

- **crypto/aes/aesni_sha1_asm_forward.c**: AES+SHA1 stitched implementation
  - `aesni_cbc_sha1_enc()`

- **crypto/aes/aesni_sha256_asm_forward.c**: AES+SHA256 stitched
  - `aesni_cbc_sha256_enc()`

- **crypto/aes/bsaes_asm_forward.c**: Bit-sliced AES wrappers
  - `ossl_bsaes_*` functions: cbc_encrypt, ctr32_encrypt_blocks, xts_encrypt/decrypt

- **crypto/aes/vpaes_asm_forward.c**: Vector-permute AES wrappers
  - `vpaes_set_encrypt_key()`, `vpaes_set_decrypt_key()`, `vpaes_encrypt()`, `vpaes_decrypt()`, `vpaes_cbc_encrypt()`

### Build Integration
- **crypto/aes/build.info**: Updated to compile new wrapper files alongside assembly
  - Changed from bare assembly references to pairs like `aes_asm_forward.c aes-x86_64.s`

### Provider Code Updates
- **cipher_aes_gcm_hw_aesni.inc**: Add `#include <stdfil.h>`
- **cipher_aes_gcm_hw_vaes_avx512.inc**: Convert function declarations to static inline wrappers with bounds checking
  - `ossl_vaes_vpclmulqdq_capable()`, `ossl_aes_gcm_*_avx512()`, `ossl_gcm_gmult_avx512()`
  - All use `zcheck()`, `zcheck_readonly()`, `zunsafe_*_call()` patterns

### Random Seeding
- **rand_cpu_x86.c**: Add `#include <stdfil.h>` for RDRAND/RDSEED support

### Disabled Tests
Deleted test files that are incompatible with Fil-C:
- **test/recipes/01-test_symbol_presence.t**: Symbol checking via nm (242 lines)
- **test/recipes/04-test_param_build.t**: Parameter building tests
- **test/recipes/30-test_afalg.t**: AF_ALG engine tests
- **test/recipes/90-test_secmem.t**: Secure memory tests
- **test/recipes/90-test_shlibload.t**: Shared library loading tests (75 lines)

## Build Artifact Bloat
None - deleted files are test scripts, not build artifacts.

## Assessment
- Patch quality: Clean, systematic wrapping strategy
- Actual changes: Substantial (extensive safety layer over assembly code + symbol versioning fixes)
