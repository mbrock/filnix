# TPM2-TSS on Fil-C

TPM2-TSS 4.1.3 builds successfully with its full configured upstream suite:
**267 test programs, 256 passed, 11 skipped, zero failures** (2026-09-19).
The 11 skips are the same upstream unsupported-TPM-feature cases seen in the
previous run. No failing TPM2 test or assertion was removed.

The recipe is in `ports/tpm2.nix`. Local patches live in `patches/`, outside
the upstream patch extractor's generated files. The compiler, runtime, glibc
and unrelated packages keep their existing derivations.

## Pointer-valued mocks

Cmocka 1.1.7 transports mock values through `LargestIntegralType`. Storing a
pointer in that integer and returning it through the mock queue loses Fil-C's
capability. A raw address comparison can pass, but dereferencing or freeing the
returned pointer then fails.

TPM2 alone now uses [cmocka 2.0.2](https://cmocka.org/files/2.0/), whose
[`CMockaValueData` API](https://api.cmocka.org/group__cmocka__mock.html) has a
pointer member. `toolchain/cmocka-pointer-mocks.h` adapts TPM2's old generic
`will_return`, `mock_type` and `check_expected` calls to select the pointer or
integer member at compile time. It preserves counted, always and optional
expectations, and evaluates each supplied value once. The adapter supports
the C integer/pointer values used by these tests, not floating-point mocks.

Three old call sites need explicit corrections: the vendor string comes from
`mock_ptr_type`, and libtpms state and buffer-length parameters use integer
checks instead of `check_expected_ptr`.

Cmocka's own **80 checks pass**. Its exception-recovery test raises `SIGSYS`
under Fil-C instead of `SIGSEGV`, exercising the same handler and recovery
path for all three cases. Fil-C rejects handlers for synchronous fault signals;
this is not evidence that it supports recovering from memory-safety traps.

## Making the linker mocks actually intercept calls

The existing `toolchain/filc-test-wrap.py` translates GNU ld's `--wrap=NAME`
to Fil-C function descriptors and renames `__wrap`/`__real` symbols accordingly.
Two additional details matter:

- Fil-C generates weak direct-call thunks for external functions. Linking the
  real definition from another object can replace a thunk with the real entry
  point, bypassing the wrapped descriptor. The adapter localizes these thunks
  only when the corresponding descriptor is undefined in that object.
- Fil-C lowers calls named `malloc` and `free` directly to runtime operations,
  even with `-fno-builtin`. TPM2's test compilation gives those calls temporary
  names; the adapter restores their descriptor names after compilation. The
  installed libraries retain normal allocation lowering.

This fixes the bypassed FAPI hash/I/O mocks and the resulting exhausted
expectations. The existing `setenv` repair remains: FAPI's integration harness
must not free a string retained by `putenv`.

## SPI pointer slots

Linux's `spi_ioc_transfer` represents its buffer pointers as 64-bit integer
fields. Under Fil-C, `tpm2-spi-pointers.patch` copies the pointer representations
into those slots with `memcpy`, preserving the shadow capabilities and the
original ABI bytes. Compile-time assertions check the pointer/slot sizes.
The mocked ioctl copies the pointers back the same way and retains all of its
request and response payload assertions.

This proves the mocked SPI protocol initialization. Physical TPM/SPI hardware
and the runtime's handling of nested ioctl pointers have not been validated.
The integration suite uses the recipe's software TPM.

## Reproduce and follow up

```sh
nix build .#legacyPackages.x86_64-linux.pkgsFilc.tpm2-tss --no-link -L
nix build --impure --file tests/link-wrap.nix --no-link -L
nix build --impure --file tests/cmocka-pointer-mocks.nix --no-link -L
```

The linker regression tests direct and indirect calls, real-function forwarding,
allocation wrappers, and both object-file orders. The pointer regression reads
and writes returned heap pointers, reads stack pointers, checks strings, and
exercises signed integers, nulls and expectation counts.

Comparing recursive derivation inputs against the campaign's failed TPM2 build
finds only three additions: TPM2, its private cmocka, and the cmocka source fetch.
All compiler/runtime/libc inputs are reused. Full logs and the comparison are
retained in `results/tpm2-20260919/` in the repairs checkout.

The recorded graph has 1,846 unsuccessful candidate attributes affected by
TPM2, with overlapping blockers. Only six have TPM2 as their sole recorded
failure: `tpm2-tss`, `tpm2-tools`, `tpm2-abrmd`, `tpm2-openssl`, `tpm2-totp`
and `ima-evm-utils`. Retry this bounded set in campaign
`3eaf2f72-7c12-4bf2-9934-9646ea9dab4d`, preserving old recipes and failure evidence.

The six candidates were submitted from repair commit
`1723cf75266dcf98b4dd3182e4ad0d98848ad8f3`. Plan
`9b913a21-99fb-4ad0-9dd6-c6d4c14e08b0` completed successfully, and build batch
`9e125559-24f3-4936-84b7-ebcb5b0ba47c` started with the already-built TPM2
derivation. Subsequent consumer results belong to the live campaign; the
successful TPM2 check above does not imply that every consumer will pass.
