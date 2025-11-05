# Compiler Structure

The Fil-C compiler is built in a simple, modular way:

## filc0 - The Actual Compiler

`filc0.nix` compiles LLVM/Clang with the FilPizlonator pass. **This is the only compilation** - everything else is just wrappers with different flags.

## mkFilc - Parameterized Wrapper Builder

`mkFilc.nix` is a function that wraps filc0 with appropriate flags for different library combinations:

```nix
mkFilc = {
  filc0,                    # Required: the base compiler
  yolo-glibc,              # Required: runtime glibc
  yolo-glibc-impl,         # Required: glibc headers
  filc-stdfil-headers,     # Required: Fil-C headers
  libpizlo ? null,         # Optional: Fil-C runtime
  filc-glibc ? null,       # Optional: memory-safe glibc
  filc-libcxx ? null,      # Optional: C++ standard library
}
```

It builds a CRT library directory combining:
- yolo-glibc libs
- GCC crt files
- libpizlo (if provided)

And creates wrappers with appropriate `--filc-*` flags baked in.

## Main Outputs

- **filc0**: The bare LLVM/Clang compiler binary
- **filc**: The final, complete compiler (has everything: yolo-glibc, libpizlo, filc-glibc, libcxx)
- **filc-libcxx**: The memory-safe C++ standard library

## Internal Build Dependencies

These are only used during the build process and aren't meant to be used directly:

- **filc-for-libpizlo**: Wrapper configured for building libpizlo
- **filc-for-glibc**: Wrapper configured for building filc-glibc (adds libpizlo)
- **filc-for-libcxx**: Wrapper configured for building libcxx (adds filc-glibc)

## Build Order

```
yolo-glibc (system GCC) → filc0 (LLVM/Clang)
              ↓                    ↓
              └───> filc-for-libpizlo
                        ↓
                     libpizlo
                        ↓
                     filc-for-glibc
                        ↓
                    filc-glibc
                        ↓
                     filc-for-libcxx
                        ↓
                    filc-libcxx
                        ↓
                       filc  (final compiler)
                        ↓
                      ports
```

The "fix" in `flake.nix` orchestrates the build order to resolve dependencies between compiler wrappers and runtime libraries.

## Legacy Aliases

For compatibility with existing code:
- `filc1`, `filc1-runtime` → `filc-for-libpizlo`
- `filc2` → `filc-for-glibc`
- `filc3` → `filc-for-libcxx`
- `filc3xx`, `filc3xx-tranquil` → `filc`
