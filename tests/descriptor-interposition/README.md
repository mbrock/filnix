# Function descriptors bind to an interposable implementation symbol

`patches/filc-descriptor-local-alias.patch` is a fork commit (`git am` on
mbrock/fil-c `filnix`, 2d9aa147f871). It adds `filc/tests/descriptorlocal`.
It is **not built or tested yet**: the orb's LLVM build was stopped partway.

## Approach

`pizlonatedFO_f` (a module's descriptor for `f`) stored `pizlonatedFIP<n>_f`,
which has `f`'s linkage and default visibility, so the descriptor's code came
from whichever DSO defines that symbol first in the global scope. The patch
makes the descriptor reference a private alias (`pizlonatedFIP<n>_f.local`)
for any non-local, non-available_externally implementation, in both the
fast-entry and the generic-entry slots. A private alias is emitted as
`.set .Lx, sym`; both LLVM's integrated assembler and GNU as then relocate
against the section (`R_X86_64_64 .text+off`), not the symbol. I checked
that with a hand-written IR module, including a linkonce function in a
comdat (the relocation targets `.text.<f>` in the same group).

Kept interposable, as natively: direct known-target calls
(`FunctionToHiddenFunction` → `pizlonatedFIP` via PLT), the cross-module
`pizlonatedFI<n>_f` alias, and the getter `pizlonated_f`, which is what
`&f` and calls from other modules go through. A descriptor for an undefined
function is never created in the module (it comes from the defining DSO's
getter), so it is unaffected.

## Expected results (`run.sh`)

Native clang 20, -O2 (at -O0, `callwhich()` is 1 in the plain case):

    plain:     which()=1 dlsym(which)()=2 callwhich()=2 whichptr()()=1
    Bsymbolic: which()=1 dlsym(which)()=2 callwhich()=2 whichptr()()=2

Pinned Fil-C (before the patch) differs only in `dlsym(which)()=1` for
`plain`. With the patch it should match native in every column.

## Still to verify on the host

- `run.sh` with the patched clang, at -O2 and `OPT=-O0`.
- `filc/run-tests -t descriptorlocal`, then the full suite against baseline.
- The SDL chain with sdl2-compat built without `-Wl,-Bsymbolic-functions`
  (drop it from `ports/pipewire-consumers.nix`): SDL_compat's `testver`.
