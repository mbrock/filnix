# Determinate Nix under Fil-C

[Determinate Nix](https://github.com/DeterminateSystems/nix-src) is
Determinate Systems' fork of Nix. Its extra features include parallel
evaluation, lazy trees, `builtins.parallel`, Wasm in the language and an
async (Boost.Asio) store layer. This port builds v3.22.5 (based on Nix
2.35.2) with Fil-C and runs its test suites. It also runs parallel
evaluation hard enough that races, use-after-frees and out-of-bounds
accesses in the fork would show up as Fil-C safety panics.

```sh
nix build -L .#legacyPackages.x86_64-linux.pkgsFilc.determinate-nix
# parallel evaluation through the whole functional suite:
nix build -L .#legacyPackages.x86_64-linux.pkgsFilc.determinateNixComponents.nix-functional-tests-parallel
```

RESULTS-PLACEHOLDER
