# sljit LIR on the Fil-C LLVM JIT

A prototype for [docs/pcre2-jit.md](../../docs/pcre2-jit.md): can PCRE2's JIT
run under Fil-C if sljit emits LLVM IR instead of machine code?

`replay.c` reads the sljit LIR that a native PCRE2 JIT compile dumped for a
pattern, lowers it to LLVM IR through the Fil-C LLVM-C API, compiles it with
`FilLLVMJIT_CompileModule`, and runs it against Fil-C PCRE2's own compiled
pattern and match data. It then checks the matches against the Fil-C
interpreter and times both. The lowering is what an sljit LLVM backend's
`sljit_emit_*` functions would do.

```sh
./run.sh         # build under /tmp/pcre2-sljit-llvm and run every pattern
./run.sh dump    # also regenerate lir/*.txt
```

`run.sh` needs gcc, make, curl and nix, and builds the staging toolchain
(`.#filcc-staging`), the only one with the LLVM JIT. After it has run:

```sh
/tmp/pcre2-sljit-llvm/replay tag 2 0.3        # pattern, opt-level, seconds
/tmp/pcre2-sljit-llvm/replay tag 2 0.3 dump   # print the IR
REPLAY_CACHE=1 /tmp/pcre2-sljit-llvm/replay tag 2 0.3   # shared object cache
REPLAY_TRACE=1 /tmp/pcre2-sljit-llvm/replay key 2 0.3   # trace the first calls
```

Files:

- `pats.h`: the ten patterns and the subject.
- `bench.c`: ns per `pcre2_match` call; `jit` as first argument JIT compiles.
- `sljit-dump.patch`: PCRE2 10.49 changes for the native build. With
  `SLJIT_DUMP=1` it prints the LIR with label and jump ids, the host addresses
  the LIR embeds (`SYM`), and read-only tables (`RODATA`). `-DPROTO_NO_SIMD`
  turns off the SIMD fast-forward paths.
- `lir/`: those dumps. The addresses in them are from the native process;
  `replay` maps each `SYM` range to the matching Fil-C object.

The LIR hard-codes native struct offsets, so `replay` links the unpatched
Fil-C PCRE2: `patches/pcre2-10.48-filc-match.patch` adds a field that moves
`ovector`.
