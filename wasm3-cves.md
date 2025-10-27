# Testing Fil-C with Real CVEs in wasm3

WebAssembly is supposed to be a safe way to run compiled code, by using a memory safe runtime. If you don't trust the memory safety of the runtime, you can't trust it to run WebAssembly code safely. I started looking around for a WebAssembly interpreter to build with Fil-C, and I found [wasm3](https://github.com/wasm3/wasm3). Perfect candidate—it's simple, portable C, easy to build, the kind of thing that should just work.

But then I noticed: wasm3 has been unmaintained for a year or two now, the author busy defending Ukraine from its foreign aggressor, and the wasm3 package in nixpkgs is actually marked as insecure because it has several unfixed CVEs; you can't even try to run it without changing your Nix configuration.

Well, okay. But wait—that's actually very interesting!

I'm always just trying to "get things to work" when building stuff with Fil-C, but it's at least as interesting to see when things _don't_ work. That is, after all, the whole point of Fil-C: to crash loudly when invalid things happen, rather than silently corrupting memory or letting attackers do whatever they want.

And these CVEs? They come with proof-of-concept exploit files. Perfect test cases.

## Building wasm3 with Fil-C

I added wasm3 to my Nix flake like this:

```nix
wasm3 =
  filenv.mkDerivation {
    src = wasm3-src;
    pname = "wasm3";
    version = "0.5.1";
    enableParallelBuilding = true;
    nativeBuildInputs = with base; [
      cmake ninja
    ];
    cmakeFlags = ["-DBUILD_WASI=simple"];
  };
```

Then: `nix build .#wasm3` and it worked. No source changes needed. Just compile with the Fil-C toolchain.

## Testing CVE-2022-39974: Out-of-Bounds Read

This CVE is about an out-of-bounds read in the `op_Select_i32_srs` operation. In normal wasm3, it causes a segfault. I grabbed the PoC from [the GitHub issue](https://github.com/wasm3/wasm3/issues/379):

```bash
$ curl -L -o cve-2022-39974.wasm.gz \
  "https://github.com/wasm3/wasm3/files/9441091/op_Select_i32_srs.wasm.gz"
$ gunzip cve-2022-39974.wasm.gz
$ ./result/bin/wasm3 cve-2022-39974.wasm
```

And here's what happened:

```
filc safety error: cannot read pointer with ptr >= upper.
    pointer: 0x7e5039350f90,0x7e5015781210,0x7e5015791220
    expected 4 bytes.
semantic origin:
    <somewhere>: op_Select_i32_srs
check scheduled at:
    <somewhere>: op_Select_i32_srs
    <somewhere>: op_f64_Ceil_s
    <somewhere>: op_i32_Divide_rs
    <somewhere>: op_f32_Load_f32_s
    <somewhere>: op_i32_Store_i32_ss
    <somewhere>: op_SetSlot_i32
    <somewhere>: op_MemGrow
    <somewhere>: op_i32_EqualToZero_s
    <somewhere>: op_Entry
    <somewhere>: m3_CallArgv
    <somewhere>: repl_call
    <somewhere>: main
    ../sysdeps/nptl/libc_start_call_main.h:58:16: __libc_start_call_main
    ../csu/libc-start.c:161:3: __libc_start_main
    <runtime>: start_program
[3310720] filc panic: thwarted a futile attempt to violate memory safety.
Trace/breakpoint trap (core dumped)
```

Well well well, if it isn't a read pointer safety overflow violation! The pointer `0x7e5039350f90` tried to read beyond its upper bound. Fil-C caught it at the exact operation that causes the CVE (`op_Select_i32_srs`), printed a full stack trace, and stopped execution.

CVE thwarted.

## Testing CVE-2022-34529: Slot Index Integer Overflow

This one involves an integer overflow in slot index calculation. In standard wasm3, this leads to memory corruption and potential RCE. Got the PoC from [this issue](https://github.com/wasm3/wasm3/issues/337):

```bash
$ curl -L -o cve-2022-34529.wasm.zip \
  "https://github.com/wasm3/wasm3/files/8939432/poc.wasm.zip"
$ unzip cve-2022-34529.wasm.zip
$ ./result/bin/wasm3 poc.wasm
```

Output:

```
filc safety error: cannot read pointer with ptr < lower.
    pointer: 0x754f1ef76590,0x754fd8581210,0x754fd8591220
    expected 4 bytes.
semantic origin:
    <somewhere>: op_MemFill
check scheduled at:
    <somewhere>: op_MemFill
    <somewhere>: op_SetRegister_i32
    <somewhere>: op_f32_Ceil_s
    <somewhere>: op_Entry
    <somewhere>: m3_CallArgv
    <somewhere>: repl_call
    <somewhere>: main
    ../sysdeps/nptl/libc_start_call_main.h:58:16: __libc_start_call_main
    ../csu/libc-start.c:161:3: __libc_start_main
    <runtime>: start_program
[3310747] filc panic: thwarted a futile attempt to violate memory safety.
Trace/breakpoint trap (core dumped)
```

This time: "cannot read pointer with ptr < lower" — the pointer underflowed! The integer overflow wrapped around and produced a negative offset, which Fil-C caught before any memory corruption could occur.

Thwarted again!

## What This Means

Fil-C can **provably thwart these real CVEs in a real program**. We're not talking about synthetic benchmarks or artificial test cases. These are actual exploits from actual security vulnerabilities that crash or exploit normal wasm3 builds.

You get the exact location where the violation happened (`op_Select_i32_srs`, `op_MemFill`), the full call stack, and the precise nature of the violation (pointer out of upper bound, pointer below lower bound).

Now this flake exposes Wasm3 as an ordinary package without marking it as insecure. Not because I'm reckless, and not because we fixed the bugs in the source code, and certainly not because we rewrote it in Rust. Just because I define it to be compiled with Fil-C!

## Try It Yourself

All the code is in this repo. The wasm3 package definition is in `packages.nix`, and the CVE payloads are defined in `wasm3-cves.nix` (fetched from GitHub with verified hashes).

If you have Nix with flakes enabled, just run:

```bash
nix develop github:mbrock/filnix#wasm3-cve-test
```

This drops you into a shell with:

- Fil-C-compiled wasm3 in your PATH
- The CVE exploit files ready to run
- A helpful banner showing what to do

Then just try:

```bash
wasm3 cve-2022-39974.wasm
wasm3 cve-2022-34529.wasm
```

[Fil-C](https://fil-c.org/) is very cool. Give it a try!
