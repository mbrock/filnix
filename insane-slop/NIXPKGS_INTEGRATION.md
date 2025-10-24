# Integrating Fil-C as an Alternative Libc in Nixpkgs

## Executive Summary

This document explains how musl and static builds are systematically integrated in nixpkgs and provides concrete patterns to create a similar `pkgsFilC` variant that rebuilds all packages with fil-c as the libc/runtime.

The integration relies on several key mechanisms:
1. **Platform/ABI definitions** in the systems library
2. **Variant package set creation** through `nixpkgsFun` re-evaluation
3. **Libc attribute routing** in all-packages.nix
4. **Stdenv bootstrap modification** for alternative libcs
5. **Systematic package rebuilding** with override mechanisms

---

## How Musl Is Integrated in Nixpkgs

### 1. Platform Definition (lib/systems/)

**Location:** `/home/mbrock/nixpkgs/lib/systems/`

#### ABI Predicates (inspect.nix:381-389)

The system defines predicates that recognize musl ABIs:

```nix
isMusl =
  with abis;
  map (a: { abi = a; }) [
    musl
    musleabi
    musleabihf
    muslabin32
    muslabi64
  ];
```

These ABIs are parsed from platform triples (e.g., `x86_64-unknown-linux-musl`).

#### Libc Derivation (default.nix:120-159)

The `libc` attribute is automatically derived from the parsed platform:

```nix
libc =
  if final.isDarwin then
    "libSystem"
  else if final.isMsvc then
    "ucrt"
  # ... other cases ...
  else if final.isMusl then
    "musl"
  else if final.isUClibc then
    "uclibc"
  else if final.isAndroid then
    "bionic"
  else if final.isLinux then
    "glibc"  # default
  # ... other cases ...
```

**Key insight:** The `stdenv.hostPlatform.libc` attribute is set automatically based on the parsed ABI. This drives downstream decisions.

### 2. Platform Triple Transformation (stage.nix:90-116)

**Location:** `/home/mbrock/nixpkgs/pkgs/top-level/stage.nix`

When switching to musl, the parsed platform is transformed:

```nix
makeMuslParsedPlatform =
  parsed:
  (
    parsed
    // {
      abi =
        {
          gnu = lib.systems.parse.abis.musl;
          gnueabi = lib.systems.parse.abis.musleabi;
          gnueabihf = lib.systems.parse.abis.musleabihf;
          gnuabin32 = lib.systems.parse.abis.muslabin32;
          gnuabi64 = lib.systems.parse.abis.muslabi64;
          gnuabielfv2 = lib.systems.parse.abis.musl;
          gnuabielfv1 = lib.systems.parse.abis.musl;
          # idempotent cases:
          musleabi = lib.systems.parse.abis.musleabi;
          musleabihf = lib.systems.parse.abis.musleabihf;
          muslabin32 = lib.systems.parse.abis.muslabin32;
          muslabi64 = lib.systems.parse.abis.muslabi64;
        }
        .${parsed.abi.name} or lib.systems.parse.abis.musl;
    }
  );
```

**Key insight:** This transforms glibc ABIs (gnu, gnueabi, etc.) to their musl equivalents. The ABI name drives the `libc` attribute later.

### 3. Variant Package Set Creation (variants.nix:74-91)

**Location:** `/home/mbrock/nixpkgs/pkgs/top-level/variants.nix`

Creating `pkgsMusl` is done via variant definition:

```nix
pkgsMusl =
  if stdenv.hostPlatform.isLinux && stdenv.buildPlatform.is64bit then
    nixpkgsFun {
      overlays = [
        (self': super': {
          pkgsMusl = super';
        })
      ]
      ++ overlays;
      ${if stdenv.hostPlatform == stdenv.buildPlatform then "localSystem" else "crossSystem"} = {
        config = lib.systems.parse.tripleFromSystem (
          makeMuslParsedPlatform stdenv.hostPlatform.parsed
        );
      };
    }
  else
    throw "Musl libc only supports 64-bit Linux systems.";
```

**Key mechanics:**
- Calls `nixpkgsFun` (the package set constructor)
- Transforms the platform via `makeMuslParsedPlatform`
- Converts back to triple string via `tripleFromSystem`
- Uses `localSystem` or `crossSystem` depending on whether native or cross
- Preserves existing overlays and adds a self-reference overlay

### 4. Libc Selection in all-packages.nix (7361-7395)

**Location:** `/home/mbrock/nixpkgs/pkgs/top-level/all-packages.nix`

Once the platform is transformed, the correct libc package is selected:

```nix
libc =
  let
    inherit (stdenv.hostPlatform) libc;
  in
  if libc == null then
    null
  else if libc == "glibc" then
    glibc
  else if libc == "bionic" then
    bionic
  else if libc == "uclibc" then
    uclibc
  else if libc == "avrlibc" then
    avrlibc
  else if libc == "newlib" && stdenv.hostPlatform.isMsp430 then
    msp430Newlib
  else if libc == "newlib" && stdenv.hostPlatform.isVc4 then
    vc4-newlib
  else if libc == "newlib" && stdenv.hostPlatform.isOr1k then
    or1k-newlib
  else if libc == "newlib" then
    newlib
  else if libc == "newlib-nano" then
    newlib-nano
  else if libc == "musl" then
    musl
  # ... other libcs ...
```

**Key insight:** The `stdenv.hostPlatform.libc` attribute (set by the systems library) determines which libc package is used.

### 5. Bootstrap Integration (linux/default.nix)

**Location:** `/home/mbrock/nixpkgs/pkgs/stdenv/linux/default.nix`

Bootstrap files are selected per-libc (lines 67-96):

```nix
bootstrapFiles ?
  let
    table = {
      glibc = {
        i686-linux = import ./bootstrap-files/i686-unknown-linux-gnu.nix;
        x86_64-linux = import ./bootstrap-files/x86_64-unknown-linux-gnu.nix;
        # ... other architectures ...
      };
      musl = {
        aarch64-linux = import ./bootstrap-files/aarch64-unknown-linux-musl.nix;
        armv6l-linux = import ./bootstrap-files/armv6l-unknown-linux-musleabihf.nix;
        x86_64-linux = import ./bootstrap-files/x86_64-unknown-linux-musl.nix;
      };
    };
    archLookupTable = table.${localSystem.libc} or (throw "unsupported libc for the pure Linux stdenv");
```

**Key insight:** Different bootstrap files (pre-built binaries) are used depending on the libc.

### 6. Libc References in Bootstrap (linux/default.nix:273-289)

Bootstrap stages reference libc conditionally:

```nix
${localSystem.libc} = self.stdenv.mkDerivation {
  pname = "bootstrap-stage0-${localSystem.libc}";
  # ...
  buildCommand = ''
    mkdir -p $out
    ln -s ${bootstrapTools}/lib $out/lib
  ''
  + lib.optionalString (localSystem.libc == "glibc") ''
    ln -s ${bootstrapTools}/include-glibc $out/include
  ''
  + lib.optionalString (localSystem.libc == "musl") ''
    ln -s ${bootstrapTools}/include-libc $out/include
  '';
};
```

**Key insight:** Different include directories are used per-libc.

---

## Static Builds Pattern (pkgsStatic)

**Location:** `/home/mbrock/nixpkgs/pkgs/top-level/stage.nix:310-331`

Static builds use the same pattern, additionally setting `isStatic`:

```nix
pkgsStatic = nixpkgsFun {
  overlays = [
    (self': super': {
      pkgsStatic = super';
    })
  ]
  ++ overlays;
  crossSystem = {
    isStatic = true;  # <-- KEY ADDITION
    config = lib.systems.parse.tripleFromSystem (
      if stdenv.hostPlatform.isLinux then
        makeMuslParsedPlatform stdenv.hostPlatform.parsed
      else
        stdenv.hostPlatform.parsed
    );
    gcc =
      lib.optionalAttrs (stdenv.hostPlatform.system == "powerpc64-linux") { abi = "elfv2"; }
      // stdenv.hostPlatform.gcc or { };
  };
};
```

The `isStatic` flag triggers different build behaviors across packages.

---

## How to Create pkgsFilC

Based on the musl integration pattern, here's how to create a similar variant for fil-c:

### Step 1: Define a Fil-C ABI (Optional but Clean)

If fil-c is going to have its own ABI identifier, add to `lib/systems/parse.nix`:

```nix
abis = setTypes types.openAbi {
  # ... existing abis ...
  filc = { };
  filceabi = { };
};
```

And to `lib/systems/inspect.nix`:

```nix
isFilC =
  with abis;
  map (a: { abi = a; }) [
    filc
    filceabi
  ];
```

**Note:** For a simpler integration, fil-c could just use the musl ABIs or create new ones.

### Step 2: Define Libc Derivation Route in all-packages.nix

Add to the libc selection logic (around line 7387-7388):

```nix
else if libc == "filc" then
  filc
```

Where `filc` is the fil-c libc package (similar to how musl package is defined).

### Step 3: Create Fil-C Platform Transformer (stage.nix)

Add a function to transform platforms to fil-c:

```nix
makeFilCParsedPlatform =
  parsed:
  (
    parsed
    // {
      abi =
        {
          gnu = lib.systems.parse.abis.filc;           # or musl if reusing
          gnueabi = lib.systems.parse.abis.filceabi;   # or musleabi
          gnueabihf = lib.systems.parse.abis.filceabi;
          gnuabin32 = lib.systems.parse.abis.filc;
          gnuabi64 = lib.systems.parse.abis.filc;
          gnuabielfv2 = lib.systems.parse.abis.filc;
          gnuabielfv1 = lib.systems.parse.abis.filc;
          # idempotent cases:
          filc = lib.systems.parse.abis.filc;
          filceabi = lib.systems.parse.abis.filceabi;
        }
        .${parsed.abi.name} or lib.systems.parse.abis.filc;
    }
  );
```

### Step 4: Add pkgsFilC to variants.nix

```nix
pkgsFilC =
  if stdenv.hostPlatform.isLinux && stdenv.buildPlatform.is64bit then
    nixpkgsFun {
      overlays = [
        (self': super': {
          pkgsFilC = super';
        })
      ]
      ++ overlays;
      ${if stdenv.hostPlatform == stdenv.buildPlatform then "localSystem" else "crossSystem"} = {
        config = lib.systems.parse.tripleFromSystem (
          makeFilCParsedPlatform stdenv.hostPlatform.parsed
        );
      };
    }
  else
    throw "Fil-C only supports 64-bit Linux systems.";
```

### Step 5: Define Fil-C Bootstrap Files (Optional)

If fil-c has different runtime requirements than glibc/musl, create bootstrap files:

**Location:** `/home/mbrock/nixpkgs/pkgs/stdenv/linux/bootstrap-files/x86_64-unknown-linux-filc.nix`

These are pre-built bootstrapTools for fil-c. For a first pass, you might reuse musl bootstrap files and substitute the libc.

Add to `linux/default.nix`:

```nix
bootstrapFiles ?
  let
    table = {
      # ... existing entries ...
      filc = {
        x86_64-linux = import ./bootstrap-files/x86_64-unknown-linux-filc.nix;
        aarch64-linux = import ./bootstrap-files/aarch64-unknown-linux-filc.nix;
      };
    };
```

### Step 6: Define the Fil-C Libc Package

The actual fil-c libc needs to be available. In the current flake.nix, this is done as `filc-libc`:

```nix
filc-libc = base.runCommand "filc-libc" {} ''
  mkdir -p $out/{include,lib} $out/nix-support
  cp -r ${filc-unwrapped}/pizfix/include/. $out/include/ 2>/dev/null || true
  cp -r ${filc-unwrapped}/pizfix/lib/.     $out/lib/     2>/dev/null || true
  # ...
  echo "$out/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
  # ...
'';
```

For full nixpkgs integration, this should be a proper package in:
`/home/mbrock/nixpkgs/pkgs/by-name/fi/filc-libc/package.nix`

### Step 7: Full Example - filnix/flake.nix Approach (Simpler)

The current approach in filnix is actually a good interim step before full nixpkgs integration:

```nix
filpkgs = import nixpkgs {
  inherit system;
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-compat;
};
```

This uses `replaceStdenv` to swap the compiler globally. This is simpler than creating a full variant because:
- It doesn't require platform changes
- It reuses the existing glibc setup
- It only swaps the compiler toolchain

---

## Key Components to Override

### For a Full Fil-C Variant (pkgsFilC approach):

1. **Platform libc attribute:** Set to "filc" via ABI parsing
2. **Bootstrap files:** Provide fil-c compatible bootstrap tools
3. **Libc package:** Define filc package selection
4. **Compiler wrapper:** May need adjustments for fil-c runtime
5. **Dynamic linker path:** `/lib/ld-yolo-x86_64.so` (as in flake.nix)
6. **CRT objects:** `crt1.o`, `cri.o`, `crtn.o` paths
7. **Include directories:** Fil-c specific headers

### For the Current Interim Approach (replaceStdenv):

Only override:
1. **cc wrapper:** `filc-wrapped` (which has filc-libc configured)
2. **bintools:** `filc-bintools` (which has filc-libc configured)

---

## Stdenv Adapters Pattern (stdenv/adapters.nix)

**Location:** `/home/mbrock/nixpkgs/pkgs/stdenv/adapters.nix`

Standard functions that modify stdenv behavior:

### makeStaticBinaries (lines 82-120)

Adds `-static` to linker flags and includes static libc:

```nix
makeStaticBinaries =
  stdenv0:
  stdenv0.override (
    old:
    {
      mkDerivationFromStdenv = withOldMkDerivation old (
        stdenv: mkDerivationSuper: args:
        # ... add -static flags ...
      );
    }
    // lib.optionalAttrs (stdenv0.hostPlatform.libc == "glibc") {
      extraBuildInputs = (old.extraBuildInputs or [ ]) ++ [
        pkgs.glibc.static
      ];
    }
  );
```

### makeStaticLibraries (lines 124-144)

Adds `--enable-static --disable-shared`:

```nix
makeStaticLibraries =
  stdenv:
  stdenv.override (old: {
    mkDerivationFromStdenv = extendMkDerivationArgs old (
      args:
      {
        dontDisableStatic = true;
      }
      // lib.optionalAttrs (!(args.dontAddStaticConfigureFlags or false)) {
        configureFlags = (args.configureFlags or [ ]) ++ [
          "--enable-static"
          "--disable-shared"
        ];
        # ... cmake and meson equivalents ...
      }
    );
  });
```

### useMoldLinker (lines 305-336)

Example of tool override pattern:

```nix
useMoldLinker =
  stdenv:
  if stdenv.targetPlatform.isDarwin then
    throw "Mold can't be used to emit Mach-O (Darwin) binaries"
  else
    let
      bintools = stdenv.cc.bintools.override {
        extraBuildCommands = ''
          wrap ld.mold ${../build-support/bintools-wrapper/ld-wrapper.sh} ${pkgs.buildPackages.mold}/bin/ld.mold
          # ...
        '';
      };
    in
    stdenv.override (
      old:
      {
        allowedRequisites = null;
        cc = stdenv.cc.override { inherit bintools; };
      }
    );
```

**Pattern:** Override the cc wrapper's bintools to customize linking behavior.

---

## Cc-Wrapper Integration (build-support/cc-wrapper/default.nix)

The cc-wrapper is the key integration point. It takes:

- `cc` - the compiler (e.g., gcc, clang, fil-c)
- `libc` - the C library with headers and runtime
- `bintools` - the linker and related tools

Key parameters:

```nix
{
  # ... other params ...
  cc ? null,           # The compiler
  libc ? null,         # The C library
  bintools,            # Linker and binutils
  nativeTools,         # Use native system tools?
  nativeLibc,          # Use native system libc?
  noLibc ? false,      # No libc at all?
  # ...
}
```

The wrapper:
1. Sets up compiler flags pointing to libc headers
2. Sets up linker flags pointing to libc runtime
3. Wraps compiler invocations with proper search paths
4. Handles different compiler types (GCC, Clang, etc.)

---

## Practical Next Steps for Fil-C

### Option A: Interim Approach (Current flake.nix)

- Pros: Minimal changes, works today
- Cons: Not as systematic as full variant

```nix
filpkgs = import nixpkgs {
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-compat;
};
```

### Option B: Full Variant Approach

Steps:
1. Add fil-c ABI to systems library (optional)
2. Add `makeFilCParsedPlatform` to stage.nix
3. Add `pkgsFilC` to variants.nix
4. Add "filc" case to all-packages.nix libc selection
5. Create filc-libc package in nixpkgs
6. (Eventually) Add fil-c bootstrap files

### Option C: Hybrid Approach

Use the interim approach now, but structure it to be easily moved into full variant integration:

```nix
# In flake.nix
filpkgs-interim = import nixpkgs {
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-compat;
};

# In nixpkgs/pkgs/top-level/variants.nix (when ready)
pkgsFilC = nixpkgsFun {
  overlays = [
    (self': super': {
      pkgsFilC = super';
    })
  ]
  ++ overlays;
  localSystem = {
    config = lib.systems.parse.tripleFromSystem (
      makeFilCParsedPlatform stdenv.hostPlatform.parsed
    );
  };
};
```

---

## Key Files Reference

| File | Purpose | Key Content |
|------|---------|------------|
| `lib/systems/parse.nix` | ABI definitions | Define ABIs (musl, gnu, filc, etc.) |
| `lib/systems/inspect.nix` | Platform predicates | Predicates like `isMusl`, `isFilC` |
| `lib/systems/default.nix` | Platform derivation | Derive `libc` attribute from ABI |
| `pkgs/top-level/stage.nix` | Package set creation | `makeMuslParsedPlatform`, variant integration |
| `pkgs/top-level/variants.nix` | Variant definitions | `pkgsMusl`, `pkgsStatic`, (future: `pkgsFilC`) |
| `pkgs/top-level/all-packages.nix` | Package selection | Libc package selection logic |
| `pkgs/stdenv/linux/default.nix` | Linux bootstrap | Bootstrap file selection per libc |
| `pkgs/stdenv/adapters.nix` | Stdenv modifiers | `makeStaticBinaries`, `useMoldLinker`, etc. |
| `pkgs/build-support/cc-wrapper/default.nix` | Compiler wrapping | Integration of compiler + libc + bintools |

---

## Summary

The nixpkgs approach to integrating alternative libcs is systematic and elegant:

1. **Define ABIs** in the systems library
2. **Auto-derive libc attribute** based on parsed ABI
3. **Create platform transformers** (e.g., `makeMuslParsedPlatform`)
4. **Define variants** using `nixpkgsFun` with transformed platforms
5. **Route libc packages** in all-packages.nix
6. **Provide bootstrap files** per libc for pure bootstrapping

To add fil-c, you would follow the same pattern. For now, the interim approach using `replaceStdenv` is practical and works well for testing and single-package builds.

