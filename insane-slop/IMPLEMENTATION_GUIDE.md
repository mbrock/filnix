# Fil-C Integration - Concrete File Examples

This document provides the exact locations and code snippets showing how musl/static builds work and how to create similar patterns for fil-c.

---

## File 1: Platform Definition and Libc Derivation

**File:** `/home/mbrock/nixpkgs/lib/systems/default.nix` (lines 120-159)

### Current Code

```nix
libc =
  if final.isDarwin then
    "libSystem"
  else if final.isMsvc then
    "ucrt"
  else if final.isMinGW then
    "msvcrt"
  else if final.isCygwin then
    "cygwin"
  else if final.isWasi then
    "wasilibc"
  else if final.isWasm && !final.isWasi then
    null
  else if final.isRedox then
    "relibc"
  else if final.isMusl then
    "musl"
  else if final.isUClibc then
    "uclibc"
  else if final.isAndroid then
    "bionic"
  else if
    final.isLinux # default
  then
    "glibc"
  else if final.isFreeBSD then
    "fblibc"
  # ... rest omitted
```

### How to Add Fil-C

To add fil-c with a custom ABI, insert:

```nix
# At the library level (lib/systems/default.nix)
else if final.isFilC then
  "filc"
```

But for now, fil-c can reuse the glibc or musl attribute without defining a custom ABI.

---

## File 2: ABI Parsing and Predicates

**File:** `/home/mbrock/nixpkgs/lib/systems/parse.nix` (lines 706-745)

### Current Code for Musl

```nix
abis = setTypes types.openAbi {
  # ... other abis ...
  muslabi64 = {
    # ...
  };
  muslabin32 = {
    # ...
  };
  musleabi = {
    # ...
  };
  musleabihf = {
    # ...
  };
  musl = { };
  uclibc = { };
  # ...
};
```

### To Add Fil-C ABI

```nix
abis = setTypes types.openAbi {
  # ... existing entries ...
  filc = { };
  filceabi = { };
  # ... rest ...
};
```

**File:** `/home/mbrock/nixpkgs/lib/systems/inspect.nix` (lines 381-389)

### Current Code for Musl

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

### To Add Fil-C Predicate

```nix
isFilC =
  with abis;
  map (a: { abi = a; }) [
    filc
    filceabi
  ];
```

---

## File 3: Platform Transformer Function

**File:** `/home/mbrock/nixpkgs/pkgs/top-level/stage.nix` (lines 90-116)

### Current Code for Musl

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
          # Idempotent cases:
          musleabi = lib.systems.parse.abis.musleabi;
          musleabihf = lib.systems.parse.abis.musleabihf;
          muslabin32 = lib.systems.parse.abis.muslabin32;
          muslabi64 = lib.systems.parse.abis.muslabi64;
        }
        .${parsed.abi.name} or lib.systems.parse.abis.musl;
    }
  );
```

### For Fil-C

```nix
makeFilCParsedPlatform =
  parsed:
  (
    parsed
    // {
      abi =
        {
          gnu = lib.systems.parse.abis.filc;
          gnueabi = lib.systems.parse.abis.filceabi;
          gnueabihf = lib.systems.parse.abis.filceabi;
          gnuabin32 = lib.systems.parse.abis.filc;
          gnuabi64 = lib.systems.parse.abis.filc;
          gnuabielfv2 = lib.systems.parse.abis.filc;
          gnuabielfv1 = lib.systems.parse.abis.filc;
          # Idempotent cases:
          filc = lib.systems.parse.abis.filc;
          filceabi = lib.systems.parse.abis.filceabi;
        }
        .${parsed.abi.name} or lib.systems.parse.abis.filc;
    }
  );
```

---

## File 4: Variant Creation

**File:** `/home/mbrock/nixpkgs/pkgs/top-level/variants.nix` (lines 74-91)

### Current Code for Musl

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
        config = lib.systems.parse.tripleFromSystem (makeMuslParsedPlatform stdenv.hostPlatform.parsed);
      };
    }
  else
    throw "Musl libc only supports 64-bit Linux systems.";
```

### For Fil-C

Add after the `pkgsMusl` definition:

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
        config = lib.systems.parse.tripleFromSystem (makeFilCParsedPlatform stdenv.hostPlatform.parsed);
      };
    }
  else
    throw "Fil-C only supports 64-bit Linux systems.";
```

**Important:** Make sure `makeFilCParsedPlatform` is passed to variants.nix in stage.nix (line 203):

```nix
variants =
  self: super:
  lib.optionalAttrs config.allowVariants (
    import ./variants.nix {
      inherit
        lib
        nixpkgsFun
        stdenv
        overlays
        makeMuslParsedPlatform
        makeFilCParsedPlatform    # <-- ADD THIS
        ;
    } self super
  );
```

---

## File 5: Libc Package Selection

**File:** `/home/mbrock/nixpkgs/pkgs/top-level/all-packages.nix` (lines 7361-7400)

### Current Code

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
  # ... other special cases for newlib ...
  else if libc == "musl" then
    musl
  else if libc == "msvcrt" then
    if stdenv.hostPlatform.isMinGW then windows.mingw_w64 else windows.sdk
  # ... rest ...
```

### To Add Fil-C

Insert after the musl case (around line 7388):

```nix
  else if libc == "filc" then
    filc
```

This requires that `filc` package is defined somewhere in all-packages.nix.

---

## File 6: Bootstrap File Selection

**File:** `/home/mbrock/nixpkgs/pkgs/stdenv/linux/default.nix` (lines 67-96)

### Current Code

```nix
bootstrapFiles ?
  let
    table = {
      glibc = {
        i686-linux = import ./bootstrap-files/i686-unknown-linux-gnu.nix;
        x86_64-linux = import ./bootstrap-files/x86_64-unknown-linux-gnu.nix;
        armv5tel-linux = import ./bootstrap-files/armv5tel-unknown-linux-gnueabi.nix;
        armv6l-linux = import ./bootstrap-files/armv6l-unknown-linux-gnueabihf.nix;
        armv7l-linux = import ./bootstrap-files/armv7l-unknown-linux-gnueabihf.nix;
        aarch64-linux = import ./bootstrap-files/aarch64-unknown-linux-gnu.nix;
        # ... more architectures ...
      };
      musl = {
        aarch64-linux = import ./bootstrap-files/aarch64-unknown-linux-musl.nix;
        armv6l-linux = import ./bootstrap-files/armv6l-unknown-linux-musleabihf.nix;
        x86_64-linux = import ./bootstrap-files/x86_64-unknown-linux-musl.nix;
      };
    };

    # Try to find an architecture compatible with our current system
    getCompatibleTools = lib.foldl (
      v: system:
      if v != null then
        v
      else if localSystem.canExecute (lib.systems.elaborate { inherit system; }) then
        archLookupTable.${system}
      else
        null
    ) null (lib.attrNames archLookupTable);

    archLookupTable = table.${localSystem.libc} or (throw "unsupported libc for the pure Linux stdenv");
    files =
      archLookupTable.${localSystem.system} or (
        if getCompatibleTools != null then
          getCompatibleTools
        else
          (throw "unsupported platform for the pure Linux stdenv")
      );
  in
  (config.replaceBootstrapFiles or lib.id) files,
```

### To Add Fil-C Bootstrap

```nix
bootstrapFiles ?
  let
    table = {
      glibc = { /* ... */ };
      musl = { /* ... */ };
      filc = {
        x86_64-linux = import ./bootstrap-files/x86_64-unknown-linux-filc.nix;
        aarch64-linux = import ./bootstrap-files/aarch64-unknown-linux-filc.nix;
        # ... other architectures ...
      };
    };
    # ... rest unchanged ...
```

**Important:** You need to create bootstrap file nix files for fil-c if doing full integration.

### Bootstrap Stage0 Libc Reference

**File:** `/home/mbrock/nixpkgs/pkgs/stdenv/linux/default.nix` (lines 273-289)

### Current Code

```nix
${localSystem.libc} = self.stdenv.mkDerivation {
  pname = "bootstrap-stage0-${localSystem.libc}";
  strictDeps = true;
  version = "bootstrapFiles";
  enableParallelBuilding = true;
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
  passthru.isFromBootstrapFiles = true;
};
```

### To Add Fil-C Support

```nix
${localSystem.libc} = self.stdenv.mkDerivation {
  pname = "bootstrap-stage0-${localSystem.libc}";
  strictDeps = true;
  version = "bootstrapFiles";
  enableParallelBuilding = true;
  buildCommand = ''
    mkdir -p $out
    ln -s ${bootstrapTools}/lib $out/lib
  ''
  + lib.optionalString (localSystem.libc == "glibc") ''
    ln -s ${bootstrapTools}/include-glibc $out/include
  ''
  + lib.optionalString (localSystem.libc == "musl") ''
    ln -s ${bootstrapTools}/include-libc $out/include
  ''
  + lib.optionalString (localSystem.libc == "filc") ''
    ln -s ${bootstrapTools}/include-filc $out/include
  '';
  passthru.isFromBootstrapFiles = true;
};
```

---

## File 7: Static Libraries Adapter

**File:** `/home/mbrock/nixpkgs/pkgs/stdenv/adapters.nix` (lines 124-144)

This pattern can be adapted for fil-c specific build flags:

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
        cmakeFlags = (args.cmakeFlags or [ ]) ++ [ "-DCMAKE_SKIP_INSTALL_RPATH=On" ];
      }
    );
  });
```

---

## File 8: Cc-Wrapper Integration

**File:** `/home/mbrock/nixpkgs/pkgs/build-support/cc-wrapper/default.nix` (lines 1-77)

The cc-wrapper is the integration point. Example from current flake.nix:

```nix
filc-wrapped = base.wrapCCWith {
  cc       = filc-cc.overrideAttrs (old: {
    passthru = (old.passthru or {}) // {
      libllvm = base.llvmPackages_20.libllvm;
    };
  });
  libc     = filc-libc;
  bintools = filc-bintools;
  isClang  = true;

  extraBuildCommands = ''
    echo "-gz=none" >> $out/nix-support/cc-cflags
    echo "-Wl,--compress-debug-sections=none" >> $out/nix-support/cc-cflags
    echo "-L${filc-libc}/lib" >> $out/nix-support/cc-cflags
    echo "-rpath ${filc-libc}/lib" >> $out/nix-support/cc-ldflags
    ln -s clang $out/bin/gcc
    ln -s clang++ $out/bin/g++
  '';    
};
```

---

## File 9: Static Builds Pattern (Reference)

**File:** `/home/mbrock/nixpkgs/pkgs/top-level/stage.nix` (lines 310-331)

### Current Code

```nix
pkgsStatic = nixpkgsFun {
  overlays = [
    (self': super': {
      pkgsStatic = super';
    })
  ]
  ++ overlays;
  crossSystem = {
    isStatic = true;
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

### Pattern for Fil-C Static

```nix
pkgsStaticFilC = nixpkgsFun {
  overlays = [
    (self': super': {
      pkgsStaticFilC = super';
    })
  ]
  ++ overlays;
  crossSystem = {
    isStatic = true;
    config = lib.systems.parse.tripleFromSystem (
      makeFilCParsedPlatform stdenv.hostPlatform.parsed
    );
  };
};
```

---

## File 10: Current Flake.nix Approach (Interim)

**File:** `/home/mbrock/filnix/flake.nix` (lines 220-226)

The current interim approach using `replaceStdenv`:

```nix
filpkgs = import nixpkgs {
  inherit system;
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-compat;
};
```

This approach:
- Doesn't modify nixpkgs source
- Only replaces the compiler, not the platform
- Reuses glibc but with fil-c compiler
- Works for immediate testing

To scale this up:

```nix
# In filnix/flake.nix, create a more complete variant:
filpkgs-full = import nixpkgs {
  inherit system;
  overlays = [
    (self: super: {
      filc-stdenv = super.stdenv.override (old: {
        cc = filc-wrapped;
        # Optional: override libc if fil-c has different ABI
      });
      # Override stdenv globally
      stdenv = self.filc-stdenv;
    })
  ];
};
```

---

## Summary of Changes Required

For a **full integration** of fil-c as `pkgsFilC` in nixpkgs:

1. **lib/systems/parse.nix** - Add filc and filceabi to abis
2. **lib/systems/inspect.nix** - Add isFilC predicate
3. **lib/systems/default.nix** - Add filc libc routing (optional if reusing musl string)
4. **pkgs/top-level/stage.nix** - Add makeFilCParsedPlatform and pass to variants
5. **pkgs/top-level/variants.nix** - Add pkgsFilC variant definition
6. **pkgs/top-level/all-packages.nix** - Add filc libc package selection
7. **pkgs/stdenv/linux/default.nix** - Add filc bootstrap file table
8. **pkgs/stdenv/linux/bootstrap-files/** - Create fil-c bootstrap nix files (optional)
9. **pkgs/by-name/fi/filc-libc/package.nix** - Create filc-libc package (if not already)

For **interim approach** (current flake.nix):

- Only need to wrap compiler and libc properly in cc-wrapper
- No nixpkgs source changes required
- Can test packages immediately

