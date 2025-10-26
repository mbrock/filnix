{ base, filenv }:

let
  lib = base.lib;
  commonTools = with base; [ perl pkg-config autoconf automake libtool python3 ccache ];

  # Filter filc-sources to only include a specific project directory
  # This ensures each project only depends on its own source, not the entire monorepo
  filterProject = filc-sources: projectPath: 
    builtins.path {
      path = filc-sources;
      name = "filc-project-${baseNameOf projectPath}";
      filter = path: type:
        let
          relPath = lib.removePrefix (toString filc-sources + "/") (toString path);
          # Keep only files in the specific project directory
          inProject = lib.hasPrefix projectPath relPath || relPath == projectPath;
        in
        path == filc-sources || inProject;  # Always include root
    };

  mkSrc = filc-sources: path: "${filterProject filc-sources path}/${path}";

in rec {
  # Minimal builder - just sets CC/CXX/out and runs commands
  minimal = filc-sources: pname: version: {
    src ? "${pname}-${version}",
    script
  }:
    base.runCommand "${pname}-${version}" {
      src = mkSrc filc-sources src;
      nativeBuildInputs = [ filenv.cc ] ++ (with base; [ gnumake findutils gnused gnugrep coreutils ]);
    } ''
      # Copy source
      cp -r $src ./build-src
      chmod -R u+w ./build-src
      cd ./build-src
      
      # Set minimal environment - just what fil-c uses
      export CC=${filenv.cc}/bin/clang
      export CXX=${filenv.cc}/bin/clang++
      export out=$out
      export NIX_BUILD_CORES=''${NIX_BUILD_CORES:-1}
      
      # Run the build script
      ${script}
    '';

  # Generic package builder with full control over all phases
  package = filc-sources: pname: version: {
    src ? "${pname}-${version}",
    needs ? [],
    tools ? [],
    flags ? [],
    pre ? null,
    configure ? null,
    build ? null,
    install ? null
  }:
    filenv.mkDerivation ({
      inherit pname version;
      src = mkSrc filc-sources src;
      buildInputs = needs;
      nativeBuildInputs = commonTools ++ tools;
      enableParallelBuilding = true;
      prePatch = "patchShebangs .";
      preConfigure = ''
        export CCACHE_DIR=/nix/var/cache/ccache
        export CCACHE_COMPRESS=1
        ${if pre != null then pre else ""}
      '';
    } // (if configure != null then { configurePhase = configure; } else {})
      // (if build != null then { buildPhase = build; } else {})
      // (if install != null then { installPhase = install; } else {})
      // (if flags != [] then { configureFlags = flags; } else {}));

  # Autotools-based projects (./configure && make && make install)
  configure = filc-sources: pname: version: { 
    src ? "${pname}-${version}", 
    flags ? [],
    needs ? [], 
    tools ? [],
    pre ? null
  }:
    filenv.mkDerivation ({
      inherit pname version;
      src = mkSrc filc-sources src;
      buildInputs = needs;
      nativeBuildInputs = commonTools ++ tools;
      configureFlags = flags;
      enableParallelBuilding = true;
      prePatch = "patchShebangs .";
      preConfigure = ''
        export CCACHE_DIR=/nix/var/cache/ccache
        export CCACHE_COMPRESS=1
        ${if pre != null then pre else ""}
      '';
    } // {});

  # CMake-based projects
  cmake = filc-sources: pname: version: { 
    src ? "${pname}-${version}", 
    flags ? [], 
    needs ? [], 
    tools ? [] 
  }:
    filenv.mkDerivation {
      inherit pname version;
      src = mkSrc filc-sources src;
      buildInputs = needs;
      nativeBuildInputs = commonTools ++ tools ++ (with base; [ base.cmake ninja ]);
      cmakeFlags = flags;
      enableParallelBuilding = true;
      prePatch = "patchShebangs .";
      preConfigure = ''
        export CCACHE_DIR=/nix/var/cache/ccache
        export CCACHE_COMPRESS=1
      '';
    };

  # Make-based projects (just make && make install)
  make = filc-sources: pname: version: { 
    src ? "${pname}-${version}", 
    flags ? [],
    needs ? [], 
    tools ? [], 
    install ? null 
  }:
    filenv.mkDerivation ({
      inherit pname version;
      src = mkSrc filc-sources src;
      buildInputs = needs;
      nativeBuildInputs = commonTools ++ tools ++ (with base; [ gnumake ]);
      makeFlags = flags;
      enableParallelBuilding = true;
      prePatch = "patchShebangs .";
      preConfigure = ''
        export CCACHE_DIR=/nix/var/cache/ccache
        export CCACHE_COMPRESS=1
      '';
    } // (if install != null then { installPhase = install; } else {}));
}
