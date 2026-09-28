# PipeWire consumers ported against the full PipeWire package.
{
  pkgs,
  prev,
  final,
}:
let
  inherit
    (import ./default.nix {
      inherit pkgs;
      inherit (pkgs) lib;
    })
    for
    arg
    use
    configure
    patch
    ;
in
{
  sdl3 = for "sdl3" [
    (patch ../patches/sdl3-fork.patch)
    (patch ../patches/sdl3-cpu-probe.patch)
    (patch ../patches/sdl3-aligned-allocation.patch)
    (patch ../patches/sdl3-process-fork.patch)
    (patch ../patches/sdl3-testfile-buffer.patch)
    (arg {
      # First pass: PipeWire/ALSA audio and X11 software rendering.
      # The GPU and alternate audio stacks have independent campaign blockers.
      drmSupport = false;
      openglSupport = false;
      waylandSupport = false;
      libdecorSupport = false;
      ibusSupport = false;
      jackSupport = false;
      pulseaudioSupport = false;
      vulkanSupport = false;
      traySupport = false;
    })
    (use (old: {
      cmakeFlags = old.cmakeFlags ++ [
        "-DSDL_MMX=OFF"
      ];
      # Nixpkgs links SDL's backends directly (SDL_DEPS_SHARED=OFF), so this
      # is normally a no-op; it guards against any backend left on dlopen.
      postConfigure = (old.postConfigure or "") + ''
        # Fil-C forwards dlopen through libc, losing SDL's caller RUNPATH.
        # Pin every configured backend to the dependency selected by Nix.
        ${pkgs.python3}/bin/python ${./pin-sdl-libraries.py} \
          include-config-release/build_config/SDL_build_config.h \
          ${pkgs.lib.escapeShellArgs (
            map (p: "${pkgs.lib.getLib p}/lib") old.buildInputs
          )}
      '';
      # testrwlock's writer can starve behind six readers that each hold
      # the lock for a second; nixpkgs already calls it intermittent, and
      # it timed out on a loaded builder.
      postPatch = (old.postPatch or "") + ''
        substituteInPlace test/CMakeLists.txt --replace-fail \
          'add_sdl_test_executable(testrwlock SOURCES testrwlock.c NONINTERACTIVE NONINTERACTIVE_TIMEOUT 300)' \
          'add_sdl_test_executable(testrwlock SOURCES testrwlock.c)'
      '';
      preCheck = (old.preCheck or "") + ''
        export FUGC_THREADS="$NIX_BUILD_CORES"
      '';
      doCheck = true;
    }))
  ];

  sdl2-compat = for "sdl2-compat" [
    (patch ../patches/sdl2-symbol-loader.patch)
    (patch ../patches/sdl2-capabilities.patch)
    (patch ../patches/sdl2-testfile-buffer.patch)
    (use (old: {
      # This cohort's SDL3 has no OpenGL backend; keep the non-GL tests.
      checkInputs = [ ];
      # Fil-C's function descriptors reference the implementation through
      # an interposable global symbol. With sdl12-compat loaded, whose
      # SDL_* functions share these names, dlsym(libSDL2, "SDL_strrchr")
      # would return a descriptor pointing back into sdl12-compat, which
      # then recursed forever. Bind libSDL2's own functions locally.
      cmakeFlags = (old.cmakeFlags or [ ]) ++ [
        "-DCMAKE_SHARED_LINKER_FLAGS=-Wl,-Bsymbolic-functions"
      ];
      postPatch = (old.postPatch or "") + ''
        # Keep SDL3 local to dlopen: direct linking would interpose SDL2 names.
        substituteInPlace src/sdl2_compat.c \
          --replace-fail '"libSDL3.so.0"' '"${pkgs.lib.getLib final.sdl3}/lib/libSDL3.so.0"'
      '';
      preCheck = (old.preCheck or "") + ''
        export FUGC_THREADS="$NIX_BUILD_CORES"
      '';
    }))
  ];

  cava = for "cava" [
    (configure "--disable-input-pulse")
    (use (old: {
      postPatch = (old.postPatch or "") + ''
        ${pkgs.python3}/bin/python ${./cava-resources.py}
      '';
    }))
    (use (old: {
      buildInputs = builtins.filter (
        dep:
        !(builtins.elem (dep.pname or "") [
          "pulseaudio"
          "libpulseaudio"
        ])
      ) old.buildInputs;
    }))
  ];

  wireplumber = for "wireplumber" [
    (patch ../patches/wireplumber-gtype.patch)
    (patch ../patches/wireplumber-pointer-properties.patch)
    (arg {
      systemd = final.systemdLibs;
      enableDocs = false;
    })
    (use (old: {
      doCheck = true;
      nativeCheckInputs = (old.nativeCheckInputs or [ ]) ++ [ pkgs.dbus ];
      mesonFlags =
        builtins.filter (
          flag: !(pkgs.lib.hasPrefix "-Dsysconfdir=" flag)
        ) old.mesonFlags
        ++ [
          "-Dsysconfdir=etc"
        ];
      preCheck = (old.preCheck or "") + ''
        export FUGC_THREADS="$NIX_BUILD_CORES"
        mesonCheckFlagsArray+=(--num-processes "$NIX_BUILD_CORES")
      '';
    }))
  ];
}
