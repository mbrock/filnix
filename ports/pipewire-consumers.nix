# Explicit first cohort. Do not replace stdenv or pipewire in the whole scope.
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
  private = import ../toolchain/cancellation.nix {
    inherit pkgs;
    baseStdenv = prev.stdenv;
  };
  pipewire =
    (import ../packages/pipewire-core.nix {
      native = pkgs;
      p = final;
      stdenv = private.stdenv;
    }).overrideAttrs
      { pname = "pipewire-core"; };
  consumer =
    name: steps:
    for name (
      [
        (arg { stdenv = private.stdenv; })
        (use (old: {
          passthru = (old.passthru or { }) // {
            filcRuntime = {
              name = "pipewire-cancellation";
              inherit (private) libc cc;
              inherit pipewire;
            };
          };
        }))
      ]
      ++ steps
    );
in
{
  sdl3 = consumer "sdl3" [
    (patch ../patches/sdl3-fork.patch)
    (patch ../patches/sdl3-cpu-probe.patch)
    (patch ../patches/sdl3-aligned-allocation.patch)
    (arg {
      inherit pipewire;
      # First pass: PipeWire/ALSA audio and X11 software rendering.
      # The GPU and alternate audio stacks have independent campaign blockers.
      drmSupport = false;
      openglSupport = false;
      waylandSupport = false;
      libdecorSupport = false;
      ibusSupport = false;
      jackSupport = false;
      pulseaudioSupport = false;
    })
    (use (
      old:
      let
        dlopenInputs = builtins.filter (
          dep:
          !(builtins.elem (dep.pname or "") [
            "libayatana-appindicator"
            "vulkan-loader"
            "vulkan-headers"
          ])
        ) old.dlopenBuildInputs;
      in
      {
        dlopenBuildInputs = dlopenInputs;
        cmakeFlags = old.cmakeFlags ++ [
          "-DSDL_VULKAN=OFF"
          "-DSDL_MMX=OFF"
        ];
        postConfigure = (old.postConfigure or "") + ''
          # Fil-C forwards dlopen through libc, losing SDL's caller RUNPATH.
          # Pin every configured backend to the dependency selected by Nix.
          ${pkgs.python3}/bin/python ${./pin-sdl-libraries.py} \
            include-config-release/build_config/SDL_build_config.h \
            ${pkgs.lib.escapeShellArgs (
              map (p: "${pkgs.lib.getLib p}/lib") dlopenInputs
            )}
        '';
        preCheck = (old.preCheck or "") + ''
          export FUGC_THREADS="$NIX_BUILD_CORES"
        '';
        doCheck = true;
      }
    ))
  ];

  sdl2-compat = consumer "sdl2-compat" [
    (patch ../patches/sdl2-symbol-loader.patch)
    (patch ../patches/sdl2-capabilities.patch)
    (use (old: {
      # This cohort's SDL3 has no OpenGL backend; keep the non-GL tests.
      checkInputs = [ ];
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

  cava = consumer "cava" [
    (arg {
      inherit pipewire;
      # CAVA uses FFTW's C API. Avoid the unsupported target Fortran compiler
      # and OpenMP runtime without changing FFTW for other packages.
      fftw = final.fftw.overrideAttrs (old: {
        patches = (old.patches or [ ]) ++ [
          ../patches/fftw-cpu-probe.patch
          ../patches/fftw-pointer-tags.patch
          ../patches/fftw-vector-load.patch
        ];
        nativeBuildInputs = builtins.filter (
          dep: !(pkgs.lib.hasInfix "gfortran" (dep.name or ""))
        ) old.nativeBuildInputs;
        configureFlags =
          builtins.filter (
            f:
            !(builtins.elem f [
              "--enable-openmp"
              "--enable-avx512"
            ])
          ) old.configureFlags
          ++ [
            "--disable-fortran"
            "--disable-openmp"
            # Fil-C does not yet lower AVX-512 gather intrinsics.
            "--disable-avx512"
          ];
        doCheck = true;
      });
    })
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

  wireplumber = consumer "wireplumber" [
    (patch ../patches/wireplumber-gtype.patch)
    (patch ../patches/wireplumber-pointer-properties.patch)
    (arg {
      inherit pipewire;
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
        ++ [ "-Dsysconfdir=etc" ];
      preCheck = (old.preCheck or "") + ''
        export FUGC_THREADS="$NIX_BUILD_CORES"
        mesonCheckFlagsArray+=(--num-processes "$NIX_BUILD_CORES")
      '';
    }))
  ];
}
