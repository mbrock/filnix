# Build-platform code generators whose output targets Fil-C.
#
# GLib's gdbus-codegen and glib-genmarshal, Meson's mkenums_simple, valac,
# gtkdoc-scangobj and the introspection scanner's gdump.c emit C for the
# package being built. Under Fil-C that C must treat GType as a pointer.
# Like a compiler, these tools are target-dependent, so patch them in the
# package set whose target is Fil-C (pkgsBuildHost): splicing then selects
# them for Fil-C nativeBuildInputs.
# The native package set, whose target is not Fil-C, keeps its ordinary tools.
#
# GLib and gobject-introspection are native twins of the Fil-C ports, at the
# same versions: generated code must only use APIs the target GLib has, and
# Meson negotiates scanner options by the build GI's version. Only the
# target-neutral parts of the port patches apply; the rest assume Fil-C.
#
# The twins are tools, not libraries for the build platform. Replacing
# pkgsBuildHost's glib would relink every native library there against GLib
# 2.80.4 (Pango, GTK, Qt, glibmm, SDL's PipeWire...), rebuilding them outside
# the binary cache and breaking those that need a newer GLib. So the twins
# are built from pkgsBuildHost but only the Fil-C set's view of it,
# `pkgsBuildHost` (and so `buildPackages` and splicing), names them; native
# packages inside pkgsBuildHost keep the ordinary GLib.
final: prev:
let
  inherit (prev) lib;

  # The ports DSL for package set `pkgs`, applied to one of its packages.
  dsl = pkgs: import ./default.nix { inherit lib pkgs; };
  build =
    pkgs: pkg: steps:
    let
      spec = (dsl pkgs).for pkg steps;
    in
    (pkg.override spec.overrideArgs).overrideAttrs spec.attrs;

  # Native Qt programs must not propagate their native qtbase into Fil-C
  # builds. Only the Fil-C view below uses these program-only modules and
  # target hooks; native packages keep their ordinary Qt scope.
  qtToolsOnly =
    m:
    prev.runCommand "${m.name}-programs" { outputs = m.outputs or [ "out" ]; } (
      lib.concatMapStrings (o: ''
        mkdir -p ''$${o}
        if [ -d ${m.${o}}/bin ]; then ln -s ${m.${o}}/bin ''$${o}/bin; fi
      '') (m.outputs or [ "out" ])
    );
  unspliced = p: p.__spliced.hostTarget or p;
  qtForFilcBuilds =
    native: filc:
    native
    // lib.mapAttrs (_: qtToolsOnly) (
      lib.filterAttrs (
        name: v: lib.hasPrefix "qt" name && lib.isDerivation v
      ) native
    )
    // {
      qmake = prev.makeSetupHook {
        name = "qmake-hook";
        propagatedBuildInputs = [
          (unspliced filc.qmake)
          (unspliced filc.qtbase).dev
        ];
      } (prev.writeText "qmake-filc.sh" "");
      wrapQtAppsHook = prev.makeSetupHook {
        name = "wrap-qt5-apps-hook";
        propagatedBuildInputs = [
          (unspliced filc.qtbase).dev
          final.makeBinaryWrapper
          (unspliced filc.qtwayland).dev
        ];
      } (prev.path + "/pkgs/development/libraries/qt-5/hooks/wrap-qt-apps-hook.sh");
    };

  twins =
    bh:
    let
      inherit (dsl bh)
        arg
        use
        pin
        patch
        skipPatch
        ;

      # Select hunks of a port patch by file, keeping one source for them.
      hunks =
        name: portPatch: files:
        bh.runCommand name { nativeBuildInputs = [ bh.patchutils ]; } ''
          filterdiff ${lib.concatMapStringsSep " " (f: "-i '*/${f}'") files} \
            ${portPatch} > $out
          test -s $out
        '';

      glib = build bh bh.glib [
        (pin "2.80.4" "sha256-JOApxd/JtE5Fc2l63zMHipgnxIk4VVAEs7kJb6TqA08=")
        (patch (
          hunks "glib-filc-generators.patch" ../ports/patch/glib-2.80.4.patch [
            "gio/gdbus-2.0/codegen/codegen.py"
            "gobject/glib-genmarshal.in"
          ]
        ))
        (skipPatch "split-dev-programs.patch")
        (patch ../patches/glib-split-backport.patch)
        (arg {
          libsysprof-capture = null;
          # The Fil-C GI port supplies the target GLib GIRs.
          withIntrospection = false;
        })
        (use {
          doCheck = false;
          mesonFlags = [
            "-Ddevbindir=${placeholder "dev"}/bin"
            "-Dglib_debug=disabled"
            "-Ddocumentation=true"
            (lib.mesonBool "dtrace" false)
            (lib.mesonBool "systemtap" false)
            "-Dnls=enabled"
            (lib.mesonEnable "introspection" false)
            "-Dtests=false"
          ];
        })
        (use (old: {
          # Native build tools such as gdk-pixbuf propagate the ordinary
          # GLib, whose newer, unpatched generators can precede these on
          # PATH and in the build pkg-config path, where Meson looks them
          # up (gio-2.0's gdbus_codegen). Put these first once all hooks
          # have run.
          postFixup = (old.postFixup or "") + ''
            mkdir -p $dev/libexec/filc-generators
            for tool in gdbus-codegen glib-genmarshal glib-mkenums; do
              ln -s $dev/bin/$tool $dev/libexec/filc-generators/$tool
            done
            cat >> $dev/nix-support/setup-hook <<EOF

            _filcGlibGenerators() {
              PATH="$dev/libexec/filc-generators:\$PATH"
              export PKG_CONFIG_PATH_FOR_BUILD="$dev/lib/pkgconfig\''${PKG_CONFIG_PATH_FOR_BUILD:+:\$PKG_CONFIG_PATH_FOR_BUILD}"
            }
            postHooks+=(_filcGlibGenerators)
            EOF
          '';
        }))
      ];

      gobject-introspection-unwrapped =
        build bh bh.gobject-introspection-unwrapped
          [
            (arg {
              inherit glib;
              # Only its library path reaches the scanner; keep it the one the
              # twin has always had.
              cairo = bh.cairo.override { inherit glib; };
            })
            (pin "1.80.1" "sha256-od98Qk4VvaGrY5wA6QUbmt9c6hqeUS+KYDtTzRmbxtg=")
            (patch (
              hunks "gobject-introspection-filc-scanner.patch"
                ../ports/patch/gobject-introspection-1.80.1.patch
                [
                  "girepository/gdump.c"
                  "giscanner/ccompiler.py"
                ]
            ))
            (patch ../patches/gobject-introspection-filc-tools.patch)
            (patch ../patches/gobject-introspection-link-environment.patch)
            (use (old: {
              postPatch = (old.postPatch or "") + ''
                # Fil-C GLib's gtype.h provides uintptr_t; native GLib's does not.
                sed -i '/#include <stdio.h>/a #include <stdint.h>' girepository/gdump.c
                # Fil-C builds have no ldd on PATH; the scanner runs it on dumpers.
                substituteInPlace giscanner/shlibs.py \
                  --replace-fail "['ldd', binary.args[0]]" "['${lib.getBin bh.stdenv.cc.libc}/bin/ldd', binary.args[0]]"
              '';
              # Resolve GIR includes against the Fil-C libraries being linked
              # rather than build-platform GIRs, which XDG_DATA_DIRS lists first.
              # The scanner searches GI_GIR_PATH before XDG_DATA_DIRS.
              postFixup = (old.postFixup or "") + ''
                cat >> "$dev/nix-support/setup-hook" <<'EOF'

                _filcTargetGirPath() {
                  if [ -d "$1/share/gir-1.0" ]; then
                    addToSearchPath GI_GIR_PATH "$1/share/gir-1.0"
                  fi
                }
                addEnvHooks "$targetOffset" _filcTargetGirPath
                EOF
                # Native PyGObject propagates the ordinary GI, whose scanner
                # can precede this one on PATH; see the GLib twin.
                cat >> "$dev/nix-support/setup-hook" <<EOF
                _filcGirTools() {
                  PATH="$dev/bin:\$PATH"
                  export PKG_CONFIG_PATH_FOR_BUILD="$dev/lib/pkgconfig\''${PKG_CONFIG_PATH_FOR_BUILD:+:\$PKG_CONFIG_PATH_FOR_BUILD}"
                }
                postHooks+=(_filcGirTools)
                EOF
              '';
            }))
          ];
    in
    {
      inherit glib gobject-introspection-unwrapped;
      # The Fil-C-targeted wrapper, which the set itself no longer names.
      gobject-introspection = bh.callPackage (
        bh.path + "/pkgs/development/libraries/gobject-introspection/wrapper.nix"
      ) { inherit gobject-introspection-unwrapped; };
      # Like the GLib twins, these generators are patched only in the
      # Fil-C-facing view, not in native libraries' own build dependencies.
      gtk-doc = build bh bh.gtk-doc [
        (patch ../patches/gtk-doc-scangobj-gtype.patch)
      ];
      vala = build bh bh.vala [
        (patch ../patches/vala-pointer-once.patch)
        (use (old: {
          postPatch = (old.postPatch or "") + ''
            # Keep the shipped patched C from being regenerated by old valac.
            touch codegen/codegen.vala.stamp
          '';
          postFixup = (old.postFixup or "") + ''
            cat >> "$out/nix-support/setup-hook" <<'EOF'

            _filcValaRegenerate() {
              find . \( -name '*_vala.stamp' -o -name '*.vala.stamp' \) -delete
            }
            preConfigureHooks+=(_filcValaRegenerate)
            EOF
          '';
        }))
      ];
    };
in
if prev.stdenv.targetPlatform.isFilc && !prev.stdenv.hostPlatform.isFilc then
  let
    inherit (dsl prev) patch use;
  in
  {
    # Meson is not linked by native libraries, so it is patched for the whole
    # set; meson-python there propagates it to Fil-C Python builds.
    meson = build prev prev.meson [
      (patch ../patches/meson-gtype.patch)
    ];

    # Qt's qmake hook is spliced from this set's buildPackages. Here Qt still
    # differs from the native one without the GLib twin (qttools and so
    # qttranslations reference another qtbase), and a native Qt module here
    # (reached through wrapQtAppsHook, e.g. qtsvg) saw two qtbases: its
    # setup hook failed with "detected mismatched Qt dependencies". Qt
    # emits no GType code, so use the ordinary native Qt, which also comes
    # from cache.nixos.org.
    qt5 = final.buildPackages.qt5;
    libsForQt5 = final.buildPackages.libsForQt5;
    qt6 = final.buildPackages.qt6;
    qt6Packages = final.buildPackages.qt6Packages;
    # Likewise the gobject-introspection wrapper: with a Fil-C target it
    # wraps the scanner for cross use and propagates the Fil-C GI, so native
    # libraries here that link GI (PyGObject, and through it graphene, GTK 4,
    # GStreamer, PipeWire, SDL) left the cache. Fil-C packages get the
    # twin's wrapper from `twins` below.
    gobject-introspection = final.buildPackages.gobject-introspection;
    # PyGObject adds Python's pkg-config path when host != target, meaning
    # when cross-compiled (NixOS/nixpkgs#378447); here that holds natively.
    pythonPackagesExtensions = prev.pythonPackagesExtensions ++ [
      (_: pyprev: {
        pygobject3 = pyprev.pygobject3.overrideAttrs { preConfigure = ""; };
      })
    ];
  }
else if
  prev.stdenv.hostPlatform.isFilc && !prev.stdenv.buildPlatform.isFilc
then
  {
    # The default targetPackages.stdenv.cc bootstraps an ordinary LLVM cross
    # compiler for gnufilc0. Runtime wrappers are Fil-C programs too: compile
    # them with this set's existing Fil-C compiler, not a new cross toolchain.
    makeBinaryWrapper = prev.makeBinaryWrapper.override { cc = prev.stdenv.cc; };
    pkgsBuildHost =
      prev.pkgsBuildHost
      // twins prev.pkgsBuildHost
      // {
        qt5 = qtForFilcBuilds prev.pkgsBuildHost.qt5 final.qt5;
        libsForQt5 = qtForFilcBuilds prev.pkgsBuildHost.libsForQt5 final.libsForQt5;
      };
  }
else
  { }
