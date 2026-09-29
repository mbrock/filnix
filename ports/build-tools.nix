# Build-platform code generators whose output targets Fil-C.
#
# GLib's gdbus-codegen and glib-genmarshal, Meson's mkenums_simple and the
# introspection scanner's gdump.c emit C for the package being built. Under
# Fil-C that C must treat GType as a pointer. Like a compiler, these tools are
# target-dependent, so patch them in the package set whose target is Fil-C
# (pkgsBuildHost): splicing then selects them for Fil-C nativeBuildInputs.
# The native package set, whose target is not Fil-C, keeps its ordinary tools.
#
# GLib and gobject-introspection are native twins of the Fil-C ports, at the
# same versions: generated code must only use APIs the target GLib has, and
# Meson negotiates scanner options by the build GI's version. Only the
# target-neutral parts of the port patches apply; the rest assume Fil-C.
final: prev:
let
  inherit (prev) lib;
  inherit
    (import ./default.nix {
      inherit lib;
      pkgs = prev;
    })
    for
    arg
    use
    pin
    patch
    skipPatch
    ;

  # Select hunks of a port patch by file, keeping one source for them.
  hunks =
    name: portPatch: files:
    prev.runCommand name { nativeBuildInputs = [ prev.patchutils ]; } ''
      filterdiff ${lib.concatMapStringsSep " " (f: "-i '*/${f}'") files} \
        ${portPatch} > $out
      test -s $out
    '';

  ports = {
    glib = for prev.glib [
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
    ];

    gobject-introspection-unwrapped = for prev.gobject-introspection-unwrapped [
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
            --replace-fail "['ldd', binary.args[0]]" "['${lib.getBin prev.stdenv.cc.libc}/bin/ldd', binary.args[0]]"
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
        '';
      }))
    ];

    meson = for prev.meson [ (patch ../patches/meson-gtype.patch) ];
  };

  # Qt 5 as seen from Fil-C nativeBuildInputs (see qt5 below). The native
  # modules' setup hooks register their qtbase, and the Fil-C qtbase's hook
  # then fails with "detected mismatched Qt dependencies"; with qttools
  # (lrelease) or wrapQtAppsHook in nativeBuildInputs, every Fil-C Qt 5
  # program did. Give Fil-C builds only the modules' programs, and the
  # Fil-C scope's own qmake and wrapQtAppsHook hooks, which bring the Fil-C
  # qtbase (its qmake, moc, uic and rcc run on the build machine). The
  # native scope itself is unchanged, so native Qt packages still build
  # against the native Qt.
  qtToolsOnly =
    m:
    prev.runCommand "${m.name}-programs" { outputs = m.outputs or [ "out" ]; } (
      lib.concatMapStrings (o: ''
        mkdir -p ''$${o}
        if [ -d ${m.${o}}/bin ]; then ln -s ${m.${o}}/bin ''$${o}/bin; fi
      '') (m.outputs or [ "out" ])
    );
  qtForFilcBuilds =
    native: filc:
    native
    // lib.mapAttrs (_: qtToolsOnly) (
      lib.filterAttrs (
        name: v: lib.hasPrefix "qt" name && lib.isDerivation v
      ) native
    )
    // {
      qmake = filc.qmake.__spliced.hostTarget or filc.qmake;
      wrapQtAppsHook = filc.wrapQtAppsHook.__spliced.hostTarget or filc.wrapQtAppsHook;
    };
in
lib.optionalAttrs
  (prev.stdenv.targetPlatform.isFilc && !prev.stdenv.hostPlatform.isFilc)
  (
    lib.mapAttrs (
      name: spec: (prev.${name}.override spec.overrideArgs).overrideAttrs spec.attrs
    ) ports
    // {
      # The overrides above change every native package here that links
      # GLib, including Qt 5, so this set's qtbase differed from the one in
      # its own buildPackages. Qt's qmake hook is spliced from there, so a
      # native Qt module (reached through wrapQtAppsHook, e.g. qtsvg) saw
      # two qtbases and its setup hook failed with "detected mismatched Qt
      # dependencies". moc, uic, rcc and qmake emit no GType code, so
      # use the ordinary native Qt 5.
      qt5 = qtForFilcBuilds final.buildPackages.qt5 final.targetPackages.qt5;
      libsForQt5 = qtForFilcBuilds final.buildPackages.libsForQt5 final.targetPackages.libsForQt5;
      # The same holds for Qt 6: a native qttools here linked the GLib twin's
      # headers against GLib 2.88's libgio and failed on
      # g_variant_builder_init_static.
      qt6 = final.buildPackages.qt6;
      qt6Packages = final.buildPackages.qt6Packages;
      # Graphviz (for docs, e.g. FLAC's) only emits target-neutral output,
      # but here it would see the GLib twin, which is older than Pango
      # requires; pangocairo then goes missing and the build fails on vimdot.
      graphviz = prev.buildPackages.graphviz;
    }
  )
