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
in
lib.optionalAttrs
  (prev.stdenv.targetPlatform.isFilc && !prev.stdenv.hostPlatform.isFilc)
  (
    lib.mapAttrs (
      name: spec: (prev.${name}.override spec.overrideArgs).overrideAttrs spec.attrs
    ) ports
  )
