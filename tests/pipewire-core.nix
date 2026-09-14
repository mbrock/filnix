# Experimental profile; both known test failures remain enabled.
let
  f = builtins.getFlake (toString ../.);
  p = f.legacyPackages.x86_64-linux.pkgsFilc;
  native = import f.inputs.nixpkgs { system = "x86_64-linux"; };
in
p.stdenv.mkDerivation {
  pname = "pipewire-core-probe";
  inherit (p.pipewire) version src;
  patches = [
    ../patches/pipewire-log-topics.patch
    ../patches/pipewire-test-suites.patch
    ../patches/pipewire-pulse-modules.patch
    ../patches/pipewire-cpu-probe.patch
    ../patches/pipewire-pointer-arithmetic.patch
    ../patches/pipewire-test-runtime.patch
  ];
  NIX_CFLAGS_COMPILE = "-DNVALGRIND";
  preCheck = ''
    export FUGC_THREADS="$NIX_BUILD_CORES"
    mesonCheckFlagsArray+=(--num-processes "$NIX_BUILD_CORES")
  '';
  nativeBuildInputs = [
    native.meson
    native.ninja
    native.pkg-config
    native.python3
  ];
  depsBuildBuild = [ native.stdenv.cc ];
  buildInputs = [
    p.alsa-lib
    p.systemdLibs
    p.dbus
    p.glib
  ];
  mesonFlags = [
    "-Dauto_features=disabled"
    "-Dexamples=disabled"
    "-Dtests=enabled"
    "-Dspa-plugins=enabled"
    "-Dsupport=enabled"
    "-Daudioconvert=enabled"
    "-Daudiomixer=enabled"
    "-Daudiotestsrc=enabled"
    "-Dcontrol=enabled"
    "-Dtest=enabled"
    "-Dvolume=enabled"
    "-Dvideoconvert=enabled"
    "-Dvideotestsrc=enabled"
    "-Dalsa=enabled"
    "-Dpipewire-alsa=enabled"
    "-Dsystemd=enabled"
    "-Dlogind=enabled"
    "-Ddbus=enabled"
    "-Dsession-managers=[]"
    "-Dsysconfdir=etc"
    "-Drlimits-install=false"
  ];
  doCheck = true;
  strictDeps = true;
}
