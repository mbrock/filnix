# Deliberate core feature profile; dependencies remain in the ordinary scope.
{
  native,
  p,
  stdenv ? p.stdenv,
}:
stdenv.mkDerivation {
  pname = "pipewire-core";
  # The pointer-token patches below were ported and tested against 1.4.7;
  # Nixpkgs 26.05 packages 1.6, which moves and adds pointer-string sites.
  version = "1.4.7";
  src = native.fetchFromGitLab {
    domain = "gitlab.freedesktop.org";
    owner = "pipewire";
    repo = "pipewire";
    rev = "1.4.7";
    hash = "sha256-U9J7f6nDO4tp6OCBtBcZ9HP9KDKLfuuRWDEbgLL9Avs=";
  };
  patches = [
    ../patches/pipewire-log-topics.patch
    ../patches/pipewire-test-suites.patch
    ../patches/pipewire-pulse-modules.patch
    ../patches/pipewire-cpu-probe.patch
    ../patches/pipewire-pointer-arithmetic.patch
    ../patches/pipewire-pointer-properties.patch
    ../patches/pipewire-test-runtime.patch
  ];
  NIX_CFLAGS_COMPILE = "-DNVALGRIND";
  preConfigure = ''
    mesonFlagsArray+=(
      "-Dudevrulesdir=$out/lib/udev/rules.d"
      "-Dsystemd-system-unit-dir=$out/lib/systemd/system"
      "-Dsystemd-user-unit-dir=$out/lib/systemd/user"
    )
  '';
  preCheck = ''
    export FUGC_THREADS="$NIX_BUILD_CORES"
    for module in a b; do
      $CC -shared -fPIC -I../spa/include \
        ${../tests/pipewire-pointer-module.c} -Lspa -lspa-filc-pointers \
        -Wl,-rpath,"$PWD/spa" -o "pointer-$module.so"
    done
    $CC -O2 ${../tests/pipewire-pointer-properties.c} -ldl -pthread -o pointer-check
    timeout 30 ./pointer-check
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
