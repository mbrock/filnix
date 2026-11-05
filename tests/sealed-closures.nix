# Sealed closures (zclosure_new_sealed, staging only): the body reads its data,
# and every other way through the closure to that data is a safety error.
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-sealed-closures-check";
  dontUnpack = true;
  buildPhase = ''
    export FUGC_THREADS=2
    for opt in -O0 -O2; do
      $CC $opt ${./sealed-closures/sealed.c} -o sealed
      ./sealed | grep -qx 'sealed closures ok'

      $CC $opt ${./sealed-closures/probe.c} -o probe
      for mode in get:'is sealed' set:'is sealed' get-self:'is sealed' \
                  rebind:'cannot make a closure from sealed closure' \
                  rebind-sealed:'cannot make a closure from sealed closure' \
                  read:'filc safety error' plain:'is not a closure' \
                  inline:'is not a closure'; do
        if ./probe "''${mode%%:*}" > probe.log 2>&1; then
          echo "probe ''${mode%%:*} exited successfully" >&2
          cat probe.log >&2
          exit 1
        fi
        grep -q 'filc safety error' probe.log
        grep -q "''${mode#*:}" probe.log
        if grep -q LEAK probe.log; then
          echo "probe ''${mode%%:*} leaked" >&2
          exit 1
        fi
      done
    done
  '';
  installPhase = "touch $out";
}
