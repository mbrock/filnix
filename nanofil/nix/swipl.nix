# SWI-Prolog 9.2.9 built entirely by nanofil, with filnix's port of it
# (ports.nix's swi-prolog: patches/swi-prolog-9.2.9-filc.patch) and the
# port's packages: the core, the packages that need no further library
# (chr, clib, clpqr, http, nlp, pengines, pldoc, plunit, RDF, semweb,
# sgml, table, utf8proc, zlib, ...) and pcre, yaml and ssl. GMP, zlib,
# OpenSSL, PCRE2, libyaml and libxcrypt are staging filnix's ports.
#
# CMake configures with filcc; ninja then compiles every C file with
# nanofil-cc (CMAKE_C_COMPILER_LAUNCHER), mkvmi and defatom included, and
# every object must come from nanofil. The build runs the nanofil-built
# swipl: it compiles SWI's boot file and its library to QLF, bootstraps
# CHR and builds the library indexes, and home/ (boot.prc's contents, every
# .qlf and INDEX.pl) must equal filcc's byte for byte, apart from the
# padded PID of a QLF file's temporary name: both builds run in the
# same directory, in their own derivations. Then the deterministic
# workload (workloads/swipl.pl) must print what filcc's prints, plainly
# and under FUGC_SCRIBBLE and FUGC_VERIFY, and SWI's own test suite
# (ctest) must give each test the result it gives filcc's build. Once
# per configuration (plain and -O), each in its own derivation.
{
  pkgs,
  filcc,
  pkgsFilc,
}:
assert pkgs.swi-prolog.version == "9.2.9";
let
  inherit (pkgs) lib;
  src = pkgs.swi-prolog.src;
  workload = ./workloads/swipl.pl;
  libs = with pkgsFilc; [
    gmp
    gmp.dev
    zlib
    zlib.dev
    openssl
    openssl.dev
    pcre2
    pcre2.dev
    libyaml
    libyaml.dev
    libxcrypt
  ];
  packages = lib.concatStringsSep ";" [
    "chr"
    "clib"
    "clpqr"
    "inclpr"
    "http"
    "nlp"
    "paxos"
    "redis"
    "stomp"
    "pengines"
    "pldoc"
    "plunit"
    "protobufs"
    "RDF"
    "semweb"
    "sgml"
    "table"
    "utf8proc"
    "zlib"
    "pcre"
    "yaml"
    "ssl"
  ];
  nativeBuildInputs = [
    pkgs.cmake
    pkgs.ninja
    pkgs.unzip
  ];
  # Configure in /build/swipl/build, the same path in every derivation,
  # so that the QLF files, which record source paths, can be compared.
  configure = ''
    cd $NIX_BUILD_TOP
    cp -r --no-preserve=mode ${src} swipl
    patch -d swipl -p1 <${../../patches/swi-prolog-9.2.9-filc.patch}
    # A QLF file can record the temporary file SWI writes it to,
    # .NAME.qlf.PID ('$stage_file'/2): pad the PID to ten digits, so
    # that files and their offsets have one length whatever the PID,
    # and the comparison below masks the digits.
    sed -i "s|'~w/.~w.~d', \\[Dir,File,Pid\\]|'~w/.~w.~\\|~\`0t~d~10+', [Dir,File,Pid]|" swipl/boot/init.pl
    grep -q '~10+' swipl/boot/init.pl
    # QLF files record their sources' modification times.
    find swipl -exec touch -h -d @1 {} +
    mkdir swipl/build
    cd swipl/build
    export CC=${filcc}/bin/clang
    export CMAKE_PREFIX_PATH=${lib.concatStringsSep ":" libs}
    export CFLAGS="${
      lib.concatMapStringsSep " " (p: "-I${lib.getDev p}/include") libs
    }"
    export LDFLAGS="-L${pkgsFilc.libxcrypt}/lib"
    cmake -G Ninja -DCMAKE_BUILD_TYPE=Release -DUSE_GMP=ON -DUSE_TCMALLOC=OFF \
      -DINSTALL_DOCUMENTATION=OFF -DSWIPL_INSTALL_IN_LIB=ON -DHAVE_SIGALTSTACK= \
      "-DSWIPL_PACKAGE_LIST=${packages}" .. >cmake.log 2>&1 || { cat cmake.log; exit 1; }
  '';
  # results: each ctest test and its outcome, in name order. The C stack
  # is 32 MB: analyseVariables2 (pl-comp.c) recurses 10,000 levels into a
  # cyclic term before it checks for a cycle, and its frame is 216 bytes
  # from clang, 512 from nanofil -O and 864 plain, past 8 MB (Fil-C stops
  # the overflow safely; test_db's cyclic_head and test_gc trap). Failed
  # tests run once more, alone, and that result counts: http:proxy's
  # "unused" port is one it found free and released, which a test running
  # beside it can take (filcc's build fails it so too, now and then).
  ctest = out: ''
    (ulimit -s 32768 && ctest -j$NIX_BUILD_CORES --timeout 1800 --output-on-failure >${out}.log 2>&1 || true)
    (ulimit -s 32768 && ctest --rerun-failed --timeout 1800 --output-on-failure >>${out}.log 2>&1 || true)
    grep -E '^ *[0-9]+/[0-9]+ Test +#' ${out}.log \
      | sed -E 's/.*Test +#[0-9]+: ([^ ]+) \.*[* ]*([A-Za-z]+).*/\1 \2/' \
      | awk '{ r[$1] = $2 } END { for (t in r) print t, r[t] }' | sort >${out}
    test -s ${out}
  '';
  reference =
    pkgs.runCommandCC "nanofil-swipl-reference" { inherit nativeBuildInputs; }
      ''
        ${configure}
        ninja -j$NIX_BUILD_CORES >ninja.log 2>&1 || { tail -50 ninja.log; exit 1; }
        ${ctest "ctest.results"}
        mkdir $out
        cp ctest.results ctest.results.log $out/
        (cd /tmp && $NIX_BUILD_TOP/swipl/build/src/swipl ${workload} >$out/workload.out 2>&1)
        find . -name '*.o' -delete
        tar -cf $out/build.tar -C $NIX_BUILD_TOP swipl
      '';
in
import ./configurations.nix { inherit pkgs; } "nanofil-swipl"
  {
    plain = "";
    O = "-O";
  }
  (
    label: opt:
    pkgs.runCommandCC "nanofil-swipl-${label}" { inherit nativeBuildInputs; } ''
      ${configure}
      # Nix stops a build after 15 minutes without output, and ninja's and
      # ctest's go to files: the plain build alone takes about that long.
      (while sleep 300; do echo "(still running)"; done) &
      trap "kill $!" EXIT
      launcher=$NIX_BUILD_TOP/nanofil-launcher
      printf '#!${pkgs.runtimeShell}\nshift\nexec ${
        import ./nanofil-cc.nix { inherit pkgs filcc; }
      } "$@"\n' >$launcher
      chmod +x $launcher
      cmake -DCMAKE_C_COMPILER_LAUNCHER=$launcher . >>cmake.log 2>&1
      echo "== SWI-Prolog 9.2.9, nanofil ${opt}"
      export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
      start=$SECONDS
      ninja -j$NIX_BUILD_CORES >ninja.log 2>&1 || { grep -B2 -A20 FAILED ninja.log | head -80; exit 1; }
      echo "built in $((SECONDS - start)) s"
      # Compare paths, not just counts: no object may come from clang.
      find . -name '*.o' -not -path './CMakeFiles/*' -printf '%P\n' | sort >../objects
      sort -u nanofil.log >../compiled
      test -s ../objects
      diff -u ../objects ../compiled
      echo "nanofil compiled every one of $(wc -l <../objects) SWI-Prolog objects"
      mkdir -p $out
      cp ../compiled $out/compiled-objects.txt
      tar -xf ${reference}/build.tar -C $NIX_BUILD_TOP --transform 's,^swipl,ref,'
      # boot.prc is a zip whose entry headers carry the time it was
      # written: compare its contents. QLF files are compared with the
      # padded PIDs of their temporary names masked.
      ref=$NIX_BUILD_TOP/ref/build/home
      mask() { ${pkgs.perl}/bin/perl -0777 -pe 's/(\.qlf\.)\d{10}/''${1}0000000000/g' "$@"; }
      diff -r -x boot.prc -x '*.qlf' -x '*.qlf.*' $ref home
      # same NAME REF NEW: they are equal, or NAME and the bytes around
      # the first difference are shown.
      same() {
        cmp $2 $3 >/dev/null && return
        local at=$(cmp $2 $3 | sed -E 's/.* ([0-9]+), line.*/\1/')
        echo "$1 differs from filcc's at byte $at:"
        od -A d -c -j $((at > 96 ? at - 96 : 0)) -N 192 $2
        od -A d -c -j $((at > 96 ? at - 96 : 0)) -N 192 $3
        return 1
      }
      unzip -p $ref/boot.prc | mask >../ref.state; unzip -p home/boot.prc | mask >../new.state
      same boot.prc ../ref.state ../new.state
      diff <(cd $ref && find . -name '*.qlf' | sort) <(cd home && find . -name '*.qlf' | sort)
      for f in $(cd home && find . -name '*.qlf'); do
        mask $ref/$f >../ref.qlf; mask home/$f >../new.qlf
        same $f ../ref.qlf ../new.qlf
      done
      echo "the nanofil-built swipl compiled boot.prc and $(find home -name '*.qlf' | wc -l) QLF files as filcc's did"
      for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
        (cd /tmp && env $env $NIX_BUILD_TOP/swipl/build/src/swipl ${workload} >$NIX_BUILD_TOP/nf.out 2>&1)
        diff -u ${reference}/workload.out $NIX_BUILD_TOP/nf.out
        echo "workload matches filcc's: $(grep -c '^## ' $NIX_BUILD_TOP/nf.out) sections ($env)"
      done
      ${ctest "ctest.results"}
      cp ctest.results ctest.results.log $out/
      diff -u ${reference}/ctest.results ctest.results || {
        grep -a -B3 -A40 -E 'filc (safety error|panic)|\*\*FAILED' ctest.results.log | head -300
        exit 1
      }
      echo "ctest: $(awk '{print $2}' ctest.results | sort | uniq -c | tr -s ' \n' ' '), as filcc's"
    ''
  )
