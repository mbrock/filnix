# CPython 3.12.5 built entirely by nanofil, with filnix's port of it
# (ports.nix's python312: the Fil-C patch, pymalloc and freelists off,
# no x87 or x64 inline assembly). nixpkgs pins 3.13, which the port
# marks broken, so the check builds the port's version. configure runs
# with filcc; make then runs with CC=nanofil-cc (with configure's
# -std=gnu23), and every object of the interpreter, its test modules
# and its 62 extension modules must come from nanofil. The modules
# that need libraries the sandbox lacks (zlib, bz2, lzma, OpenSSL,
# ctypes, sqlite, curses, readline, dbm, uuid, tkinter) are not built.
# Configured out of both builds as well: __uint128_t (nanofil refuses
# __int128; libmpdec takes its portable path).
#
# The build runs the nanofil-built interpreter itself (deepfreeze.py
# freezes the bootstrap modules with _bootstrap_python), and its
# Python/deepfreeze/deepfreeze.c must equal the reference's. One build
# derivation per configuration (plain and -O) is shared by the checks:
# nanofil-python runs, on the same builder, both builds' deterministic
# workload (workloads/python.sh, nanofil's also under FUGC_SCRIBBLE and
# FUGC_VERIFY), which must match byte for byte, and -O's regrtest on the
# tests below; nanofil-python-regrtest-plain runs the plain build's,
# about as long as the rest. Both builds' per-test-case results (from
# --junit-xml, read by the reference interpreter) and per-file results
# must be equal: some tests fail or stop with a Fil-C error in filcc's
# build too. Everything runs with a 256 MB stack: nanofil's frames are
# larger than clang's (_PyEval_EvalFrameDefault's is 24,880 bytes plain
# and 9,872 with -O, against clang's 3,640), and Python's recursion
# tests overflow 8 MB first (Fil-C stops them safely); test_isinstance's
# test_infinitely_many_bases recurses about 2,400 levels of about 27 KB
# each in the plain build, past 64 MB.
{ pkgs, filcc }:
let
  src = pkgs.fetchurl {
    url = "https://www.python.org/ftp/python/3.12.5/Python-3.12.5.tar.xz";
    hash = "sha256-+oouEsXmILCfU+ZbzYdVDS5aHi4Ev4upkdzFUROHY5c=";
  };
  workload = ./workloads/python.sh;
  junit = ./workloads/python-junit.py;
  tests = pkgs.lib.concatStringsSep " " [
    "test_abc test_array test_augassign test_base64 test_baseexception"
    "test_binascii test_bisect test_bool test_class test_cmath test_codecs"
    "test_collections test_compare test_complex test_contains test_contextlib"
    "test_copy test_csv test_defaultdict test_deque test_dict test_dictviews"
    "test_enumerate test_exception_group test_float test_format test_fractions"
    "test_functools test_gc test_generators test_genexps test_grammar"
    "test_hash test_hashlib test_heapq test_index test_int test_int_literal"
    "test_isinstance test_iter test_keyword test_list test_listcomps"
    "test_memoryview test_opcodes test_operator test_ordered_dict test_patma"
    "test_pow test_pprint test_print test_property test_raise test_re"
    "test_reprlib test_richcmp test_scope test_sort test_string"
    "test_string_literals test_strtod test_struct test_structseq test_super"
    "test_syntax test_textwrap test_thread test_threading_local test_tuple"
    "test_types test_unicodedata test_unpack test_userdict test_userlist"
    "test_with test_yield_from"
  ];
  unpack = dir: ''
    cd $NIX_BUILD_TOP
    mkdir ${dir}
    tar -xf $src -C ${dir} --strip-components=1
    cd ${dir}
    for p in ${../../ports/patch/Python-3.12.5.patch} \
      ${../../patches/python-code-header-cxx.patch} \
      ${../../patches/python-faulthandler.patch}; do
      patch -p1 <$p
    done
    export ACLOCAL_PATH=${pkgs.autoconf-archive}/share/aclocal:${pkgs.pkg-config}/share/aclocal
    autoreconf -f >autoreconf.log 2>&1 || { cat autoreconf.log; exit 1; }
    CC=${filcc}/bin/clang ./configure --without-ensurepip --without-pymalloc \
      --without-freelists ac_cv_func_chflags=no ac_cv_func_lchflags=no \
      ac_cv_func_sigaltstack=no ac_cv_gcc_asm_for_x64=no ac_cv_gcc_asm_for_x87=no \
      ac_cv_gcc_asm_for_mc68881=no ac_cv_x87_double_rounding=no \
      ac_cv_func_lchmod=no ac_cv_type___uint128_t=no >configure.log 2>&1 \
      || { cat configure.log; exit 1; }
  '';
  # regrtest on the tests with a fixed seed; the per-case results, then
  # each test file's.
  regrtest = tree: out: ''
    (cd ${tree} && ./python -m test -j$NIX_BUILD_CORES --randseed 1 --timeout 1200 \
      --junit-xml $NIX_BUILD_TOP/${out}.xml ${tests}) >$NIX_BUILD_TOP/${out}.log 2>&1 || true
    $NIX_BUILD_TOP/ref/python ${junit} $NIX_BUILD_TOP/${out}.xml >$NIX_BUILD_TOP/${out}
    grep -oE '\] test_[a-z0-9_]+ [a-z]+' $NIX_BUILD_TOP/${out}.log | sed 's/^\] //' \
      | sort >>$NIX_BUILD_TOP/${out}
    test -s $NIX_BUILD_TOP/${out}
  '';
  reference =
    pkgs.runCommandCC "nanofil-python-reference"
      {
        inherit src;
        nativeBuildInputs = [
          pkgs.autoconf
          pkgs.automake
          pkgs.pkg-config
        ];
      }
      ''
        ${unpack "ref"}
        make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
        find . -name '*.o' -delete
        cd $NIX_BUILD_TOP
        mkdir $out
        tar -cf $out/ref.tar ref
      '';
  # build label opt: the tree nanofil builds with NANOFIL_OPT=opt, its
  # objects deleted once checked to all come from nanofil.
  build =
    label: opt:
    pkgs.runCommandCC "nanofil-python-build-${label}"
      {
        inherit src;
        nativeBuildInputs = [
          pkgs.autoconf
          pkgs.automake
          pkgs.pkg-config
        ];
      }
      ''
        cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
        ulimit -s 262144
        (cd $NIX_BUILD_TOP && tar -xf ${reference}/ref.tar)
        ${unpack "python"}
        echo "== python, nanofil ${opt}"
        export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
        make -j$NIX_BUILD_CORES CC="$cc$(sed -n 's/^CC=[[:space:]]*[^ ]*//p' Makefile)"
        cmp $NIX_BUILD_TOP/ref/Python/deepfreeze/deepfreeze.c Python/deepfreeze/deepfreeze.c
        echo "the nanofil-built bootstrap interpreter froze the same modules as filcc's"
        # Compare paths, not just counts: no object may come from clang.
        find . -name '*.o' -printf '%P\n' | sort >../objects
        sort -u nanofil.log >../compiled
        test -s ../objects
        diff -u ../objects ../compiled
        echo "nanofil compiled every one of $(wc -l <../objects) python objects"
        find . -name '*.o' -delete
        cd $NIX_BUILD_TOP
        mkdir $out
        tar -cf $out/python.tar python
      '';
  builds = builtins.mapAttrs build {
    plain = "";
    O = "-O";
  };
  # test name label body: a derivation that runs body beside both
  # builds' trees, ref and python, under $NIX_BUILD_TOP.
  test =
    name: label: body:
    pkgs.runCommandCC name { } ''
      ulimit -s 262144
      cd $NIX_BUILD_TOP
      tar -xf ${reference}/ref.tar
      tar -xf ${builds.${label}}/python.tar
      ${body}
      touch $out
    '';
  workloads = ''
    w=$NIX_BUILD_TOP/w
    rm -rf $w && mkdir $w
    (cd $w && bash ${workload} $NIX_BUILD_TOP/ref/python >../ref.out)
    for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
      rm -rf $w && mkdir $w
      (cd $w && env $env bash ${workload} $NIX_BUILD_TOP/python/python >../nf.out)
      diff -u $NIX_BUILD_TOP/ref.out $NIX_BUILD_TOP/nf.out
      echo "python matches filcc's on $(grep -c '^### exit' $NIX_BUILD_TOP/ref.out) scripts ($env)"
    done
  '';
  regrtests = ''
    ${regrtest "$NIX_BUILD_TOP/ref" "ref.results"}
    ${regrtest "$NIX_BUILD_TOP/python" "nf.results"}
    diff -u $NIX_BUILD_TOP/ref.results $NIX_BUILD_TOP/nf.results
    echo "regrtest: $(awk '{print $2}' $NIX_BUILD_TOP/nf.results | sort | uniq -c | tr -s ' \n' ' '), as filcc's"
  '';
in
{
  # The workload for both builds, and regrtest for -O's; the plain
  # build's regrtest, about as long as the rest, is its own check.
  nanofil-python =
    import ./configurations.nix { inherit pkgs; } "nanofil-python"
      {
        plain = "";
        O = "-O";
      }
      (
        label: _:
        test "nanofil-python-${label}" label (
          workloads + pkgs.lib.optionalString (label == "O") regrtests
        )
      );
  nanofil-python-regrtest-plain =
    test "nanofil-python-regrtest-plain" "plain"
      regrtests;
}
