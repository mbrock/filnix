# User glibc with some of its units compiled by nanofil, and programs
# run against it and against the stock one (docs/zsys.md, *Running
# nanofil's glibc*). By hand, not CI: the glibc build takes a while.
#
#   nix build -f nanofil/survey/glibc/mixed.nix check -o /tmp/glibc-mixed-check
#   nix build -f nanofil/survey/glibc/mixed.nix glibc -o /tmp/glibc-mixed
#
# glibc is the staging toolchain's own filc-glibc, rebuilt with one
# change: CC is a wrapper that, for each unit named in units (paths
# under the build directory, such as string/strlen.os), compiles the
# preprocessed unit with nanofil (opt, -O by default) and assembles it
# with GNU as over filcc's object; every other compile is filcc's.
# glibc's own make then links libc.so from them. Each unit nanofil
# compiles is listed in $out/nanofil/compiled, any it fails on (which
# keep filcc's object) in $out/nanofil/failed.
#
# check builds GNU hello and the programs in run/ with filcc, against
# the stock glibc, and runs each twice: as built, and with
# LD_LIBRARY_PATH naming this glibc's lib, which the loader searches
# before the RUNPATH. It fails unless the second run loads this glibc's
# libc.so; $out/verdict says whether stdout, stderr and the exit status
# of every invocation agree, and $out/diff shows where they do not.
{
  repo ? ../../..,
  units ? ./run/units.txt,
  opt ? "-O",
}:
let
  flake = builtins.getFlake (toString repo);
  system = "x86_64-linux";
  pkgs = import flake.inputs.nixpkgs { inherit system; };
  filcc = flake.packages.${system}.filcc-staging;
  stock = filcc.components.filc-glibc;
  nanofil =
    pkgs.runCommand "nanofil-src" { nativeBuildInputs = [ pkgs.swi-prolog ]; }
      ''
        mkdir $out
        cp -r ${../../bin} $out/bin
        cp -r ${../../src} $out/src
        chmod -R u+w $out
        patchShebangs $out/bin
        $out/bin/nanofil --save-state $out/nanofil.state
      '';
  wrap = pkgs.writeShellScript "glibc-mixed-cc" ''
    set -u
    out= compile= src=
    args=("$@")
    i=0
    while [ $i -lt ''${#args[@]} ]; do
      case ''${args[$i]} in
        -c) compile=1 ;;
        -o) i=$((i + 1)); out=''${args[$i]} ;;
        *.c) src=''${args[$i]} ;;
      esac
      i=$((i + 1))
    done
    # glibc's CC is several words: the compiler and its flags.
    if [ -z "$compile" ] || [ -z "$out" ] || [ -z "$src" ]; then exec $GLIBC_MIXED_CC "$@"; fi
    rel=''${out#"$NIX_BUILD_TOP"/build/}
    if ! grep -qxF "$rel" ${units}; then exec $GLIBC_MIXED_CC "$@"; fi
    # filcc's object first, which also writes make's dependency file.
    $GLIBC_MIXED_CC "$@" || exit
    pp=() i=0 std= errno= common= copies= inline=
    while [ $i -lt ''${#args[@]} ]; do
      a=''${args[$i]}
      case $a in
        -o | -MF | -MT | -MQ) i=$((i + 1)); a= ;;
        -MD | -MMD | -MP | -c) a= ;;
        -std=gnu89 | -std=c89 | -std=c90 | -fgnu89-inline) std=gnu89 ;;
        -std=c23 | -std=gnu23 | -std=c2x | -std=gnu2x) std=c23 ;;
        -fno-math-errno) errno=0 ;;
        -fmath-errno) errno= ;;
        -fcommon) common=1 ;;
        -fno-common) common= ;;
        -fno-builtin | -ffreestanding) copies=--memcpy=call ;;
        -fno-inline | -O0) inline=--inline=none ;;
      esac
      [ -n "$a" ] && pp+=("$a")
      i=$((i + 1))
    done
    log=$NIX_BUILD_TOP/nanofil
    mkdir -p "$log"
    # nanofil refuses __int128 and has no _BitInt (c_pp.pl).
    if $GLIBC_MIXED_CC "''${pp[@]}" -U__SIZEOF_INT128__ -U__BITINT_MAXWIDTH__ -E -o "$out.nf.i" &&
       (cd ${nanofil}/src &&
        NANOFIL_STATE=${nanofil}/nanofil.state NANOFIL_STD=$std NANOFIL_MATH_ERRNO=$errno \
          NANOFIL_COMMON=$common ../bin/nanofil ${opt} $copies $inline cc "$out.nf.i" </dev/null) \
          >"$out.nf.s" 2>"$out.nf.err" &&
       ${pkgs.binutils-unwrapped}/bin/as -o "$out.nf.o" "$out.nf.s" 2>>"$out.nf.err"; then
      mv "$out.nf.o" "$out"
      echo "$rel" >>"$log/compiled"
    else
      echo "$rel: $(head -c 300 "$out.nf.err")" >>"$log/failed"
    fi
    rm -f "$out.nf.i" "$out.nf.s"
    exit 0
  '';
  glibc = stock.overrideAttrs (old: {
    pname = "filc-glibc-nanofil";
    nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ pkgs.swi-prolog ];
    preConfigure = old.preConfigure + ''
      export GLIBC_MIXED_CC="$CC"
      export CC=${wrap}
    '';
    postInstall = (old.postInstall or "") + ''
      mkdir -p $out/nanofil
      touch $NIX_BUILD_TOP/nanofil/compiled $NIX_BUILD_TOP/nanofil/failed
      sort $NIX_BUILD_TOP/nanofil/compiled >$out/nanofil/compiled
      sort $NIX_BUILD_TOP/nanofil/failed >$out/nanofil/failed
      cp ${units} $out/nanofil/units.txt
    '';
  });
  hellos = [
    ""
    "-g x"
    "-t"
    "--version"
    "--help"
    "--bogus"
    "extra"
    "-g"
    "-g Grüße,_мир_→_世界"
    "--greeting=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    "-t -g ignored"
    "--traditional"
  ];
  check = pkgs.runCommandCC "glibc-nanofil-check" { src = pkgs.hello.src; } ''
    cc=${filcc}/bin/clang
    mkdir hello progs $out
    tar -xf $src -C hello --strip-components=1
    (cd hello && CC=$cc ./configure --disable-nls >configure.log 2>&1 && make -j$NIX_BUILD_CORES >make.log 2>&1) ||
      { cat hello/configure.log hello/make.log | tail -40; exit 1; }
    cp hello/hello progs/hello
    for p in ${./run}/*.c; do
      $cc -O1 -fno-builtin -w -o progs/$(basename $p .c) $p
    done
    # Each invocation: the program and its arguments, one per line.
    {
      ${pkgs.lib.concatMapStrings (
        a: "printf '%s\\n' ${pkgs.lib.escapeShellArg "hello ${a}"}\n"
      ) hellos}
      for p in strings stdio floats malloc; do echo $p; done
      for a in "" 3 a q; do echo "exit $a"; done
    } >invocations
    run() {
      local lib=$1 line=$2 status
      mkdir -p work && cd work
      read -r -a words <<<"$line"
      if [ -n "$lib" ]; then
        LD_LIBRARY_PATH=$lib LC_ALL=C.UTF-8 ../progs/''${words[0]} "''${words[@]:1}" >stdout 2>stderr && status=0 || status=$?
      else
        LC_ALL=C.UTF-8 ../progs/''${words[0]} "''${words[@]:1}" >stdout 2>stderr && status=0 || status=$?
      fi
      # Fil-C's panic messages name the process id.
      sed -i 's/^\[[0-9]*\] /[pid] /' stderr
      echo "### $line"; cat stdout; echo "### stderr"; cat stderr; echo "### exit $status"
      cd .. && rm -rf work
    }
    while IFS= read -r line; do run "" "$line"; done <invocations >$out/stock.out
    while IFS= read -r line; do run ${glibc}/lib "$line"; done <invocations >$out/nanofil.out
    # The swap took: the loader maps this glibc's libc.so.
    LD_LIBRARY_PATH=${glibc}/lib LD_DEBUG=libs progs/strings 2>&1 >/dev/null | grep 'libc.so' | tee $out/loaded
    grep -q '${glibc}/lib/libc.so' $out/loaded
    cp ${glibc}/nanofil/compiled ${glibc}/nanofil/failed $out/
    echo "nanofil compiled $(wc -l <$out/compiled) units, failed on $(wc -l <$out/failed)"
    if diff -u $out/stock.out $out/nanofil.out >$out/diff; then
      echo "agree: all $(wc -l <invocations) invocations" | tee $out/verdict
    else
      echo "differ: see diff" | tee $out/verdict; head -80 $out/diff
    fi
  '';
in
{
  inherit glibc check;
}
