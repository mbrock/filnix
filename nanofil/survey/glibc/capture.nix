# User glibc's translation units, as filcc compiled them, for the
# by-hand experiment of compiling them with nanofil (docs/zsys.md).
#
#   nix build -f nanofil/survey/glibc/capture.nix -o /tmp/glibc-pp
#
# This is the staging toolchain's own filc-glibc, rebuilt with one
# change: CC is a wrapper that, before each C compile (`-c` of a .c
# file, or of C on stdin as the syscalls.list stubs are), runs the same
# command with -E and keeps the result as OBJ.i beside OBJ.cmd, the
# command. OBJ is the object's path under the build directory, such as
# string/strlen.os. The compile itself is unchanged, so the glibc built
# is the toolchain's. The output holds only the captures.
{
  repo ? ../../..,
}:
let
  flake = builtins.getFlake (toString repo);
  system = "x86_64-linux";
  pkgs = import flake.inputs.nixpkgs { inherit system; };
  glibc = flake.packages.${system}.filcc-staging.components.filc-glibc;
  wrap = pkgs.writeShellScript "glibc-pp-cc" ''
    set -eu
    out= compile= stdin= src= lang=
    args=("$@")
    i=0
    while [ $i -lt ''${#args[@]} ]; do
      a=''${args[$i]}
      case $a in
        -c) compile=1 ;;
        -o) i=$((i + 1)); out=''${args[$i]} ;;
        -x) i=$((i + 1)); lang=''${args[$i]} ;;
        -) stdin=1 ;;
        *.c) src=$a ;;
      esac
      i=$((i + 1))
    done
    if [ -n "$stdin" ] && [ "$lang" != c ]; then stdin=; fi
    if [ -z "$compile" ] || [ -z "$out" ] || { [ -z "$src" ] && [ -z "$stdin" ]; }; then
      exec "$@"
    fi
    rel=''${out#"$NIX_BUILD_TOP"/build/}
    dest=$NIX_BUILD_TOP/pp/$rel
    mkdir -p "$(dirname "$dest")"
    # Everything but -o FILE and the dependency-file flags, then -E.
    # nanofil refuses __int128 and has no _BitInt, so, as nanofil-cc
    # does, neither is advertised to the preprocessor.
    pp=() i=0
    while [ $i -lt ''${#args[@]} ]; do
      a=''${args[$i]}
      case $a in
        -o | -MF | -MT | -MQ) i=$((i + 1)) ;;
        -MD | -MMD | -MP) ;;
        -c) ;;
        *) pp+=("$a") ;;
      esac
      i=$((i + 1))
    done
    printf '%q ' "$@" >"$dest.cmd"
    echo >>"$dest.cmd"
    if [ -n "$stdin" ]; then
      tmp=$(mktemp)
      cat >"$tmp"
      cp "$tmp" "$dest.stdin.c"
      "''${pp[@]}" -U__SIZEOF_INT128__ -U__BITINT_MAXWIDTH__ -E -o "$dest.i" <"$tmp" || echo "preprocess failed" >"$dest.pperr"
      "$@" <"$tmp"
      status=$?
      rm -f "$tmp"
      exit $status
    fi
    "''${pp[@]}" -U__SIZEOF_INT128__ -U__BITINT_MAXWIDTH__ -E -o "$dest.i" || echo "preprocess failed" >"$dest.pperr"
    exec "$@"
  '';
in
glibc.overrideAttrs (old: {
  pname = "filc-glibc-pp";
  preConfigure = old.preConfigure + ''
    export CC="${wrap} $CC"
  '';
  postInstall = ''
    rm -rf $out
    mkdir -p $out
    cp -r $NIX_BUILD_TOP/pp/. $out/
  '';
})
