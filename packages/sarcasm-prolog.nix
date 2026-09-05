{
  pkgs,
  filcc,
  trealla,
}:
pkgs.writeShellApplication {
  name = "sarcasm-prolog";
  runtimeInputs = [ pkgs.coreutils ];
  text = ''
    for arg in "$@"; do
      case "$arg" in
        --emit-c|--emit-ir|--emit-effects|--explain|--emit-checks|--help|-h)
          exec ${trealla}/bin/tpl -q -f ${../experiments/sarcasm-prolog}/main.pl -- "$@"
          ;;
      esac
    done
    work=$(mktemp -d)
    trap 'rm -rf "$work"' EXIT
    ${trealla}/bin/tpl -q -f ${../experiments/sarcasm-prolog}/main.pl -- "$@" > "$work/output.c"
    ${filcc}/bin/clang -O2 -fno-addrsig -S -x c "$work/output.c" -o -
  '';
  meta = {
    description = "Experimental Prolog assembly frontend with Fil-C lowering";
    mainProgram = "sarcasm-prolog";
    platforms = [ "x86_64-linux" ];
  };
}
