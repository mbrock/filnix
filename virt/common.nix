{
  pkgs,
  ports,
  filcc,
}:

{
  ghostty-terminfo = pkgs.runCommand "ghostty-terminfo" { } ''
    mkdir -p $out/share/terminfo
    ${pkgs.ncurses}/bin/tic -x -o $out/share/terminfo ${../misc/ghostty.terminfo}
  '';

  dank-bashrc = pkgs.writeText "dank-bashrc" ''
    echo
    tput bold
    figlet -f fender "Fil-C" | sed 's/^/   /' | clolcat -f | head -n-1
    tput sgr0; tput dim
    echo -n '    '; clang 2>&1 -v | grep Fil-C
    tput sgr0
    echo; echo '  You feel an uncanny sense of safety...'
    tput sgr0
    echo

    export CC=filc
    export CXX=filc++
    export PKG_CONFIG=pkgconf
  '';

  lighttpd-demo = pkgs.callPackage ../httpd { inherit ports filcc; };
}
