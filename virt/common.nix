{ base, ports }:

{
  ghostty-terminfo = base.runCommand "ghostty-terminfo" { } ''
    mkdir -p $out/share/terminfo
    ${base.ncurses}/bin/tic -x -o $out/share/terminfo ${../ghostty.terminfo}
  '';

  dank-bashrc = base.writeText "dank-bashrc" ''
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

  lighttpd-demo = base.callPackage ../httpd { inherit ports; };
}

