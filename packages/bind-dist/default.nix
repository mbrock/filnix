# A relocatable BIND 9 distribution for ordinary x86-64 Linux systems, built
# like php-dist: the tarball carries the Fil-C runtime, glibc and every
# library the programs need, so nothing is loaded from /nix or the host, and
# each bin/ entry is a small static launcher that starts libexec/ through
# lib/ld-fil1-*.so.
{
  pkgs,
  pkgsFilc,
  bind ? pkgsFilc.bind,
  # Marks an alternate build in the tarball and image names.
  suffix ? "",
}:

let
  name = "bind-${bind.version}${suffix}-filc-x86_64-linux";

  launcher = pkgs.pkgsStatic.runCommandCC "bind-dist-launcher" { } ''
    $CC -O2 -static -Wall -Werror -o $out ${./launcher.c}
  '';
in
pkgs.runCommand "${name}.tar.xz"
  {
    nativeBuildInputs = [
      pkgs.patchelf
      pkgs.python3
      pkgs.xz
    ];
    passthru = { inherit bind launcher suffix; };
  }
  ''
    root=$PWD/${name}
    interp=$(patchelf --print-interpreter ${bind.out}/bin/named)

    items=()
    progs=()
    for f in ${bind.out}/bin/* ${bind.dnsutils}/bin/* ${bind.host}/bin/*; do
      items+=(libexec/$(basename $f)=$(readlink -f $f))
      progs+=($(basename $f))
    done
    # named's plugins; configure them by absolute path (see README.md).
    for f in ${bind.lib}/lib/bind/*.so; do
      items+=(lib/bind/$(basename $f)=$f)
    done
    python3 ${../php-dist/bundle.py} $root $interp "''${items[@]}"

    mkdir -p $root/bin $root/etc/ssl
    for prog in "''${progs[@]}"; do
      install -m755 ${launcher} $root/bin/$prog
    done
    install -m644 ${pkgsFilc.openssl.out}/etc/ssl/openssl.cnf $root/etc/ssl/
    install -m644 ${./README.md} $root/README.md

    chmod -R u+w,go-w $root
    tar --sort=name --mtime=@1 --owner=0 --group=0 --numeric-owner \
      -cf - ${name} | xz -T$NIX_BUILD_CORES -6 > $out
  ''
