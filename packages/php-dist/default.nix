# A relocatable PHP distribution for ordinary x86-64 Linux systems.
#
# The tarball carries the Fil-C runtime, glibc, libc++ and every library the
# programs and extensions need, so nothing is loaded from /nix or the host.
# A Fil-C program's interpreter must be an absolute path, so each bin/ entry
# is a small static launcher that starts libexec/ through lib/ld-fil1-*.so.
#
# php is PHP with the extensions to load; the default is PHP 8.4 (base) with
# the extensions below. suffix marks an alternate build in the tarball and
# image names, as in php-8.5.12-staging-filc-x86_64-linux.
{
  pkgs,
  pkgsFilc,
  base ? pkgsFilc.php,
  suffix ? "",
  php ? base.withExtensions (
    { enabled, all }:
    enabled
    # Commonly enabled extensions ported to Fil-C (docs/php-extensions.md).
    # Debuggers and profilers (xdebug, pcov, spx) slow every request when
    # loaded and are left out.
    ++ (with all; [
      apcu
      ast
      bz2
      decimal
      ds
      event
    ])
    # igbinary 3.2.14 does not build on PHP 8.5 (docs/php.md).
    ++ pkgs.lib.optional (pkgs.lib.versionOlder base.version "8.5") all.igbinary
    ++ (with all; [
      imagick
      mailparse
      maxminddb
      memcached
      mongodb
      msgpack
      protobuf
      redis
      shmop
      sysvmsg
      sysvshm
      tidy
      uuid
      xsl
      yaml
      zstd
    ])
  ),
}:

let
  name = "php-${php.version}${suffix}-filc-x86_64-linux";

  launcher = pkgs.pkgsStatic.runCommandCC "php-dist-launcher" { } ''
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
    passthru = { inherit php launcher suffix; };
  }
  ''
    root=$PWD/${name}
    unwrapped=${php.unwrapped}
    interp=$(patchelf --print-interpreter $unwrapped/bin/php)
    gconv=$(dirname $interp)/gconv

    items=()
    for prog in php php-cgi php-fpm phpdbg; do
      items+=(libexec/$prog=$unwrapped/bin/$prog)
    done
    # The wrapper's ini lists the extensions in load order.
    for ext in $(grep -o '/nix/store/[^ ]*\.so' ${php}/lib/php.ini); do
      items+=(lib/php/extensions/$(basename $ext)=$ext)
    done
    for module in $gconv/*.so; do
      items+=(lib/gconv/$(basename $module)=$module)
    done
    python3 ${./bundle.py} $root $interp "''${items[@]}"
    cp -r $gconv/gconv-modules $gconv/gconv-modules.d $root/lib/gconv/
    mkdir $root/lib/locale
    cp -r $(dirname $interp)/locale/C.utf8 $root/lib/locale/

    # The launcher points glibc at lib/gconv and lib/locale. Under their
    # usual names the variables would also reach host programs that PHP
    # runs, whose glibc would then load these Fil-C modules, or ignore its
    # locale archive.
    python3 - $root/lib/libc.so.6666 <<'EOF'
    import sys
    path = sys.argv[1]
    data = open(path, "rb").read()
    for old, new, count in [
        (b"GCONV_PATH\0", b"FILC_GCONV\0", 1),
        (b"LOCPATH\0", b"FILCLOC\0", 2),  # setlocale and newlocale
    ]:
        assert data.count(old) == count, old
        data = data.replace(old, new)
    open(path, "wb").write(data)
    EOF

    mkdir -p $root/bin $root/etc/php.d $root/etc/php-fpm.d $root/etc/ssl \
      $root/var/log $root/var/run
    for prog in php php-cgi php-fpm phpdbg; do
      install -m755 ${launcher} $root/bin/$prog
    done

    install -m644 $unwrapped/etc/php.ini $root/etc/php.ini
    cat >> $root/etc/php.ini <<'EOF'

    ; Settings whose compiled-in defaults point into /nix.
    [PHP]
    include_path = "."
    sendmail_path = "/usr/sbin/sendmail -t -i"
    EOF
    {
      echo 'extension_dir = "''${PHP_DIST_DIR}/lib/php/extensions"'
      grep -o '^[a-z_]*extension=/nix/store/[^ ]*\.so' ${php}/lib/php.ini |
        sed -E 's|=.*/([^/]*)\.so$|=\1|'
    } > $root/etc/php.d/extensions.ini

    cat > $root/etc/php-fpm.conf <<'EOF'
    ; Relative paths are relative to the distribution directory, or to the
    ; directory given with --prefix.
    [global]
    pid = var/run/php-fpm.pid
    error_log = var/log/php-fpm.log
    include = etc/php-fpm.d/*.conf
    EOF
    sed -e 's/^group = nobody/;group = nobody/' \
      $unwrapped/etc/php-fpm.d/www.conf.default > $root/etc/php-fpm.d/www.conf

    install -m644 ${pkgsFilc.cacert}/etc/ssl/certs/ca-bundle.crt $root/etc/ssl/cert.pem
    # Without a configuration file, openssl_pkey_new() and friends fail.
    install -m644 ${pkgsFilc.openssl.out}/etc/ssl/openssl.cnf $root/etc/ssl/
    ${
      if pkgs.lib.versions.majorMinor php.version == "8.4" then
        "install -m644 ${./README.md} $root/README.md"
      else
        "sed 's/^PHP 8\\.4 compiled/PHP ${pkgs.lib.versions.majorMinor php.version} compiled/' ${./README.md} > $root/README.md"
    }

    chmod -R u+w,go-w $root
    tar --sort=name --mtime=@1 --owner=0 --group=0 --numeric-owner \
      -cf - ${name} | xz -T$NIX_BUILD_CORES -6 > $out
  ''
