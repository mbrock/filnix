{ pkgs, pkgsFilc, filcc, filc-emacs }:
{
  lighttpd-demo =
    (pkgs.callPackage ./httpd {
      inherit filcc;
      ports = pkgsFilc;
    }).overrideAttrs (_: {
      meta.mainProgram = "lighttpd-demo";
    });

  ttyd-emacs-demo =
    (pkgs.callPackage ./ttyd-demo {
      ports = pkgsFilc;
      inherit filc-emacs;
    }).overrideAttrs (_: {
      meta.mainProgram = "ttyd-emacs-demo";
    });

  lua-with-stuff = pkgsFilc.lua5.withPackages (
    ps: with ps; [
      lpeg
      luafilesystem
      luabitop
      luadbi
      luadbi-sqlite3
      luaffi
      lua-ffi-zlib
      luaposix
      lua-pam
    ]
  );

  python-with-stuff = pkgsFilc.python3.withPackages (
    ps: with ps; [
      (lxml.overrideAttrs (_: {
        env.CFLAGS = "-O0";
      }))
      uvicorn
      starlette
      msgspec
      tagflow
      pycairo
      rich
      python-multipart
    ]
  );

  python-web-demo =
    (pkgsFilc.callPackage ./demo {
      demo-src = ./demo;
    }).overrideAttrs (_: {
      meta.mainProgram = "python-web-demo";
    });

  perl-demos = pkgsFilc.callPackage ./demo/perl { };

  perl-with-stuff = pkgsFilc.perl.withPackages (
    ps: with ps; [
      InlineC
      # JSONXS
      # YAMLLibYAML
      # DBI
      # DBDSQLite
      #            ack
    ]
  );
}
