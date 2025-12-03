{ pkgs, pkgsFilc, filcc, filc-emacs }:
let
  rubyNativeGems = (import ./rubyports.nix { inherit pkgs; }).nativeGems;

  # Flatten all native gem categories into a single list
  allNativeGemNames = pkgs.lib.flatten (builtins.attrValues rubyNativeGems);
in
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

  # Ruby with all native extension gems (excluding GTK3)
  # See rubyports.nix for the categorized list
  ruby-maxxed =
    let
      ruby = pkgsFilc.ruby_3_3;
      gems = ruby.gems;
      # Filter to gems that actually exist in nixpkgs
      availableGems = builtins.filter (name: gems ? ${name}) allNativeGemNames;
    in
    pkgsFilc.buildEnv {
      name = "ruby-maxxed";
      paths = [ ruby ] ++ map (name: gems.${name}) availableGems;
    };
}
