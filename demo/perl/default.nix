# Perl + C Integration Demos with Fil-C Memory Safety
# Shows various Perl XS modules using C libraries, all compiled with Fil-C

{
  lib,
  pkgs,
  perl540Packages,
}:

let
  # Perl with required XS modules
  perlEnv = with perl540Packages; [
    perl

    # C integration
    InlineC

    # Fast C-based data processing
    JSONXS
    YAMLLibYAML # YAML::LibYAML - fast C-based YAML parser

    # Database with C backend
    DBI
    DBDSQLite

    # XML parsing (libxml2)
    XMLLibXML

    # Compression (zlib, bzip2)
    CompressZlib
    CompressBzip2

    # Other useful XS modules
    ListMoreUtils
    ScalarListUtils
  ];

  # Create wrapper scripts
  makeDemo =
    name: script:
    pkgs.writeShellScriptBin name ''
      ${perlEnv}/bin/perl ${script}
    '';

  runAll = pkgs.writeShellScriptBin "perl-demos" ''
    cd ${./.}
    exec bash ${./run-all.sh}
  '';

in
pkgs.buildEnv {
  name = "filc-perl-demos";

  paths = [
    perlEnv
    (makeDemo "perl-demo" ./demo.pl)
    (makeDemo "perl-inline-c" ./inline-c.pl)
    runAll
  ];

  meta = {
    mainProgram = "perl-demos";
    description = "Perl + C integration demos with Fil-C memory safety";
    longDescription = ''
      Two concise demos showing Perl XS (C extension) modules with Fil-C:

      1. demo.pl: Multiple C libraries (JSON::XS, XML::LibXML, DBD::SQLite, zlib)
      2. inline-c.pl: Write memory-safe C code directly in Perl

      All C code gets complete memory safety from Fil-C automatically.
    '';
  };
}
