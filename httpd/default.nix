{ pkgs, portset }:

let
  builders = import ./lib/builders.nix {
    inherit pkgs;
    ports = portset;
  };

  html-escape = builders.filcProgram "html-escape" {
    deps = with portset; [ ];
    lang = "c";
    src = ./src/html-escape.c;
  };

  parse-query = builders.filcProgram "parse-query" {
    deps = with portset; [ ];
    src = ./src/parse-query.cxx;
  };

  hello-cgi = builders.bashScript "hello.cgi" {
    deps = with portset; [ coreutils ];
    src = ./src/hello.sh;
  };

  demo-cgi = builders.filcProgram "demo.cgi" {
    deps = with portset; [ ];
    lang = "c";
    src = ./src/demo.c;
  };

  figlet-cgi = builders.bashScript "figlet.cgi" {
    deps =
      (with portset; [
        coreutils
        figlet
        gnused
        gawk
      ])
      ++ [
        html-escape
        parse-query
      ];
    bashOptions = [
      "errexit"
      "nounset"
    ];
    src = ./src/figlet.sh;
  };

  style-css = ./src/style.css;

  cgi-docroot = builders.www-root {
    scripts = {
      "hello.cgi" = hello-cgi;
      "demo.cgi" = demo-cgi;
      "figlet.cgi" = figlet-cgi;
    };
    static = {
      "style.css" = style-css;
    };
  };

  lighttpd-conf-template = import ./config/lighttpd.nix {
    inherit pkgs cgi-docroot;
  };

  lighttpd-demo = import ./demo-runner.nix {
    inherit
      pkgs
      builders
      lighttpd-conf-template
      cgi-docroot
      ;
    ports = portset;
  };

in
lighttpd-demo
