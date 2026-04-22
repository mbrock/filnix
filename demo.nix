{
  pkgs,
  pkgsFilc,
  filcc,
  filc-emacs,
  libei,
}:
let
  libei-ping-cnode = pkgsFilc.callPackage ./demo/libei/cnode.nix { inherit libei; };
in
{
  lighttpd-demo =
    (pkgs.callPackage ./httpd {
      inherit filcc;
      ports = pkgsFilc;
    }).overrideAttrs
      (_: {
        meta.mainProgram = "lighttpd-demo";
      });

  ttyd-emacs-demo =
    (pkgs.callPackage ./ttyd-demo {
      ports = pkgsFilc;
      inherit filc-emacs;
    }).overrideAttrs
      (_: {
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
    }).overrideAttrs
      (_: {
        meta.mainProgram = "python-web-demo";
      });

  perl-demos = pkgsFilc.callPackage ./demo/perl { };

  libei-ping-demo = pkgs.callPackage ./demo/libei {
    cnode = libei-ping-cnode;
    erlang = pkgs.erlang;
    runnerName = "libei-ping-demo";
    alive = "filc_libei_ping";
    description = "End-to-end ping demo proving Fil-C libei can talk to an Erlang node";
  };

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

  # Sinatra + Puma web demo
  # NOTE: Currently crashes due to rb_define_finalizer_no_check null pointer in gc.c
  # The finalizer code needs porting to Fil-C (null object pointer at 0x8)
  sinatra-demo =
    let
      ruby = pkgsFilc.ruby_3_3;
      gems = ruby.gems;
      rubyEnv = pkgsFilc.buildEnv {
        name = "sinatra-env";
        paths = [
          ruby
          gems.sinatra
          gems.puma
          gems.rack
        ];
      };
    in
    pkgs.writeShellScriptBin "sinatra-demo" ''
            export GEM_PATH="${rubyEnv}/lib/ruby/gems/3.3.0"
            export GEM_HOME="${rubyEnv}/lib/ruby/gems/3.3.0"
            cd "$(mktemp -d)"

            cat > app.rb << 'EOF'
      require 'sinatra/base'

      class App < Sinatra::Base
        get '/' do
          'Hello from Sinatra on Fil-C!'
        end

        get '/time' do
          "The time is: #{Time.now}"
        end

        get '/hello/:name' do
          "Hello, #{params[:name]}!"
        end
      end
      EOF

            cat > config.ru << 'EOF'
      require './app'
      run App
      EOF

            echo "Starting Sinatra on http://127.0.0.1:9292"
            exec ${rubyEnv}/bin/puma -b tcp://127.0.0.1:9292 config.ru
    '';
}
