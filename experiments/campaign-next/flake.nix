{
  description = "An event-first Filnix campaign prototype using NXT and the Nix C++ API";

  inputs = {
    nixpkgs.url = "github:lessrest/filnixpkgs/e63c68034d742160a48ca80640442337e6356cf4";
    nixpkgs.flake = false;
    nxtui.url = "github:mbrock/nxtui/50e7caffc371960e8473f12b138dcbc925fbdcd2";
    nxtui.flake = false;
  };

  outputs =
    {
      self,
      nixpkgs,
      nxtui,
    }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      nix = pkgs.nixVersions.nix_2_34;
      nxt =
        (pkgs.callPackage "${nxtui}/nix/package.nix" { doCheck = false; })
        .overrideAttrs
          (old: {
            mesonFlags = old.mesonFlags ++ [
              "-Ddefault_wand=epoll"
              "-Ddemo=false"
              "-Dllm_tool=false"
              "-Dwisp_tool=false"
            ];
          });
      campaign = pkgs.stdenv.mkDerivation {
        pname = "filnix-campaign-next";
        version = "0.1.0";
        src = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset = pkgs.lib.fileset.unions [
            ./meson.build
            ./src
            ./tests
            ./static
          ];
        };
        nativeBuildInputs = [
          pkgs.meson
          pkgs.ninja
          pkgs.pkg-config
        ];
        buildInputs = [
          nxt
          pkgs.boost
          pkgs.brotli.dev
          pkgs.zstd.dev
          pkgs.zlib.dev
          nix.dev
          pkgs.nlohmann_json
          pkgs.duckdb.dev
        ];
        nativeCheckInputs = [
          (pkgs.python3.withPackages (ps: [ ps.duckdb ]))
          nix
          pkgs.bash
          pkgs.coreutils
        ];
        doCheck = true;
        meta.mainProgram = "filnix-campaign";
      };
    in
    {
      packages.${system} = {
        default = campaign;
        inherit campaign nxt;
      };
      checks.${system}.campaign = campaign;
      devShells.${system}.default = pkgs.mkShell {
        inputsFrom = [ campaign ];
        packages = [
          (pkgs.python3.withPackages (ps: [ ps.duckdb ]))
          nix
          pkgs.clang-tools
          pkgs.nixfmt
        ];
      };
      formatter.${system} = pkgs.nixfmt;
    };
}
