{
  description = "An event-first Filnix campaign prototype using NXT and the Nix C++ API";

  inputs = {
    nixpkgs.url = "github:lessrest/filnixpkgs/e63c68034d742160a48ca80640442337e6356cf4";
    nixpkgs.flake = false;
    nxtui.url = "github:mbrock/nxtui/4d706802815db437749fe0c39a1c1a93941b7afa";
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
          nix.dev
          pkgs.nlohmann_json
        ];
        nativeCheckInputs = [
          pkgs.python3
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
          pkgs.python3
          nix
          pkgs.clang-tools
          pkgs.nixfmt
        ];
      };
      formatter.${system} = pkgs.nixfmt;
    };
}
