let
  f = builtins.getFlake (toString ../.);
  native = import f.inputs.nixpkgs { system = "x86_64-linux"; };
  p = f.legacyPackages.x86_64-linux.pkgsFilc;
  private = import ../toolchain/cancellation.nix {
    pkgs = native;
    baseStdenv = p.stdenv;
  };
  pipewire = p.sdl3.filcRuntime.pipewire;
  client =
    major: dependency:
    private.stdenv.mkDerivation {
      name = "pipewire-sdl${toString major}-client";
      dontUnpack = true;
      nativeBuildInputs = [ native.pkg-config ];
      buildInputs = [ dependency ];
      buildPhase = ''
        $CC ${native.lib.optionalString (major == 3) "-DSDL_THREE"} \
          -O2 -Werror ${./pipewire-sdl.c} \
          $(pkg-config --cflags --libs sdl${toString major}) -o client
      '';
      installPhase = ''install -Dm755 client "$out/bin/client"'';
    };
  sdl3Client = client 3 p.sdl3;
  sdl2Client = client 2 p.sdl2-compat;
in
{
  inherit pipewire sdl3Client sdl2Client;
  inherit (p)
    sdl3
    sdl2-compat
    cava
    wireplumber
    ;
  cavaRuntime = native.runCommand "cava-runtime-check" { } ''
    ${native.python3}/bin/python ${./cava-runtime.py} \
      ${p.cava}/bin/cava ${private.libc} > "$out"
  '';
  runtime = native.runCommand "pipewire-consumers-runtime-check" { } ''
    ${native.python3}/bin/python ${./pipewire-runtime.py} \
      --pipewire ${pipewire} --libc ${private.libc} \
      --client ${sdl3Client}/bin/client --client ${sdl2Client}/bin/client \
      --wpctl ${p.wireplumber}/bin/wpctl > "$out"
  '';
}
