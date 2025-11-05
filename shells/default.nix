{
  base,
  toolchain,
  compiler,
  runtime,
  portset,
  wasm3-cve-payloads,
  ghostty-terminfo,
  dank-bashrc,
}:

let
  dev = import ./dev.nix {
    inherit
      base
      toolchain
      compiler
      runtime
      ;
  };
  world = import ./world.nix {
    inherit
      base
      toolchain
      portset
      ghostty-terminfo
      dank-bashrc
      ;
  };
  wasm3 = import ./wasm3-cve-test.nix {
    inherit base portset wasm3-cve-payloads;
  };

in
dev // world // wasm3
