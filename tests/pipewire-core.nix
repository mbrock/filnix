# Core profile with the shared cancellation-capable Fil-C toolchain.
let
  f = builtins.getFlake (toString ../.);
in
import ../packages/pipewire-core.nix {
  p = f.legacyPackages.x86_64-linux.pkgsFilc;
  native = import f.inputs.nixpkgs { system = "x86_64-linux"; };
}
