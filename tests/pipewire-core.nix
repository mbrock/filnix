# Core profile with the ordinary toolchain; cancellation remains a libc blocker.
let
  f = builtins.getFlake (toString ../.);
in
import ../packages/pipewire-core.nix {
  p = f.legacyPackages.x86_64-linux.pkgsFilc;
  native = import f.inputs.nixpkgs { system = "x86_64-linux"; };
}
