# libpizlo with the SerenityOS platform edits (libpas-serenity.patch) and its
# Linux syscall layer split out of filc_runtime.c (split_zsys.py). On Linux
# the result must behave exactly like the stock libpizlo; check.sh compares
# them. Pass `libpizlo` to apply the same changes on top of another build,
# such as libpizlo-spike.nix.
{
  flake ? builtins.getFlake (toString ../../..),
  libpizlo ? flake.packages.x86_64-linux.filcc.components.libpizlo,
}:
let
  pkgs = import flake.inputs.nixpkgs { system = "x86_64-linux"; };
in
libpizlo.overrideAttrs (old: {
  pname = "${old.pname}-split";
  patches = old.patches ++ [ ./libpas-serenity.patch ];
  nativeBuildInputs = old.nativeBuildInputs ++ [ pkgs.python3 ];
  postPatch = (old.postPatch or "") + ''
    python3 ${./split_zsys.py} libpas/src/libpas
  '';
})
