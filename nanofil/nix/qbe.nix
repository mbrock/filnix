# qbe at an upstream commit newer than nixpkgs' 1.2, with fixes for the
# miscompiles nanofil's interpreter found (tests/qbe-bugs/) and for
# constant shift counts that GNU as rejects. Each patch header describes
# its bug; they are meant to be sent upstream.
{ pkgs }:
pkgs.qbe.overrideAttrs (old: {
  version = "unstable-2026-05-13";
  src = pkgs.fetchzip {
    url = "https://git.sr.ht/~mcf/qbe/archive/c0818978acec60ebb6167fade60fb7012cbf20ca.tar.gz";
    hash = "sha256-IzHO5GT81G7xwoDVhkvQlDwdQGm1ijpJ+dl+IH1P/1s=";
  };
  patches = (old.patches or [ ]) ++ [
    ../../patches/qbe-load-store-width.patch
    ../../patches/qbe-amd64-shift-flags.patch
    ../../patches/qbe-amd64-jnz-long.patch
    ../../patches/qbe-gvn-jnz-long-const.patch
    ../../patches/qbe-amd64-shift-imm.patch
  ];
})
