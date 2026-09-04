{ pkgs }:

let
  inherit (pkgs) fetchgit;
  upstream = builtins.fromJSON (builtins.readFile ./filc-upstream.json);
  hashData = builtins.fromJSON (builtins.readFile ./filc-hashes.json);
  coreRev = upstream.coreRev;
  sourcePatterns = upstream.sourcePatterns;
  filcHashes =
    assert hashData.coreRev == coreRev;
    hashData.hashes;

  # Stable names and exact sparse patterns make unchanged component content
  # reusable across core revisions. Cone mode also includes ancestor files.
  mkFilcSrc =
    name:
    fetchgit {
      url = "https://github.com/pizlonator/fil-c";
      inherit name;
      rev = coreRev;
      nonConeMode = true;
      sparseCheckout = sourcePatterns.${name};
      hash = filcHashes.${name};
    };
in
{
  inherit coreRev sourcePatterns filcHashes;

  # Minimal clang compiler only (filc0)
  filc0-src = mkFilcSrc "filc0-src";

  # C++ runtimes and their CMake support, independent of compiler sources.
  libcxx-src = mkFilcSrc "libcxx-src";

  # Just libpas + filc headers
  libpas-src = mkFilcSrc "libpas-src";

  # Yolo glibc (stage 1 runtime)
  yolo-glibc-src = mkFilcSrc "yolo-glibc-src";

  # User glibc (memory-safe glibc)
  user-glibc-src = mkFilcSrc "user-glibc-src";

  # compiler-rt (CRT files and builtins)
  compiler-rt-src = mkFilcSrc "compiler-rt-src";

  # yolounwind (stub unwind library for yolo runtime)
  yolounwind-src = mkFilcSrc "yolounwind-src";
}
