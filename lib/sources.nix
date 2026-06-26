{ pkgs }:

let
  inherit (pkgs) fetchgit;
  upstream = builtins.fromJSON (builtins.readFile ./filc-upstream.json);
  hashData = builtins.fromJSON (builtins.readFile ./filc-hashes.json);
  filc-rev = upstream."filc-rev";
  sparseCheckouts = upstream.sparseCheckouts;
  filcHashes =
    assert hashData."filc-rev" == filc-rev;
    hashData.hashes;

  mkFilcSrc =
    name:
    fetchgit {
      url = "https://github.com/pizlonator/fil-c";
      rev = filc-rev;
      sparseCheckout = sparseCheckouts.${name};
      hash = filcHashes.${name};
    };
in
rec {
  inherit filc-rev sparseCheckouts filcHashes;

  # Minimal clang compiler only (filc0)
  filc0-src = mkFilcSrc "filc0-src";

  # LLVM + libcxx + libcxxabi (for filc-libcxx build)
  libcxx-src = filc0-src;

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
