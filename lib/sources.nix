{ base }:

let
  inherit (base) fetchgit;
  filc-rev = "d1f83629d6c56d1fdf6f3e207d7f06c2ef31ecda";
in
rec {
  # Minimal clang compiler only (filc0)
  filc0-src = fetchgit {
    url = "https://github.com/mbrock/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "llvm"
      "clang"
      "cmake"
      "third-party"
      "libc" # for "shared/fp_bits.h" among other things
      "libcxx"
      "libcxxabi"
      "runtimes"
    ];
    hash = "sha256-iLdlrzcEZfFdhEo1Zz8l/1ZiUBc8f3slGdX2X6oRU6A=";
  };

  # LLVM + libcxx + libcxxabi (for filc-libcxx build)
  libcxx-src = filc0-src;

  # Just libpas + filc headers
  libpas-src = fetchgit {
    url = "https://github.com/mbrock/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "libpas"
      "filc"
    ];
    hash = "sha256-uiraSFXY0mhH/PtcV4IwTT7qrePW0t/ji3JjPRFDtTE=";
  };

  # Yolo glibc (stage 1 runtime)
  yolo-glibc-src = fetchgit {
    url = "https://github.com/mbrock/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "projects/yolo-glibc-2.40"
    ];
    hash = "sha256-BGF8EWfzLYUAheyMVETNoV4KNsQTATc4FxBktgEEqTE=";
  };

  # User glibc (memory-safe glibc)
  user-glibc-src = fetchgit {
    url = "https://github.com/mbrock/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "projects/user-glibc-2.40"
    ];
    hash = "sha256-NaDSI9zonbam48fk/UzUMNnpX/ATKjDET7qJDffVDGo=";
  };

  # libxcrypt
  libxcrypt-src = fetchgit {
    url = "https://github.com/mbrock/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "projects/libxcrypt-4.4.36"
    ];
    hash = base.lib.fakeHash;
  };
}
