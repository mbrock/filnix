{ pkgs }:

let
  inherit (pkgs) fetchgit;
  filc-rev = "b71bd6a69294b779fda363e151a3ba11614c7211";
in
rec {
  # Minimal clang compiler only (filc0)
  filc0-src = fetchgit {
    url = "https://github.com/pizlonator/fil-c";
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
    hash = "sha256-rgNapyNF8Mu3DS4Dca4yiGlZN8lqeH9Y2yoAVVznT0E=";
  };

  # LLVM + libcxx + libcxxabi (for filc-libcxx build)
  libcxx-src = filc0-src;

  # Just libpas + filc headers
  libpas-src = fetchgit {
    url = "https://github.com/pizlonator/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "libpas"
      "filc"
    ];
    hash = "sha256-UlzhbAlMzesjiIZVYCUewbqTSwgLl4c04PHgBIAkmhE=";
  };

  # Yolo glibc (stage 1 runtime)
  yolo-glibc-src = fetchgit {
    url = "https://github.com/pizlonator/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "projects/yolo-glibc-2.40"
    ];
    hash = "sha256-qyieetxCggG7QfSKAkvEP/uNYzYuqtf/0I0PuLDMl3w=";
  };

  # User glibc (memory-safe glibc)
  user-glibc-src = fetchgit {
    url = "https://github.com/pizlonator/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "projects/user-glibc-2.40"
    ];
    hash = "sha256-FNZQspQBxMfyo+P1z6q5ggkoGE9DDW95DXZB5RmNNZQ=";
  };

  # libxcrypt
  libxcrypt-src = fetchgit {
    url = "https://github.com/pizlonator/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "projects/libxcrypt-4.4.36"
    ];
    hash = pkgs.lib.fakeHash;
  };

  # compiler-rt (CRT files and builtins)
  compiler-rt-src = fetchgit {
    url = "https://github.com/pizlonator/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "compiler-rt"
      "cmake"
      "llvm"
    ];
    hash = "sha256-RChLGaSdzHqHImkj6MJOa0vBZ6H+9T5wbj5l8bsemPs=";
  };

  # yolounwind (stub unwind library for yolo runtime)
  yolounwind-src = fetchgit {
    url = "https://github.com/pizlonator/fil-c";
    rev = filc-rev;
    sparseCheckout = [
      "yolounwind"
    ];
    hash = "sha256-bgjXmlv52KpmjgmXh5Ff3Wau5qkeeqJdvN45C9RMZBg=";
  };
}
