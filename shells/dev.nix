{
  base,
  toolchain,
  compiler,
  runtime,
}:

let
  inherit (toolchain) filcc filc-aliases;
  inherit (compiler) filc-libcxx;
  inherit (runtime) libpizlo libmojo;

in
{
  default = base.mkShell {
    name = "filc-dev";

    buildInputs = with base; [
      filcc
      filc-aliases
      cmake
      ninja
      ccache
      git
      gdb
      valgrind
      strace
      ltrace
      hexdump
      ripgrep
      fd
      jq
      bat
    ];

    shellHook = ''
      export CC=filc
      export CXX=filc++

      clang --version | head -1
      echo
      echo "  filc     $(which filc)"
      echo "  filc++   $(which filc++)"
      echo "  pizlo    ${libpizlo}"
      echo "  glibc    ${libmojo}"
      echo "  libc++   ${filc-libcxx}"
      echo
    '';
  };
}
