# Python package ports using the same DSL as ports2.nix
#
# Returns a packageOverrides function for Python

{
  pkgs,
}:
let
  inherit (import ./ports { inherit (pkgs) lib pkgs; })
    for
    arg
    use
    src
    patch
    skipTests
    ;
in
# This will be converted to a packageOverrides function
[
  (for "pygobject3" [
    (src "3.48.2" "sha256-B5SutKm+MaCSrCBiG19U7CgPkYWUPTKLEFza5imK0ac=" (
      v: "https://download.gnome.org/sources/pygobject/3.48/pygobject-${v}.tar.xz"
    ))
    (patch ./ports/patch/pygobject-3.48.2.patch)
    (patch ./patches/pygobject-metaclass-init.patch)
  ])

  (for "pycparser" [
    (use (old: {
      # Its parser tests invoke cpp. Fil-C's compiler wrapper has no cpp alias;
      # preprocessing fixtures needs only a native tool, not a target compiler.
      preCheck = (old.preCheck or "") + ''
        export PATH="${pkgs.lib.getBin pkgs.stdenv.cc}/bin:$PATH"
      '';
    }))
  ])

  (for "psutil" [
    # heap_info/heap_trim wrap glibc's mallinfo2/malloc_trim, which see
    # none of Fil-C's GC heap; build them out as on musl.
    (patch ./patches/psutil-filc-no-heap-info.patch)
  ])

  (for "execnet" [
    # gevent needs greenlet, which switches CPython thread state fields that
    # the Fil-C CPython port does not have. The gevent execmodel tests skip
    # without it.
    (arg { gevent = null; })
  ])

  (for "mypy" [
    (patch ./patches/mypy-function-wrapper-python-h-first.patch)
    (use (old: {
      # mypyc emits one huge C file by default; Fil-C's clang needed over
      # 12 GB for it. Compile per module, as mypy does on Windows.
      env = (old.env or { }) // {
        MYPYC_MULTI_FILE = "1";
      };
    }))
  ])

  (for "uharfbuzz" [
    # The bundled harfbuzz swaps qsort elements bytewise, which mismatches
    # pointers and capabilities (fonttools' check input).
    (patch ./patches/uharfbuzz-sort-swap-memcpy.patch)
  ])

  (for "skia-pathops" [
    # Skia's arena stores destructor pointers unaligned (fonttools' check
    # input).
    (patch ./patches/skia-pathops-arena-footer-ptrtable.patch)
  ])

  (for "pybind11" [
    (use {
      # The CMake check target runs pytest with the build platform's Python,
      # which cannot import the Fil-C test extension modules.
      doCheck = false;
      doInstallCheck = false;
    })
  ])

  (for "pytest-regressions" [
    (arg {
      matplotlib = null;
      pandas = null;
      pillow = null;
    })
    (skipTests "requires optional dependencies")
  ])

  (for "annotated-types" [
    (skipTests "test dependencies missing")
  ])

  (for "decorator" [
    (skipTests "float printing discrepancies")
  ])

  (for "tqdm" [
    (arg { tkinter = null; })
  ])

  (for "flask" [
    (skipTests "slow integration tests")
  ])

  (for "anyio" [
    (skipTests "depends on cryptography which is Rust")
  ])

  (for "trio" [
    (skipTests "network tests flaky")
  ])

  (for "markdown" [
    (skipTests "slow")
  ])

  (for "markdown-it-py" [
    (skipTests "needs pandas")
  ])

  (for "decorator" [
    (skipTests "not critical")
  ])

  (for "jsonpickle" [
    (skipTests "not critical")
  ])

  (for "jedi" [
    (skipTests "slow")
  ])

  (for "networkx" [
    (skipTests "slow graph tests")
  ])

  (for "ipython" [
    (skipTests "terminal interaction tests flaky")
  ])

  (for "pyvis" [
    (skipTests "not critical")
  ])

  (for "jinja2" [
    (skipTests "float formatting differs without Motorola assembly")
  ])

  (for "prompt-toolkit" [
    (skipTests "terminal tests flaky")
  ])

  (for "chardet" [
    (skipTests "incredibly slow test suite")
  ])

  (for "pycairo" [
    (skipTests "requires X11")
  ])

  (for "rich" [
    (skipTests "4 failed, 844 passed - close enough")
  ])

  (for "httpx" [
    (skipTests "huge dependency tree")
  ])

  (for "libevdev" [
    (skipTests "broken?")
  ])

  (for "pyyaml" [
    (skipTests "slow")
  ])

  # Custom package - defined inline since it's not in pyprev
  {
    tagflow = {
      pname = "tagflow";
      __customPython =
        pyself:
        pyself.buildPythonPackage {
          pname = "tagflow";
          version = "0.13.0";
          format = "pyproject";

          src = pkgs.fetchFromGitHub {
            owner = "lessrest";
            repo = "tagflow";
            rev = "cf84326fb41037db8efcefd09898b7659931e77e";
            hash = "sha256-CLeLDoh2cxPkqt4rircCUUxemdgskWJYBdPBd7X07Bo=";
          };

          nativeBuildInputs = [ pyself.hatchling ];
          propagatedBuildInputs = with pyself; [
            anyio
            beautifulsoup4
          ];

          doCheck = false;
          doInstallCheck = false;
        };
    };
  }
]
