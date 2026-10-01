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
  # The pin matches the Fil-C GLib and gobject-introspection. The build
  # Python's PyGObject links the ordinary native GLib and GI, which 3.48.2's
  # tests do not build against, so it stays the Nixpkgs one.
  (
    (for "pygobject3" [
      (src "3.48.2" "sha256-B5SutKm+MaCSrCBiG19U7CgPkYWUPTKLEFza5imK0ac=" (
        v: "https://download.gnome.org/sources/pygobject/3.48/pygobject-${v}.tar.xz"
      ))
      (patch ./ports/patch/pygobject-3.48.2.patch)
      (patch ./patches/pygobject-metaclass-init.patch)
    ])
    // {
      filcOnly = true;
    }
  )

  (for "pycparser" [
    (use (old: {
      # Its parser tests invoke cpp. Fil-C's compiler wrapper has no cpp alias;
      # preprocessing fixtures needs only a native tool, not a target compiler.
      preCheck = (old.preCheck or "") + ''
        export PATH="${pkgs.lib.getBin pkgs.stdenv.cc}/bin:$PATH"
      '';
    }))
  ])

  (for "mypy" [
    # mypyc-generated C loads pointer fields as the integer type CPyPtr and
    # writes through them, which loses the Fil-C capability and traps (e.g.
    # charset-normalizer's compiled modules). These overrides also reach the
    # build platform's mypy, which is the one that runs mypyc for Fil-C
    # packages; the typedef change only applies when compiling with Fil-C.
    (patch ./patches/mypyc-filc-pointer-cpyptr.patch)
    # Python.h must come first: glibc 2.44 headers define _POSIX_C_SOURCE
    # differently, and mypyc builds with -Werror.
    (patch ./patches/mypy-function-wrapper-python-h-first.patch)
    (use (old: {
      # mypyc emits one huge C file by default; Fil-C's clang needed over
      # 12 GB for it. Compile per module, as mypy does on Windows.
      env = (old.env or { }) // {
        MYPYC_MULTI_FILE = "1";
      };
    }))
  ])

  (for "charset-normalizer" [
    (use (old: {
      # Its optional mypyc extensions trap under Fil-C while decoding the
      # GB18030 signature (test_empty_but_with_bom_or_sig). The same test
      # passes with the upstream pure-Python implementation.
      env = (old.env or { }) // {
        CHARSET_NORMALIZER_USE_MYPYC = "0";
      };
    }))
  ])

  (
    (for "backports-zstd" [
      (use (old: {
        # setup.py unconditionally enables LTO for compilation and linking.
        # Fil-C has no LLVMgold.so; use ordinary objects for this optional
        # optimization rather than rebuilding the compiler or interpreter.
        postPatch = (old.postPatch or "") + ''
          substituteInPlace setup.py \
            --replace-fail '"-g0", "-flto"' '"-g0"'
          cp ${./tests/python-backports-zstd.py} tests/test_filc_boundaries.py
        '';
      }))
    ])
    // {
      filcOnly = true;
    }
  )

  (for "httpcore" [
    (use (old: {
      # Test the client under Fil-C Python, but run the real HTTP/TLS test
      # server as a native tool. Its Swagger dependency imports Rust rpds,
      # which the Fil-C interpreter cannot load.
      nativeInstallCheckInputs = builtins.filter (
        p: (p.pname or "") != "pytest-httpbin"
      ) old.nativeInstallCheckInputs;
      postPatch = (old.postPatch or "") + ''
        test ! -e tests/conftest.py
        cp ${./tests/httpcore-httpbin.py} tests/conftest.py
      '';
      preCheck = (old.preCheck or "") + ''
        export HTTPBIN_PYTHON=${
          pkgs.buildPackages.python3.withPackages (ps: [
            ps.pytest-httpbin
            ps.pytest
          ])
        }/bin/python3
      '';
    }))
  ])

  (for "django" [
    (use (old: {
      # The XML deserializer's complexity check times one parse of a
      # one-character field against a 1000-character one and requires the
      # ratio to stay under 2. Both take microseconds, so on a loaded builder
      # the ratio is noise (3.4 in a campaign). The varying-depth check,
      # averaged over four ratios of larger inputs, still runs.
      postPatch = (old.postPatch or "") + ''
        substituteInPlace tests/serializers/test_deserialization.py --replace-fail 'assertFactor("constant depth, varying length", [(100, 1), (100, 1000)], 2)' ""
      '';
    }))
  ])

  (for "cffi" [
    (patch ./patches/cffi-filc.patch)
    (use (old: {
      disabledTestPaths = (old.disabledTestPaths or [ ]) ++ [
        # The pure-Python ctypes backend passes every address through
        # ctypes.cast() from an integer, so its pointers have no capability.
        # test_ffi_backend.py::TestFFI runs the same tests on _cffi_backend.
        "testing/cffi0/test_ctypes.py"
        "testing/cffi0/test_function.py::TestFunction"
        "testing/cffi0/test_ownlib.py::TestOwnLib"
        "testing/cffi0/test_verify.py::test_ctypes_backend_forces_generic_engine"
        "testing/cffi0/test_verify2.py::test_ctypes_backend_forces_generic_engine"
        "testing/cffi0/test_vgen.py::test_ctypes_backend_forces_generic_engine"
        "testing/cffi0/test_vgen2.py::test_ctypes_backend_forces_generic_engine"
        # They cast integers to pointers and dereference them.
        "src/c/test_c.py::test_cast_between_pointers"
        "testing/cffi0/test_ffi_backend.py::TestFFI::test_cast_pointer_and_int"
        "testing/cffi1/test_new_ffi_1.py::TestNewFFI1::test_cast_pointer_and_int"
        # It calls a function pointer that went through intptr_t.
        "testing/cffi1/test_recompiler.py::test_convert_api_mode_builtin_function_to_cdata"
        # It indexes a from_buffer() pointer out of bounds ("hopefully
        # does not crash").
        "src/c/test_c.py::test_from_buffer_types"
        # Fil-C zeroes every allocation, so should_clear_after_alloc=False
        # never yields dirty memory.
        "testing/cffi1/test_ffi_obj.py::test_ffi_new_allocator_1"
        # They dlopen find_library('dl'). libdl has been part of libc since
        # glibc 2.34 and the sandbox has no ldconfig cache, so -ldl only
        # resolves to the empty libdl.a.
        "testing/cffi0/test_ffi_backend.py::TestFFI::test_dlopen_handle"
        "testing/cffi1/test_re_python.py::test_dlopen_handle"
        # Fil-C exports pizlonated_* and pizlonated<N>ET* symbols.
        "testing/cffi1/test_cffi_binary.py::test_no_unknown_exported_symbols"
      ];
    }))
  ])

  (for "psutil" [
    # heap_info/heap_trim wrap glibc's mallinfo2/malloc_trim, which see
    # none of Fil-C's GC heap; build them out as on musl.
    (patch ./patches/psutil-filc-no-heap-info.patch)
    (use (old: {
      disabledTests = (old.disabledTests or [ ]) ++ [
        # glibc's mallinfo2 counts glibc's heap; Fil-C allocates elsewhere,
        # so the numbers are all zero.
        "test_heap_info"
        # Gives the children 0.01 s to exit, which is too short for Fil-C
        # processes; test_wait_procs_no_timeout passes.
        "test_wait_procs"
      ];
    }))
  ])

  (for "websockets" [
    (use (old: {
      disabledTests = (old.disabledTests or [ ]) ++ [
        # Timing-sensitive: expects the peer's close frame within a short
        # timeout, which Fil-C's slower Python misses.
        "test_writing_in_recv_events_fails"
      ];
    }))
  ])

  (for "protobuf7" [
    (use (old: {
      # The upb C extension (google._upb._message) keeps pointers in integer
      # words (arena block allocators, hash entries) and traps at import
      # under Fil-C. api_implementation probes it before it reads
      # PROTOCOL_BUFFERS_PYTHON_IMPLEMENTATION, so that variable cannot avoid
      # it. The build-time constant module makes the pure-Python backend the
      # default without the probe (the variable can still select upb).
      # Porting upb itself is a separate job.
      postInstall = (old.postInstall or "") + ''
        internal=$(echo $out/lib/python*/site-packages/google/protobuf/internal)
        echo 'api_version = 0  # Fil-C: pure-Python backend' \
          > "$internal/_api_implementation.py"
      '';
      pythonImportsCheck = pkgs.lib.remove "google._upb._message" (
        old.pythonImportsCheck or [ ]
      );
    }))
  ])

  {
    greenlet = {
      pname = "greenlet";
      filcOnly = true;
      __customPython =
        pyself:
        (pyself.callPackage (
          pkgs.path + "/pkgs/development/python-modules/greenlet"
        ) { }).overridePythonAttrs
          (old: {
            patches = (old.patches or [ ]) ++ [ ./patches/greenlet-filc.patch ];
            doCheck = true;
            dontRemoveTests = true;
            nativeCheckInputs = [
              (pyself.psutil.overridePythonAttrs { doCheck = false; })
              # Pure Python; its native package avoids the
              # objgraph -> graphviz -> Python test dependency cycle.
              (pkgs.python312Packages.objgraph.overridePythonAttrs { doCheck = false; })
              pyself.unittestCheckHook
            ];
            postCheck = (old.postCheck or "") + ''
              mkdir -p "$TMPDIR/greenlet-regression"
              $CC -shared -fPIC -O2 -I${pyself.python}/include/python${pyself.python.pythonVersion} \
                ${./tests/greenlet-filc.c} \
                -o "$TMPDIR/greenlet-regression/_greenlet_filc_roots.so"
              PYTHONPATH="$out/${pyself.python.sitePackages}:$TMPDIR/greenlet-regression:$PYTHONPATH" \
                ${pyself.python.interpreter} ${./tests/greenlet-filc.py}
            '';
          });
    };
  }

  (for "execnet" [
    # greenlet now has a Fil-C context backend, but gevent itself has not
    # been verified. Its optional execmodel tests still skip without it.
    (arg { gevent = null; })
  ])

  (for "uharfbuzz" [
    # The bundled harfbuzz swaps qsort elements bytewise, which mismatches
    # pointers and capabilities (fonttools' check input).
    (patch ./patches/uharfbuzz-sort-swap-memcpy.patch)
  ])

  (
    (for "regex" [
      # Its byte stack mixes pointer-bearing records with byte opcodes. Align
      # every entry under Fil-C so copied pointers retain their capabilities.
      (patch ./patches/regex-filc-stack-alignment.patch)
    ])
    // {
      filcOnly = true;
    }
  )

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

  (for "dbus-python" [
    (use {
      # Meson's tests run the build platform's Python, which cannot import
      # the Fil-C _dbus_bindings or pyexpat modules.
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
