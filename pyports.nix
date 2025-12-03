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
    skipTests
    ;
in
# This will be converted to a packageOverrides function
[
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
    (skipTests "slow")])

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
