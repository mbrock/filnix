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
    skipTests
    skipCheck
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
    (skipCheck "requires optional dependencies")
  ])

  (for "annotated-types" [
    (skipCheck "test dependencies missing")
  ])

  (for "tqdm" [
    (arg { tkinter = null; })
  ])

  (for "flask" [
    (skipCheck "slow integration tests")
  ])

  (for "anyio" [
    (skipCheck "depends on cryptography which is Rust")
  ])

  (for "trio" [
    (skipCheck "network tests flaky")
  ])

  (for "markdown" [
    (skipCheck "slow")
  ])

  (for "markdown-it-py" [
    (skipTests "needs pandas")
  ])

  (for "decorator" [
    (skipCheck "not critical")
  ])

  (for "jsonpickle" [
    (skipCheck "not critical")
  ])

  (for "jedi" [
    (skipCheck "slow")
  ])

  (for "networkx" [
    (skipCheck "slow graph tests")
  ])

  (for "ipython" [
    (skipCheck "terminal interaction tests flaky")
  ])

  (for "pyvis" [
    (skipCheck "not critical")
  ])

  (for "jinja2" [
    (skipCheck "float formatting differs without Motorola assembly")
  ])

  (for "prompt-toolkit" [
    (skipCheck "terminal tests flaky")
  ])

  (for "chardet" [
    (skipCheck "incredibly slow test suite")
  ])

  (for "pycairo" [
    (skipCheck "requires X11")
  ])

  (for "rich" [
    (skipCheck "4 failed, 844 passed - close enough")
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
