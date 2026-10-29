# The nanofil package survey (docs/survey.md). `nanofilize` is a
# package adapter: drv built with nanofil as its C compiler, in the Fil-C
# staging package set (whose libraries, built by filcc, it links with),
# and nothing else compiling its C: cc.sh hands every C compile to
# nanofil-cc and refuses what it cannot, so a package builds with nanofil
# alone or fails. C++ still goes to filcc and is counted (cxx.sh). Its
# own checkPhase runs where the port's package runs one.
#
#   nix build -f nanofil/survey ref.zlib   # the filcc build
#   nix build -f nanofil/survey nf.zlib    # the same package by nanofil
#   nix eval --json -f nanofil/survey meta.zlib # versions, sources, deps
#
# The build log ends with "nanofil-survey: N objects, M C++, K fallbacks"
# on success, and on failure also the first nanofil errors that
# configure, meson or cmake logged.
{
  repo ? ../..,
}:
let
  flake = builtins.getFlake (toString repo);
  system = "x86_64-linux";
  pkgs = import flake.inputs.nixpkgs { inherit system; };
  filcc = flake.packages.${system}.filcc-staging;
  pkgsFilc = flake.legacyPackages.${system}.pkgsFilcStaging;
  lib = pkgs.lib;
  # Only bin/ and src/, so that the survey's own results and docs do not
  # change the nanofil builds.
  nanofil-cc = import ../nix/nanofil-cc.nix {
    inherit pkgs filcc;
    src = lib.fileset.toSource {
      root = ../.;
      fileset = lib.fileset.unions [
        ../bin
        ../src
      ];
    };
  };
  cc = pkgs.runCommand "nanofil-survey-cc" { } ''
    mkdir -p $out/bin
    for f in cc cxx; do
      substitute ${./.}/$f.sh $out/bin/$f --subst-var-by bash ${pkgs.bash}/bin/bash \
        --subst-var-by nanofilcc ${nanofil-cc} --subst-var-by filcc ${filcc}
      chmod +x $out/bin/$f
    done
    for n in clang gcc; do ln -s cc $out/bin/$n; done
    for n in c++ clang++ g++; do ln -s cxx $out/bin/$n; done
  '';
  report = ''
    nanofilSurveyReport() {
      local log=$NIX_BUILD_TOP/nanofil.log
      echo "nanofil-survey: $(grep -cv '^\(cxx\|fallback\) ' $log) objects," \
        "$(grep -c '^cxx ' $log) C++, $(grep -c '^fallback ' $log) fallbacks"
    }
  '';
  nanofilize =
    drv:
    drv.overrideAttrs (old: {
      postHook = (old.postHook or "") + ''
        export NANOFIL_LOG=$NIX_BUILD_TOP/nanofil.log
        : >$NANOFIL_LOG
        export PATH=${cc}/bin:$PATH CC=${cc}/bin/cc CXX=${cc}/bin/c++
        ${report}
      '';
      exitHook = (old.exitHook or "") + "\nnanofilSurveyReport\n";
      failureHook = (old.failureHook or "") + ''

        nanofilSurveyReport
        find $NIX_BUILD_TOP \( -name config.log -o -name meson-log.txt \
          -o -name CMakeError.log -o -name CMakeConfigureLog.yaml \) 2>/dev/null |
          while read -r f; do grep -m 3 '^nanofil: ' "$f" | sed "s|^|nanofil-survey-config: |"; done
      '';
    });
  names = lib.filter (n: n != "<custom>") (
    lib.flatten (
      map
        (
          i:
          if i ? pname then
            [ (if i.pname == null then "<custom>" else i.pname) ]
          else
            builtins.attrNames i
        )
        (
          import ../../ports.nix {
            inherit pkgs;
            prev = pkgs;
            final = pkgs;
          }
        )
    )
  );
  present = lib.filter (n: pkgsFilc ? ${n}) names;
  # A package's own build dependencies' names, to set aside what needs
  # LLVM, Rust or Go.
  depNames =
    p:
    map (d: d.pname or (builtins.parseDrvName (d.name or "")).name) (
      lib.filter lib.isDerivation (
        (p.nativeBuildInputs or [ ])
        ++ (p.buildInputs or [ ])
        ++ (p.propagatedBuildInputs or [ ])
      )
    );
  try =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if r.success then r.value else null;
  info =
    n:
    let
      p = pkgsFilc.${n};
    in
    {
      version = try (p.version or "");
      ref = try p.drvPath;
      nf = try (nanofilize p).drvPath;
      src = try (toString (p.src or ""));
      srcDrv = try (p.src.drvPath or "");
      # Its checkPhase or installCheckPhase runs (tpm2-tss runs `make
      # check` as its installCheck).
      doCheck = try ((p.doCheck or false) || (p.doInstallCheck or false));
      deps = try (depNames p);
    };
in
{
  inherit nanofilize cc;
  names = present;
  meta = lib.genAttrs present info;
  ref = lib.genAttrs present (n: pkgsFilc.${n});
  nf = lib.genAttrs present (n: nanofilize pkgsFilc.${n});
}
