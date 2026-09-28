# Rehost a pure-JS npm CLI on qnode. The package is built natively
# (buildPackages: npm, bundlers and node run at build time only); its
# lib/node_modules is platform-independent JavaScript. Only the launcher
# changes, from node to qnode.
{
  lib,
  runCommand,
  makeWrapper,
  qnode,
}:
{
  # The native build, e.g. buildPackages.bibtex-tidy.
  package,
  # Executable name -> script path relative to lib/node_modules.
  bins,
}:
runCommand "${package.pname}-${package.version}"
  {
    inherit (package) pname version;
    nativeBuildInputs = [ makeWrapper ];
    meta = package.meta // {
      platforms = lib.platforms.linux;
    };
  }
  (
    ''
      mkdir -p $out/lib $out/bin
      cp -r ${package}/lib/node_modules $out/lib/
      chmod -R u+w $out/lib
      # Native node shebangs would keep the build platform's node in the
      # runtime closure; qnode ignores the shebang line.
      grep -rlZ '^#!/nix/store/[^/]*-nodejs' $out/lib | \
        xargs -0 -r sed -i '1s|^#!/nix/store/[^ ]*|#!/usr/bin/env node|'
    ''
    + lib.concatStrings (
      lib.mapAttrsToList (name: script: ''
        makeWrapper ${lib.getExe qnode} $out/bin/${name} \
          --add-flags $out/lib/node_modules/${script}
      '') bins
    )
  )
