{ source, attrPath }:
let
  flake = builtins.getFlake source;
  pkgs = flake.legacyPackages.x86_64-linux.pkgsFilc;
  p = builtins.foldl' (set: key: builtins.getAttr key set) pkgs attrPath;
  inputs =
    role: xs:
    map (x: {
      inherit role;
      drv = x.drvPath;
    }) (builtins.filter (x: builtins.isAttrs x && x ? drvPath) xs);
in
{
  drv = p.drvPath;
  name = p.name;
  outputs = builtins.listToAttrs (
    map (o: {
      name = o;
      value = p.${o}.outPath;
    }) p.outputs
  );
  doCheck = p.doCheck or false;
  doInstallCheck = p.doInstallCheck or false;
  compiler = p.stdenv.cc.drvPath or null;
  expectedCompiler = pkgs.stdenv.cc.drvPath;
  hostPlatform = p.stdenv.hostPlatform.config or null;
  patches = map toString (p.patches or [ ]);
  roles =
    inputs "host" ((p.buildInputs or [ ]) ++ (p.propagatedBuildInputs or [ ]))
    ++ inputs "native" (
      (p.nativeBuildInputs or [ ]) ++ (p.propagatedNativeBuildInputs or [ ])
    )
    ++ inputs "host-check" (p.checkInputs or [ ])
    ++ inputs "native-check" (p.nativeCheckInputs or [ ]);
}
