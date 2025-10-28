# Query comprehensive package information from nixpkgs
# Usage: nix eval --json .#lib.x86_64-linux.queryPackage --apply 'f: f "bash"'
pkgs: packageName:

let
  
  extractInput = x: 
    if builtins.isPath x then {
      type = "setup-hook";
      path = builtins.baseNameOf (builtins.toString x);
      fullPath = builtins.toString x;
    }
    else if builtins.isAttrs x then {
      type = "derivation";
      name = x.pname or x.name or "unnamed";
    }
    else if builtins.isString x then {
      type = "string";
      value = x;
    }
    else {
      type = "unknown";
      typeOf = builtins.typeOf x;
    };
  
  # Extract list-like attributes safely
  extractList = pkg: attr: 
    let val = pkg.${attr} or null;
    in if val == null then []
       else if builtins.isList val then val
       else [val];
  
  # Extract NIX_ environment variables
  extractNixVars = pkg:
    let
      allAttrs = builtins.attrNames pkg;
      nixAttrs = builtins.filter (name: 
        builtins.substring 0 4 name == "NIX_"
      ) allAttrs;
    in builtins.listToAttrs (map (name: { 
      name = name; 
      value = pkg.${name}; 
    }) nixAttrs);
  
  # Extract derivation structure
  extractDerivation = pkg: {
    type = pkg.type or null;
    system = pkg.system or null;
    builder = builtins.toString (pkg.builder or "");
    args = pkg.args or [];
    drvPath = pkg.drvPath or null;
    
    # Custom build phases (if defined)
    phases = {
      preConfigure = pkg.preConfigure or null;
      configurePhase = pkg.configurePhase or null;
      postConfigure = pkg.postConfigure or null;
      preBuild = pkg.preBuild or null;
      buildPhase = pkg.buildPhase or null;
      postBuild = pkg.postBuild or null;
      preInstall = pkg.preInstall or null;
      installPhase = pkg.installPhase or null;
      postInstall = pkg.postInstall or null;
      preFixup = pkg.preFixup or null;
      fixupPhase = pkg.fixupPhase or null;
      postFixup = pkg.postFixup or null;
    };
  };
  
  # Get function arguments from package definition
  getFunctionArgs = pkg:
    let
      position = pkg.meta.position or "";
      filePath = if position != "" then 
        builtins.head (builtins.split ":" position)
      else null;
      pkgFunc = if filePath != null then import filePath else null;
    in if pkgFunc != null then builtins.functionArgs pkgFunc else {};
  
  # Format function args as required/optional
  formatArgs = args:
    let
      required = builtins.filter (name: args.${name} == false) (builtins.attrNames args);
      optional = builtins.filter (name: args.${name} == true) (builtins.attrNames args);
    in { inherit required optional; };
  
  # Extract relative path from nix store position
  extractPath = position:
    let
      parts = builtins.split "-source/" position;
      hasSource = builtins.length parts > 1;
      afterSource = if hasSource then builtins.elemAt parts 2 else "";
      pathParts = builtins.split ":" afterSource;
    in if afterSource != "" then builtins.head pathParts else "";
  
  pkg = pkgs.${packageName} or (throw "Package '${packageName}' not found in nixpkgs");
  position = pkg.meta.position or "";
  args = getFunctionArgs pkg;

in {
  # Basic info
  name = packageName;
  version = pkg.version or "unknown";
  pname = pkg.pname or packageName;
  path = extractPath position;
  
  # Function signature
  functionArgs = formatArgs args;
  
  # Build inputs (with structured types)
  buildInputs = {
    native = map extractInput (pkg.nativeBuildInputs or []);
    build = map extractInput (pkg.buildInputs or []);
    propagated = map extractInput (pkg.propagatedBuildInputs or []);
  };
  
  # Build configuration
  buildConfig = {
    configureFlags = extractList pkg "configureFlags";
    makeFlags = extractList pkg "makeFlags";
    cmakeFlags = extractList pkg "cmakeFlags";
    mesonFlags = extractList pkg "mesonFlags";
    patches = map builtins.toString (extractList pkg "patches");
  };
  
  # Build flags
  buildFlags = {
    outputs = pkg.outputs or ["out"];
    doCheck = pkg.doCheck or null;
    doInstallCheck = pkg.doInstallCheck or null;
    enableParallelBuilding = pkg.enableParallelBuilding or null;
    enableParallelChecking = pkg.enableParallelChecking or null;
    separateDebugInfo = pkg.separateDebugInfo or null;
    strictDeps = pkg.strictDeps or null;
    hardeningDisable = pkg.hardeningDisable or [];
  };
  
  # NIX environment variables
  nixVars = extractNixVars pkg;
  
  # Derivation structure (how it's actually built)
  derivation = extractDerivation pkg;
  
  # Metadata
  meta = {
    description = pkg.meta.description or null;
    homepage = pkg.meta.homepage or null;
    license = 
      if pkg.meta ? license then
        if builtins.isAttrs pkg.meta.license then
          pkg.meta.license.shortName or pkg.meta.license.spdxId or "unknown"
        else pkg.meta.license
      else null;
    mainProgram = pkg.meta.mainProgram or null;
    platforms = pkg.meta.platforms or [];
    position = position;
  };
  
  # Source information
  src = 
    if pkg ? src then
      if builtins.isAttrs pkg.src then {
        type = "derivation";
        drvPath = pkg.src.drvPath or null;
        outPath = pkg.src.outPath or null;
        urls = pkg.src.urls or [];
        hash = pkg.src.outputHash or null;
      }
      else if builtins.isPath pkg.src then {
        type = "path";
        path = builtins.toString pkg.src;
      }
      else {
        type = "unknown";
        value = builtins.toString pkg.src;
      }
    else null;
}
