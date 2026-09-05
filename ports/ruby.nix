{
  mkRuby,
  mkRubyVersion,
  defaultGemConfig,
  buildPackages,
  pkgs,
}:
# Ruby's version also determines its soname and gem metadata. Instantiate the
# versioned nixpkgs definition instead of replacing only its source attributes.
(mkRuby {
  version = mkRubyVersion "3" "3" "10" "";
  hash = "sha256-tVW6pGejBs/I5sbtJNDSeyfpob7R2R2VUJhZ6saw6Sg=";
}).override
  {
    yjitSupport = false;
    jitSupport = false;
    cargo = null;
    rustPlatform = null;
    rustc = null;
    defaultGemConfig =
      defaultGemConfig
      // (import ./rubyPorts-as-gemConfig.nix {
        pkgs = buildPackages;
        final = pkgs;
      });
  }
