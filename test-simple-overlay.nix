# Dead simple test: does the overlay apply to dependencies?

{ lib }:

final: prev: {
  zlib = prev.zlib.overrideAttrs (old: {
    name = "ZLIB-OVERLAY-MARKER-${old.version}";
  });
}

