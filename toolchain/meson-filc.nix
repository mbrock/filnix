# Meson runs natively but emits GType registration code for the Fil-C target.
{ pkgs }:
pkgs.meson.overrideAttrs (old: {
  patches = (old.patches or [ ]) ++ [ ../patches/meson-gtype.patch ];
})
