# A stdenv adapter that marks Rust and Go derivations broken.
#
# Fil-C compiles C and C++. Rust and Go bring their own compilers and
# runtimes, so a Fil-C build of them is either impossible or not memory safe
# in the Fil-C sense. With this adapter such packages fail evaluation with a
# "broken" problem that says why, instead of reaching a confusing error deep
# in rustc's or Go's platform tables. Native tools used at build time are
# unaffected: they come from buildPackages, whose stdenv this adapter does not
# touch.
{ lib, stdenvAdapters }:
let
  compiler =
    attrs:
    let
      names = map lib.getName (
        lib.filter lib.isDerivation (attrs.nativeBuildInputs or [ ])
      );
      isRust = n: n == "rustc" || n == "cargo" || lib.hasSuffix "-cargo" n;
    in
    if lib.any isRust names || (attrs.cargoDeps or null) != null then
      "Rust"
    else if lib.elem "go" names then
      "Go"
    else
      null;
in
stdenvAdapters.overrideMkDerivationArgs (
  old:
  let
    blocked = compiler old;
  in
  {
    # Only the problem's presence depends on the inputs, not the shape of
    # meta: deciding the shape from nativeBuildInputs recurses.
    meta = (old.meta or { }) // {
      problems =
        (old.meta.problems or { })
        // lib.optionalAttrs (blocked != null) {
          filc = {
            kind = "broken";
            message = "${blocked} has no Fil-C target. Use the native build instead (filc.userland.native in finix), or leave it out.";
          };
        };
    };
  }
)
