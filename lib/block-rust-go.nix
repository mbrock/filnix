# A stdenv adapter that marks Rust and Go derivations broken.
#
# Fil-C compiles C and C++. Rust and Go bring their own compilers and
# runtimes, so a Fil-C build of them is either impossible or not memory safe
# in the Fil-C sense. With this adapter such packages fail evaluation with a
# "broken" problem that says why, instead of reaching a confusing error deep
# in rustc's or Go's platform tables. Native tools used at build time are
# unaffected: they come from buildPackages, whose stdenv this adapter does not
# touch.
#
# Servers whose processes share memory that holds pointers are refused the
# same way: the PostgreSQL server here, nginx in ports.nix. Fil-C
# keeps each pointer's capability in the process's own shadow memory, so a
# pointer one process stores in shared memory has none in another
# (docs/nixos-userland.md). Their client libraries, such as libpq, are
# separate packages and stay Fil-C.
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
    if (attrs.pname or null) == "postgresql" then
      "PostgreSQL"
    else if lib.any isRust names || (attrs.cargoDeps or null) != null then
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
            message =
              let
                name =
                  if blocked == "PostgreSQL" then
                    "postgresql_${lib.versions.major old.version}"
                  else
                    old.pname or (lib.getName (old.name or "it"));
                why =
                  if blocked == "PostgreSQL" then
                    "${blocked} cannot be Fil-C: its processes share memory that holds pointers, and a Fil-C pointer's capability does not cross processes."
                  else
                    "${blocked} has no Fil-C target.";
              in
              "${why} Take the native build instead, with filc.native = native: { inherit (native) ${name}; }; in your system's configuration, or leave it out.";
          };
        };
    };
  }
)
