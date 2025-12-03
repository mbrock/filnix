{
  pkgs,
}:
let
  inherit (import ./ports { inherit (pkgs) lib pkgs; })
    for
    use
    ;
in
[
  (for "ruby-terminfo" [
    (use (attrs: {
      postPatch = (attrs.postPatch or "") + ''
        substituteInPlace terminfo.c \
          --replace 'RTEST(ret)' 'RTEST((VALUE)ret)'
      '';
    }))
  ])
]
