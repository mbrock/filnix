{
  pkgs,
}:
let
  inherit (import ./ports { inherit (pkgs) lib pkgs; })
    for
    use
    ;

  replace = file: old: new:
    use (attrs: {
      postPatch = (attrs.postPatch or "") + ''
        substituteInPlace ${file} \
          --replace-fail ${pkgs.lib.escapeShellArg old} \
                         ${pkgs.lib.escapeShellArg new}
      '';
    });

in
[
  (for "ruby-terminfo" [
    (replace "terminfo.c" "RTEST(ret)" "RTEST((VALUE)ret)")
  ])

  (for "msgpack" [
    (replace "ext/msgpack/buffer_class.c"
      "unsigned long max = ((VALUE*) args)[2];"
      "unsigned long max = (unsigned long)(uintptr_t)((VALUE*) args)[2];")
    (replace "ext/msgpack/buffer_class.c"
      "(VALUE) max,"
      "(VALUE)(uintptr_t) max,")
  ])
]
