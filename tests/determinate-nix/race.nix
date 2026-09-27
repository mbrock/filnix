# Many attributes share one failing thunk. `nix eval --json` with eval-cores > 1
# forces them on worker threads; every forcing rethrows the *same* exception
# object and the catch sites (forceInt's errorCtx, primop call traces) prepend
# traces to it concurrently, while the main thread prints it.
{ n ? 5000 }:
let
  bad = builtins.throw "shared failure";
in
builtins.listToAttrs (builtins.genList (i: {
  name = "a${toString i}";
  value = { x = builtins.add bad i; y = builtins.sub i bad; };
}) n)
