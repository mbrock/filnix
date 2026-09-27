let
  bad = throw "boom";
  first = builtins.tryEval (builtins.add bad 1);
in
builtins.seq first (builtins.sub bad 2)
