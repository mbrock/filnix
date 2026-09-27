# Force one failing thunk from many threads (builtins.parallel + tryEval),
# then report it once more. The final error's trace shows every frame that
# any thread ever prepended to the one shared exception object.
{
  n ? 2000,
}:
let
  bad = builtins.throw "shared failure";
  xs = builtins.genList (i: builtins.tryEval (builtins.add bad i)) n;
  failures = builtins.length (builtins.filter (r: !r.success) xs);
in
builtins.parallel xs (builtins.seq failures (builtins.sub 0 bad))
