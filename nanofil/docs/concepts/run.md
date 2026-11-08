# run

**nanofil**

A run is the execution of one function of a module from its initial memory, step after step, to an [[outcome]] or forever. The theorems quantify over every state a run reaches, not over its outcome, so a run that never ends is covered too.

- Prolog: `interp:run/5` prepares the module and runs the function under a [[fuel]] bound.
- Rocq: Run.v's [Driver] runs over any [[runtime]], from [initial_memory], by [run] and [run_steps]; Semantics.v's [reachable] and Machine.v's [mreachable] are runs as relations. ExternalMachine.v adds labelled runs through [[external-call|external calls]].
- The theorems' form: "along every run of a checked module that starts [[ready]]", as in [[soundness]]'s [valid_no_unchecked].

The subtlety: two bounds. The run's own fuel counts blocks entered and ends with `out_of_fuel`, which proves nothing; the extracted driver's gas, taken by [run_steps] in halves up to 2^60 steps, is never the limit in practice. Campaign 7 quantifies over reached states so that neither plays a part.

Defined in [Run.v](../../rocq/theories/Run.v) and [Machine.v](../../rocq/theories/Machine.v).
