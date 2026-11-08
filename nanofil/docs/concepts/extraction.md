# extraction / judge

**nanofil**

Extraction compiles the Rocq model to OCaml so that it can be run beside the Prolog on the same inputs. `judge` is the extracted function that reads one run line nanofil printed, runs it in the model, and answers `agree`, `disagree`, `outside` or `stuck_both`.

- Extract.v and `rocq/extraction/main.ml`, a reader of Prolog terms; [judge] and [judge_valid] are in Transport.v. `rocq/agree.sh` pipes `nanofil outcomes` through `judge`; `rocq/valid.sh` pipes [[mutant]] verdicts through `judge_valid`.
- The model runs as `Driver InterpRuntime` ([Driver], [InterpRuntime]), so `Print Assumptions` of `judge` is closed: no axiom of the [[runtime]] module type is left open.
- A disagreement is presumed the model's fault; none has been found.

The subtlety: `nat` extracts to OCaml's `int` and integers to zarith's. A unary `nat` as large as a big function's fuel overflowed the stack, and a positive-keyed map walked keys bit by bit, so the model's types were chosen for the extracted code.

See [rocq.md, The full outcome gate](../rocq.md#the-full-outcome-gate) and [Extract.v](../../rocq/theories/Extract.v).
