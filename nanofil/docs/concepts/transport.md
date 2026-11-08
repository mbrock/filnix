# transport / decode / encode

Transport is the crossing between Prolog terms and the model: decoding a checked module that nanofil printed into Syntax.v's syntax, and encoding the model's [[outcome]] back as the term `interp:run/5` would give, so that the two can be compared with `==`.

- `main:outcomes/3` (`nanofil outcomes FILE`) prints the module and each run line. Transport.v decodes with [decode_module] and its helpers ([dinst], [dfunc], ...) and encodes with [eoutcome], [ereason], [eword] and [ecap].
- Both sides are Term.v's [term]: an integer, an atom, a compound or a proper list, as ground Prolog terms are.
- Decoding is partial on purpose: a function outside the [[core-subset|core subset]] becomes [IOutside], a data item the interpreter does not lay out [ItemOther], an unknown linkage [LOther], each keeping its term.

[judge] and [judge_valid] are built on it; see [[extraction]].

Defined in [Transport.v](../../rocq/theories/Transport.v).
