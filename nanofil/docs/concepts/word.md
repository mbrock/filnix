# word

**nanofil** · a pointer word is a [[flight-pointer|flight pointer]]

A word is the value a [[temporary]] holds at run time: an integer, a pointer (an address with its [[capability]]), or a limit's opaque snapshot. The temporary's [[class]] says how it is read.

| interp.pl | Values.v | Classes |
|---|---|---|
| an integer | [WInt] | `w`, `l`; also `p` for an integer argument with no pointer term |
| `ptr(Addr, Cap)` | [WPtr] of a [ptr] | `p`, `a`, `f` |
| `limit(Cap, Size)` | [WLimit] | `l`, a [[limit]]'s snapshot |

[word] is a sum over classes: being well classed is a boolean fact about a word ([word_at_class], `interp:word_at_class/3`), not an index of its type, as formal.md decided.

The subtlety: "word" has other meanings nearby. In ir.pl's class table, `w` is "a word", a 32-bit integer, beside `l`, "a long"; in the backends a word is an 8-byte machine word, as in a frame's [[home|homes]]. And the integer at class `p` exists only for main's canonical arguments (`interp:class_arg/2`): every operation that needs a pointer is stuck on it.

Defined in [Values.v](../../rocq/theories/core/Values.v).
