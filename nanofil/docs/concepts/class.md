# class

**nanofil** · a `p` value is a [[flight-pointer|flight pointer]]

A value's machine type, one letter: `w` and `l` integers (32 and 64 bits), `s`, `d` and `x` floats, `p` a pointer with its [[capability]], and in [[stage|checked IR]] `a` (a proven address) and `f` (a proven function) (`ir:class/3`).

- Rocq: [class] in Syntax.v, with [W], [L], [P], [A], [F], [Single], [Double] and [Extended]; [word_at_class] (`interp:word_at_class/3`) says when a [[word]] is of a class.
- `a` and `f` are the [[proof]] classes: never parameters, phis, call arguments or stored values.
