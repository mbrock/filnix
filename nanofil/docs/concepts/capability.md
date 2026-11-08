# capability / cap / InvisiCaps

**Fil-C** · [InvisiCaps](https://fil-c.org/invisicaps.html), [filc_runtime.h](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.h)

A capability is the authority half of a Fil-C pointer: which object, if any, its address may be used to access. In the model a capability is an identity, never bounds; the object's current bounds live in its [[region]], so freeing through one alias empties what every alias sees.

| interp.pl | Values.v | Names |
|---|---|---|
| `none` | [CNone] | no object: a null or forged pointer |
| `obj(Base)` | [Obj] | a writable object |
| `ro(Base)` | [Ro] | a read-only object |
| `fn(F)` | [Fn] | a function of the module |
| `ext(N)` | [External] | a symbol defined outside the module |

Upstream names the same three kinds: the null capability (`none`), plain capabilities with bounds (`obj` and `ro`, read-only being a flag of the object), and special ones such as a function's, whose upper bound equals its lower so that no data access passes.

A pointer pairs it with an address: a [[flight-pointer|flight pointer]], `ptr(Addr, Cap)` in interp.pl, [ptr] in Values.v. Natively the capability is the [[lower]]; the model abstracts that to the base, the object's [[identity]], never recovered from address bits. A [[flight]] takes its capability from a named donor, independently of its address.

The access check (`interp:cap_access_res/7`, [cap_access_res]) tests null, bounds, read-only, then alignment. A function's capability has zero size, so every access through it is out of bounds; an external symbol's is stuck.

Defined in [Values.v](../../rocq/theories/Values.v) and interp.pl's header; see [guide.md, Address is not authority](../guide.md#address-is-not-authority).
