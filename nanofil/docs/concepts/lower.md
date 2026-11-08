# lower / upper / object header

**Fil-C** · [InvisiCaps, flight pointers](https://fil-c.org/invisicaps#flightptr), [filc_runtime.h](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.h)

The lower is how Fil-C represents a [[capability]] natively: the address of the first byte of the object a pointer may access, kept beside the pointer's intval in a [[flight-pointer|flight pointer]]. The object header sits just below it: the upper bound at lower−16 and the aux word at lower−8, whose low 48 bits point at the [[aux]] allocation and whose top 16 bits hold the object's flags (free, read-only, global, ...). A null lower accesses nothing, and free sets upper to lower, so every access through any lower of a freed object fails. `filc_abi:lower_function/5` keeps each live one in a [[root]].

The model abstracts the lower to an [[identity]]: `obj(Base)` in interp.pl, [Obj] in Values.v, whose current bounds are in its [[region]], not in a header. A [[flight]]'s `lower(P)` names its donor, and a [[lower-chain|lower chain]] follows donors.
