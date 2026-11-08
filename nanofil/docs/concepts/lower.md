# lower

The lower is how Fil-C represents a [[capability]] natively: the address of the first byte of the object a pointer may access, kept beside the pointer's address. The object's header sits below it: the upper bound at lower−16 and the [[aux]] pointer at lower−8, with the object's flags in its top 16 bits. `filc_abi:lower_function/5` keeps each live one in a [[root]].

The model abstracts the lower to an [[identity]]: `obj(Base)` in interp.pl, [Obj] in Values.v, whose current bounds are in its [[region]], not in a header. A [[flight]]'s `lower(P)` names its donor, and a [[lower-chain|lower chain]] follows donors.
