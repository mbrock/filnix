# fast and generic conventions / fast convention / generic convention / fast entry / generic entry

Fil-C's two ways into a function: the fast entry takes the arguments in registers, for a caller that agrees on the signature; the generic entry takes them as a buffer in the thread, for any caller.

A call through a pointer compares the signature word at lower+16 with its own and takes the fast entry if they match; otherwise it marshals the arguments into thread+128 (data) and thread+384 (lowers) and calls the generic entry, which checks the size (`argument_size`, `return_size` [[trap|traps]]). Functions with over 16 words of arguments and variadic functions are generic-only (`filc_abi:signature/3`, `filc_amd64:fast_call//4`, `filc_amd64:generic_entry//2`).

Rocq models the generic entry's argument and result conversions for a call through a pointer: [indirect_call_conv] and [generic_word].
