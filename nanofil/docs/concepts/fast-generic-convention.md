# fast and generic conventions / fast convention / generic convention / fast entry / generic entry / optimized calling convention / CC buffer

**Fil-C** · [optimized calling convention](https://fil-c.org/calling_convention), [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp)

Fil-C's two ways into a function, from its optimized calling convention: the fast entry takes the arguments in registers, for a caller that agrees on the signature; the generic entry takes them in the thread's CC buffers, one for bytes and one for lowers, for any caller. A function object holds both entries and a 64-bit signature, an arithmetic encoding of its type that is 0 when only the generic entry exists.

In nanofil's backend a call through a pointer compares the signature word at lower+16 with its own and takes the fast entry if they match; otherwise it marshals the arguments into thread+128 (data) and thread+384 (lowers) and calls the generic entry, which checks the size (`argument_size`, `return_size` [[trap|traps]]). Functions with over 16 words of arguments and variadic functions are generic-only (`filc_abi:signature/3`, `filc_amd64:fast_call//4`, `filc_amd64:generic_entry//2`).

Rocq models the generic entry's argument and result conversions for a call through a pointer: [indirect_call_conv] and [generic_word].
