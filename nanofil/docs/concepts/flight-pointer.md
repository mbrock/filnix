# flight pointer / pointer in flight / intval / pointer at rest / rest pointer

**Fil-C** · [InvisiCaps, flight pointers](https://fil-c.org/invisicaps#flightptr), [GIMSO, pointers at rest](https://fil-c.org/gimso), [filc_runtime.h](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.h)

A flight pointer is a pointer held in a variable or register rather than in memory. It has two words: its intval, the address the C program sees, prints and computes with, which nothing trusts; and its [[lower]], the [[capability]], which only an allocation creates and the program can neither see nor forge. Stored to memory it becomes a pointer at rest: the intval goes in the object's bytes and the lower in the object's [[aux]] allocation, where no capability reaches. That invisibility gives InvisiCaps their name, and it keeps `sizeof(void*)` at 8.

- Every access pairs an untrusted intval with a trusted lower; the check asks whether the intval's bytes lie inside the lower's object.
- Converting an integer to a pointer gives a null lower, unless [[launder|laundering]] traces the integer to the one pointer it came from. Storing an integer over a pointer at rest changes its intval and keeps its lower, so a load then yields a pointer that may trap but is never forged.
- In nanofil a word of [[class]] `p` is a flight pointer: `ptr(Addr, Cap)` in interp.pl, [ptr] in Values.v, whose Cap abstracts the lower to an [[identity]]. The [[flight]] instruction builds one from an intval and a lower that come from different names (`pizlonate:flight_inst/2`).

Fil-C's source calls the intval `ptr`: a `filc_ptr` is the pair `ptr`, `lower`.
