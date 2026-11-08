# GIMSO / garbage in, memory safety out

**Fil-C** · [GIMSO](https://fil-c.org/gimso), [compiler](https://fil-c.org/compiler), [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp)

GIMSO, garbage in, memory safety out, is Fil-C's promise. Fil-C's LLVM pass, FilPizlonator, gives every module a memory-safe meaning, however buggy or adversarial its code. Each operation does what C means or ends in a Fil-C [[trap|panic]], and no access touches bytes its [[capability]] does not cover. It does not promise that a program never panics, nor does it remove bugs that stay inside memory safety, such as integer overflow or wrong logic.

- nanofil states the same promise in two halves. [[pizlonate|Pizlonating]] makes every check explicit, and the [[validator]] accepts only checked IR whose every access is covered. [[soundness|Soundness]] then proves that an accepted module never makes an access unchecked (`pizlonate:pizlonate_module/2`, [valid_no_unchecked]).
- GIMSO's document describes pointers at rest as if their capabilities lived in a shadow address space. Fil-C implements that space with the [[aux]] allocation.
