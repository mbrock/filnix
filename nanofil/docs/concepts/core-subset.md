# core subset / IOutside

**nanofil**

The core subset is the part of checked filc-mode IR that the Rocq model runs and validates: the integer, pointer and proof classes, floats, `check` and every reuse form, the raw accesses, `flight`, poll edges, direct calls, `check_function` with `raw_call`, `free`, named locals, `touch`, variadics and `setjmp`, which is validated as ir.pl does while its step is stuck, as the interpreter refuses it. A function that uses anything else decodes to IOutside.

- Left out: vectors, `store`, `cas` and atomics, `asm_fixed`, and plain mode.
- Transport.v's decoder makes such a function [IOutside] in Syntax.v, and Semantics.v's [fn_def] [Outside]. It keeps its address, its `fn` capability and its term, so the validator can read its signature and calls to it and pointers to it behave as the interpreter's do; running it is [Stuck], and the gates report the run `outside`. [valid] answers `None` for a module with such a function.

The subtlety: formal.md's "In scope" paragraph still lists floats and `va_arg` as deferred; both are now in the subset, as rocq.md's "Covered" paragraph says.

See [rocq.md, What exists](../rocq.md#what-exists).
