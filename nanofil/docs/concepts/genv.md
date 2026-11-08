# global environment / genv

**nanofil**

The global environment is what every [[step]] of a run reads but never changes: the module, each global's pointer, and the free that a call of libc's `free` runs.

- Semantics.v's [genv]: [ge_module], [ge_globals] (each symbol's name with its address and [[capability]]), [ge_free]. Run.v's [Driver] builds it with [ge_free] the [[runtime]]'s [free]; the interpreter's is Memory.v's [free_res].
- interp.pl's counterpart is the prepared module of `interp:module_prepared/2`, its function and global indexes; its free is `interp:free_res/4`.
- [find_fn] looks a callee up in it, through aliases.

The subtlety: the theorems ask `ge_free ge = R.free` and `ge_module ge = md` explicitly, because a genv could pair a module with any free; [valid_no_unchecked] is stated for the genv a run of R would build.

Defined in [Semantics.v](../../rocq/theories/Semantics.v).
