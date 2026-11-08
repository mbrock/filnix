# rights

**Fil-C** · [InvisiCaps](https://fil-c.org/invisicaps), [filc_runtime.h](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.h)

Rights are what an access asks of a [[capability]]: `read` or `write`, where write allows reading too. Every check, renew and raw access names the rights it needs.

- ir.pl: the `Rights` argument of `check(Lo, Hi, Rights, Align)` and the reuse forms; `ir:rights_allow/2`. Syntax.v: [rights], [Read] and [Write].
- A write through `ro(Base)` ([Ro]) traps `readonly`, tested after bounds and before alignment ([cap_access_res]). All exposed capabilities of one object have the same rights, so read-only is a property of the object: natively, the READONLY flag in its [[lower|header]].

The subtlety: a reuse form asks its own rights, not its source's. A [[renew]] of a read-only object for a write traps `readonly`, which `interp:renew_res/4` keeps as the program's trap; a [[renew_hull|hull]] write needs some span with write rights, since a passed write check shows the capability is not read-only.

See [rocq.md, Renew and the half check](../rocq.md#renew-and-the-half-check).
