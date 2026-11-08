# region / object

**Fil-C** · [InvisiCaps](https://fil-c.org/invisicaps), [filc_runtime.h](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.h)

An object is one allocation a [[capability]] can name, its bytes what upstream calls the payload: a heap object, a named local, a data item or a variadic argument snapshot. A region is the model's record of it, `region(Base, End, Kind, Life)`: its bounds `[Base, End)`, its kind (stack, heap or global data) and whether it is live or freed.

- interp.pl keeps the regions in `mem(Bytes, Regions, Next, Aux)`; Memory.v has [region] with [kind] and [life], listed in [mem]'s [m_regions]. Next is not part of the model's memory: the [[runtime]] keeps it.
- Only an ending changes a region: End becomes Base and Life becomes freed. Free does this to a live heap object ([lifetime_step]); the end of an invocation does it to its locals ([region_step]). Bytes and stored capabilities stay where they were.
- An object is what [object_region] (`interp:object_region/3`) finds for a base: the first region with that base. A later region of the same [[identity]] is no object, and the proofs ([fresh], [persists], [objects_fit]) speak of objects only this way.

The subtlety: a live zero-sized object also has End = Base, so empty bounds do not mean freed. Only the converse holds, freed implies empty ([freed_empty]), and [freed_bounds] asks it of every [[ready]] memory.

Defined in [Memory.v](../../rocq/theories/Memory.v) and interp.pl's Memory section.
