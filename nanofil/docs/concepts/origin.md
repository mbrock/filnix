# origin

**Fil-C** · [safepoints, Pizderson frames](https://fil-c.org/safepoints#pizderson), [filc_runtime.h](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.h)

An origin is a static record the runtime reads to name a function and source location in a trap or backtrace (`filc_amd64:function_origins//3`). In [[context]] records the word means something else: a typed source node (provenance.pl).

Neither has a counterpart in the formal model, which compares [[trap]] reasons, not their reports.
