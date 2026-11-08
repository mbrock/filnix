# context

An explanatory item of a module: `context(Fn, Records)` holds binding, typed-origin, value, alias and site records that say where Fn's IR came from (provenance.pl). Nothing runs it; only provenance's own check reads it (`provenance:valid_contexts/1`).

The Rocq model does not transcribe context items: `interp:run/5` never reads them, and the module the gates compare has none. See also [[origin]].
