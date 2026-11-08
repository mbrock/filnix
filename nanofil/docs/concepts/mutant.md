# mutant / mutation campaign

**nanofil**

A mutant is a checked module with one item changed, inserted or deleted: a check deleted or moved, its bounds, rights or alignment changed, a raw access's offset moved by one, a free inserted between evidence and its use, a reuse form given another proof, a poll edge removed, or a data object's or alias's linkage, target or name changed. Prolog's and Rocq's [[validator|validators]] judge each, and must agree.

- `rocq/mutants.pl` prints up to 150 mutants per item; [judge_valid] applies each change, computes [valid_items] of the whole module and compares it with `ir:valid_module/1`'s verdict; `rocq/valid.sh` runs it.
- The mutation campaign is the full matrix, `checks.x86_64-linux.nanofil-rocq-full`, run only when asked. The routine check sets `NANOFIL_MUTANTS=0` and compares base verdicts only.
- Mutants test rejection as well as acceptance; eight bugs planted in Validate.v were each caught.

The subtlety: a mutant is `outside`, not judged, when it is itself outside the [[core-subset|core subset]], or changes a signature, data or alias that an outside function refers to.

See [rocq.md, The validator and its gate](../rocq.md#the-validator-and-its-gate).
