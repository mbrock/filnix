# pizlonate

**nanofil** · FilPizlonator, Fil-C's LLVM pass ([compiler](https://fil-c.org/compiler), [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp))

To pizlonate is to make Fil-C's checks explicit: turn [[stage|unchecked IR]] into checked IR, each access becoming a [[check]] and a [[raw-access|raw access]] that names its [[proof]], and each pointer operation a [[flight]] (after FilPizlonator, Fil-C's LLVM pass; `pizlonate:pizlonate_module/2`).

The pizlonation oracle compares the unchecked and checked runs in the [[interpreter]] (`main:pizlonation_verdict/4`). The formal model starts at pizlonation's output. See [pizlonation.md](../pizlonation.md).
