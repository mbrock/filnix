# proof

**nanofil**

A proof is a [[temporary]] of class `a` or `f`, the result of a [[check]]: it holds the checked pointer itself and certifies that the check passed. A [[raw-access|raw access]] names the proof it relies on, so evidence is structural (`ir:proof_use/6`).

- Rocq: the classes [A] and [F] ([proof_class]); a proof's [[word]] is the pointer, a [WPtr].
- A heap proof is usable only while its [[live-fact|live fact]] holds, or through a [[reuse]] form's rule.
