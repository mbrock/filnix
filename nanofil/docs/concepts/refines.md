# refines

`opt:refines/2` is the outcome relation that [[translation-validation|translation validation]] of the middle end uses: the original's undefined behaviour allows anything, an unknown value allows any consistent one, and otherwise the [[outcome|outcomes]] must be equal. An optimized run may go on where the original ran out of memory, a runtime's choice; `too_big` must stay.

The Rocq model has no counterpart yet: Campaign 4 plans to restate it as trace inclusion ([formal.md, Campaign 4](../formal.md#campaign-4-observations-refinement-and-the-environment)).
