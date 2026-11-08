# unchecked / unchecked(Why)

`unchecked(Why)` is the outcome of a [[raw-access|raw access]] its capability does not allow, or of a [[reuse]] form whose trust was false: a check was missing or too weak, which only a broken pass produces. It is neither undefined behaviour nor a [[trap]], so it refines nothing (`interp:raw_res/2`).

- Why is an access check's reason, or `alias`, `span`, `half`, `limit` or `ahead(Why)` for the reuse forms.
- Rocq: the [[outcome]] [Unchecked] and the partial result [RUnchecked], made by [raw_res]. [[soundness|Soundness of checking]] says a valid module's run never reaches it ([valid_no_unchecked]).
