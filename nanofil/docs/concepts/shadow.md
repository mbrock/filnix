# shadow

**nanofil** · GIMSO's *shadow address space*, where pointers at rest keep their capabilities, is a third thing: the [[aux]] allocation ([GIMSO](https://fil-c.org/gimso))

A shadow is a slot that holds a copy on the side, in two unrelated places. In the backends, a [[phi]]'s shadow slot holds the incoming value during a parallel copy (it may be a [[home]]). In launder.pl, a local integer's capability shadow is a pointer slot that holds the [[capability]] of the value last stored in the integer (`launder:launder_func/4`, [[launder]]).

Neither appears in the formal model.
