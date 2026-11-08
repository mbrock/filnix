# fuel

The interpreter's bound on executed blocks: each block entered costs one unit, and running out ends the run `out_of_fuel`, which proves nothing (`interp:run/5`).

The Rocq model counts the same way ([c_fuel], the outcome [OutOfFuel]), so both run out at the same point. The theorems quantify over every state a [[run]] reaches, so fuel plays no part in them. Not to be confused with the extracted driver's gas or with the fuel of Cfg.v's graph walks.
