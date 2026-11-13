From Nanofil Require Import Runtime ExternalMachine Language.
Declare Module Arbitrary : Runtime.
Module EM := ExternalMachine Arbitrary.
Module L := Language Arbitrary.
About EM.Running.
About EM.Stopped.
About EM.admissible.
About EM.step.
About EM.run.
About L.mkLstate.
About L.ls_mem.
About L.ls_rt.
About L.ls_fuel.
About L.ls_world.
