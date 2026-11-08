# checked IR / unchecked IR / stage

The two stages of the IR. Unchecked IR leaves Fil-C's checks implicit in every `load` and `store` at a `p` address; checked IR states every [[check]], every [[raw-access|raw access]] and the [[proof]] it uses, so the [[validator]] can see that each access is covered. A module's stage is read off its vocabulary, never a flag (`ir:module_stage/2`).

[[pizlonate|Pizlonation]] turns unchecked IR into checked. The Rocq model covers checked filc-mode IR only: [module_checked] reads the stage, and [stage_func] is the checked part of the validator, the [[evidence-pass|evidence pass]] and its companions.
