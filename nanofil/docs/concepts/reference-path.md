# reference path

The reference path is nanofil without `-O`: every choice at its simplest correct translation, against which each optimization is compared (`main:registers_default/2`). For checks it is `--checks=reference`, every access with its own [[check]], and [[check_ahead]]'s contract is stated against it. See [guide.md, Plain and -O](../guide.md#plain-and--o).
