# Initial Fil-C discovery inputs

The initial inventory selects **13,772 top-level package attributes** from
Nixpkgs revision `400439b089773d3fc593b512250e283a33485de4` for later Filnix
build attempts. The goal is to discover useful working software. The selection
is permissive; uncertain C/C++ and mixed builds are included.

[inputs.json](inputs.json) is the explicit input snapshot, with the Nixpkgs pin,
policy and observation hashes, counts, and exact attribute paths. It is generated
by [the inventory tool](../../scripts/package-inventory.py). The selection rules,
scope, and commands are documented in [package-inventory.md](../../docs/package-inventory.md).

| Decision | Attributes |
| --- | ---: |
| Candidate, selected | 10,842 |
| Uncertain, selected | 2,930 |
| Excluded | 7,376 |
| Deferred | 1,938 |
| Unresolved evaluation | 3 |
| Total top-level attributes inspected | 23,089 |

The selected set has **443 entries with assembly clues** and **3,202 whose
native recipes enable checks or install checks**. Assembly mentions, including
flags that disable assembly, never exclude an entry. Ruby is retained as
uncertain because its native recipe declares Rust dependencies for YJIT.

These are attribute counts. Deprecated aliases were disabled, but other aliases
and variants remain. Nested package collections were not recursively enumerated.
The three unresolved attributes are `AAAAAASomeThingsFailToEvaluate`, `gnufilc0`,
and `pkgsx86_64Darwin`.

No package builds or tests have been attempted. Check flags describe native
Nixpkgs recipes; Filnix evaluation and test execution remain future work.

The full local report and raw observations are in
`results/package-inventory-initial/`, which is ignored by Git. That directory
contains every inclusion/exclusion reason, packaging-file evidence, the complete
attribute universe, evaluator diagnostics, and collection provenance.

To collect another inventory into a new output directory:

```sh
python3 scripts/package-inventory.py --output results/package-inventory-next
```

Review its report before replacing this snapshot. The saved attribute paths are
arrays: a dot inside an attribute name is literal, not a nested package lookup.
