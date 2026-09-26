# Fil-C discovery inputs for Nixpkgs 26.05

[inputs.json](inputs.json) selects **14,647 top-level package attributes** from
filnixpkgs `118d872d35b2ddbff87356e6dc407affe40032ad` (nixos-26.05), with the
same policy as the [first inventory](../package-inventory/README.md):

| Decision | Attributes |
| --- | ---: |
| Candidate, selected | 11,274 |
| Uncertain, selected | 3,373 |
| Excluded | 8,206 |
| Deferred | 2,161 |
| Unresolved evaluation | 3 |

Collected with `python3 scripts/package-inventory.py --output results/package-inventory-2605`.
