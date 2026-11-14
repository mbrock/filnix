#!/usr/bin/env bash
# Two small cases where rocqchk and Print Assumptions disagree about lemmas
# in sealed modules. Run with rocq and rocqchk on PATH (env.sh):
#
#   bash run.sh
#
# Use.v proves q from M.l0 and A.l1, two lemmas that have proofs but sit
# in modules sealed with a signature (M : S, and the functor F (X : S) : FS X).
# Print Assumptions q says "Closed under the global context", while
# rocqchk -o lists T.Use.M.l0 and T.Use.A.l1 as axioms: the checker reads a
# sealed module's opaque fields as assumptions (Rocq 9.1.1 lists only
# T.Use.A.l1, the functor's). This is how 9.3.0 reports
# Hello's HelloGlibcWorldOn.os_wi_stable and Libs.hello_libs at Rocq 9.3.
#
# IncUse.v seals a module that includes a library defining a record. At
# Rocq 9.1.1 rocqchk stops with an anomaly ("Inductive T.IncUse.M.w does
# not appear in the environment"), as it does on Hello's closure; at 9.3.0
# it checks the file.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
cp "$here"/*.v "$work"/
cd "$work"
for f in Lib Use IncLib IncUse; do rocq c -q -R . T "$f.v"; done
echo "== rocqchk -o T.Use"
rocqchk -silent -o -R . T T.Use 2>&1 | sed -n '/Axioms/,/type-in-type/p'
echo "== rocqchk -o T.IncUse"
rocqchk -silent -o -R . T T.IncUse 2>&1 | sed -n '1,4p'
rm -rf "$work"
