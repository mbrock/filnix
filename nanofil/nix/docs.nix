# The documents' checks, apart from the compiler check (check.nix), so a
# docs or theory edit reruns only these: every predicate, module, link
# and concept reference in the documents dterm draws (packages/site's
# dtermDocs) and the concepts resolves, as does every [[concept]] in a
# Prolog or Rocq comment, and each prolog output has its terms
# (web/dterm_guide.pl), including links to any file under nanofil, so
# it reads the whole tree; and the guide's example outputs (docs/guide.md,
# README.md) are what the compiler now produces (tests/guide.sh).
{
  pkgs,
  filcc,
}:
pkgs.runCommandCC "nanofil-docs"
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
    ];
  }
  ''
    cp -r ${../.} nanofil
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs tests bin
    export FILCC=${filcc}/bin/clang
    python3 tests/watch.py --label "guide links" --warn-after 120 --timeout 600 -- \
      swipl web/dterm.pl --check docs/README.md docs/guide.md docs/formal.md docs/filc.md docs/iris.md docs/logic.md docs/nfb-guide-argon.md docs/nfb-guide-wonder.md docs/nfb-guide-wonderful.md src \
      --concepts=docs/concepts --rocq=rocq/theories --rocq=rocq/spikes --rocq=rocq/backend
    python3 tests/watch.py --label guide --warn-after 120 --timeout 600 -- tests/guide.sh --check
    touch $out
  ''
