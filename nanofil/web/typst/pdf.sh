#!/usr/bin/env bash
# A PDF of any source the wiki draws, on the fly:
#
#   pdf.sh SOURCE [-o OUT.pdf] [--profile remarkable|a5|a4] [--typ OUT.typ]
#
# SOURCE is a nanofil document (nanofil/docs/NAME.md), a Prolog module
# (nanofil/src/NAME.pl), a Rocq file (nanofil/rocq/.../NAME.v) or any Nix
# file of the repository. pdf.sh draws its page as the site build does,
# into a scratch copy of the wiki's layout, then typeset.py sets it.
# Run from the repository root, with swipl, chromium, typst, python3 and
# TYPESET_FONTS available: typeset.nix provides all of them.
set -euo pipefail

src=${1:?usage: pdf.sh SOURCE [-o OUT.pdf] [--profile P] [--typ OUT.typ]}
shift
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd "$here/../../.." && pwd)
start=$PWD
src=$(realpath --relative-to="$repo" "$src")
site=$(mktemp -d "${TMPDIR:-/tmp}/dterm-pdf.XXXXXX")
trap 'rm -rf "$site"' EXIT
mkdir -p "$site/nanofil/rocq" "$site/nix"
cp "$repo/pages/style.css" "$site/"
cp "$repo"/nanofil/web/dterm.css "$repo"/nanofil/web/dterm.js "$site/nanofil/"
cp "$repo"/nanofil/web/rocq/dterm-rocq.css "$repo"/nanofil/web/rocq/dterm-rocq.js "$site/nanofil/rocq/"
cp "$repo"/dterm-nix/dterm-nix.css "$repo"/dterm-nix/dterm-nix.js "$site/nix/"
base=$(basename "$src")

cd "$repo"
case "$src" in
  nanofil/docs/*.md | nanofil/src/*.pl)
    # dterm.pl draws every module with the documents; the index across
    # them is what resolves a document's references.
    doc=()
    if [[ $src == *.md ]]; then
      doc=(--doc="${src#nanofil/}")
      page=${base%.md}.html
      [[ $page == README.html ]] && page=index.html
    else
      page=${base%.pl}.html
    fi
    (cd nanofil && swipl web/dterm.pl "$site/nanofil" src "${doc[@]}" \
      --concepts=docs/concepts --rocq=rocq/theories --rocq=rocq/spikes \
      --rocq=rocq/backend --rocq=rocq/glibc </dev/null >&2)
    page=$site/nanofil/$page
    ;;
  nanofil/rocq/*.v)
    swipl nanofil/web/rocq/dterm_rocq.pl "$site/nanofil/rocq" . --prolog=nanofil/src \
      --concepts=nanofil/docs/concepts "$src" </dev/null >&2
    rel=${src#nanofil/}
    page=$site/nanofil/rocq/${rel//\//-}
    page=${page%.v}.html
    ;;
  *.nix)
    swipl dterm-nix/dterm_nix.pl "$site/nix" . "$src" </dev/null >&2
    page=$site/nix/${src//\//-}
    page=${page%.nix}.html
    ;;
  *)
    echo "pdf.sh: no page for $src (a nanofil document, module or Rocq file, or a Nix file)" >&2
    exit 2
    ;;
esac
[[ -f $page ]] || { echo "pdf.sh: $src drew no $page" >&2; exit 1; }

cd "$start"
out=()
[[ " $* " == *" -o "* || " $* " == *" --output "* ]] || out=(-o "$start/$(basename "${page%.html}").pdf")
python3 "$here/typeset.py" "$page" --site "$site" "${out[@]}" "$@"
