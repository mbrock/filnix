#!/usr/bin/env bash
#
# Extract Fil-C patch for a single project
# Usage: extract-patch.sh PROJECT_NAME [REPO_DIR] [OUTPUT_DIR] [REV]
#

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "$0")" && pwd)"
PROJECT="${1:-}"
REPO_DIR="${2:-$HOME/fil-c}"
OUTPUT_DIR="${3:-$SCRIPT_DIR/patch}"
REV="${4:-$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["portsRev"])' "$SCRIPT_DIR/upstream.json")}"

if [[ -z "$PROJECT" || "$PROJECT" == */* || "$PROJECT" == .* ]]; then
    echo "Usage: $0 PROJECT_NAME [REPO_DIR] [OUTPUT_DIR] [REV]" >&2
    exit 1
fi

# Skip glibc projects and projects with no actual code changes
case "$PROJECT" in
    yolo-glibc-*|user-glibc-*|yolomusl|usermusl)
        echo "$PROJECT: Skipping (glibc project, built from fil-c source)"
        exit 0
        ;;
    tcl-*)
        echo "$PROJECT: Skipping (no Fil-C code changes, only build artifacts)"
        exit 0
        ;;
esac

if [[ ! -d "$REPO_DIR" ]]; then
    echo "Error: Repository directory $REPO_DIR does not exist"
    exit 1
fi

# Make paths absolute before changing directory
REPO_DIR="$(realpath "$REPO_DIR")"
OUTPUT_DIR="$(realpath -m "$OUTPUT_DIR")"
mkdir -p "$OUTPUT_DIR"

cd "$REPO_DIR"

project_dir="projects/$PROJECT/"

# Resolve once: neither another branch nor an uncommitted file may affect a patch.
last_commit=$(git rev-parse --verify "$REV^{commit}")
if [[ "$(git cat-file -t "$last_commit:${project_dir%/}" 2>/dev/null || true)" != tree ]]; then
    echo "Error: Project $PROJECT not found at $last_commit" >&2
    exit 1
fi

# The original import is the unmodified upstream release. Restrict history to
# ancestors of the chosen ports revision; diff against that revision's tree.
mapfile -t commits < <(git log --format=%H --reverse "$last_commit" -- "$project_dir")
first_commit="${commits[0]:?No project history}"
echo "$PROJECT: extracting $first_commit..$last_commit"

# Publish only a complete patch, leaving an existing patch intact on failure.
patch_file="$OUTPUT_DIR/${PROJECT}.patch"
patch_tmp=$(mktemp "$OUTPUT_DIR/.${PROJECT}.XXXXXX")
trap 'rm -f "$patch_tmp"' EXIT

# List of autotools-generated files and repo infrastructure to exclude
exclude_patterns=(
    # Autotools generated files
    ":(exclude)*/configure"
    ":(exclude)*/config.h.in"
    ":(exclude)*/Makefile.in"
    ":(exclude)*/aclocal.m4"
    ":(exclude)*/build-aux/*"
    ":(exclude)*/conftools/*"
    # Exclude entire m4/ and po/ directories (autotools/gettext generated)
    ":(exclude)*/m4/*"
    ":(exclude)*/po/*"
    ":(exclude)*/ABOUT-NLS"
    ":(exclude)*/config.rpath"
    # Autotools helper scripts
    ":(exclude)*/INSTALL"
    ":(exclude)*/install-sh"
    ":(exclude)*/missing"
    ":(exclude)*/compile"
    ":(exclude)*/depcomp"
    ":(exclude)*/test-driver"
    ":(exclude)*/ar-lib"
    ":(exclude)*/ltmain.sh"
    ":(exclude)*/config.guess"
    ":(exclude)*/config.sub"
    ":(exclude)*/config.status.lineno"
    ":(exclude)*/aux/*"
    ":(exclude)*/etc/compile"
    ":(exclude)*/etc/config.guess"
    ":(exclude)*/etc/config.sub"
    ":(exclude)*/etc/depcomp"
    ":(exclude)*/etc/install-sh"
    ":(exclude)*/etc/missing"
    ":(exclude)*/etc/ylwrap"
    # Repository infrastructure
    ":(exclude)*/.github/*"
    ":(exclude)*/.gitlab-ci/*"
    ":(exclude)*/.gitlab-ci.yml"
    ":(exclude)*/.git/*"
    ":(exclude)*/.gitignore"
    ":(exclude)*/.gitattributes"
    ":(exclude)*/.travis.yml"
    ":(exclude)*/.circleci/*"
    ":(exclude)*/appveyor.yml"
    ":(exclude)*/.editorconfig"
    ":(exclude)*/.codedocs"
    ":(exclude)*/flist"
    # Vendored dependencies (common cases)
    ":(exclude)*/compat/zlib/*"
    # Prebuilt binaries
    ":(exclude)*/*.dll"
    ":(exclude)*/*.exe"
    ":(exclude)*/*.lib"
    ":(exclude)*/*.a"
    ":(exclude)*/*.so"
    ":(exclude)*/*.dylib"
    ":(exclude)*/win32/*"
    ":(exclude)*/win64/*"
    ":(exclude)*/win64-arm/*"
    # Generated documentation
    ":(exclude)*/doc/*.1"
    ":(exclude)*/doc/*.info"
    ":(exclude)*/*.svg"
    ":(exclude)*/Doc/help/.cvsignore"
    ":(exclude)*/Doc/help/.distfiles"
    # Fil-C test files (added by Filip, not needed for building)
    ":(exclude)*/fil-tests/*"
    # Toybox kconfig system (GPL'd build infrastructure, doesn't go in binary)
    ":(exclude)*/kconfig/*"
    ":(exclude)*/good-config"
    # TCL test library and Windows/tool artifacts
    ":(exclude)*/library/tcltest/*"
)

# Filnix's compiler handles version-script ABI translation, and gettext also
# uses this list for C namespace hiding. Omit upstream's prefix-only rewrite;
# preserve any other changes to the list so they can be reviewed on updates.
# See docs/toolchain-symbols.md in the Filnix repository.
case "$PROJECT" in
    gettext-*)
        symbol_list="${project_dir}libtextstyle/lib/libtextstyle.sym.in"
        if git cat-file -e "$first_commit:$symbol_list" 2>/dev/null && \
           git cat-file -e "$last_commit:$symbol_list" 2>/dev/null && \
           cmp -s <(git show "$first_commit:$symbol_list") \
                  <(git show "$last_commit:$symbol_list" | sed 's/^pizlonated_//'); then
            exclude_patterns+=(":(exclude)$symbol_list")
        fi
        ;;
esac

# Dynamically exclude yacc/bison/flex generated files
# Find .y files and exclude their generated .c/.h counterparts
while IFS= read -r -d '' yfile; do
    dir=$(dirname "$yfile")
    base=$(basename "$yfile" .y)
    # Common generated file patterns from yacc/bison
    exclude_patterns+=(":(exclude)$dir/$base.c")
    exclude_patterns+=(":(exclude)$dir/$base.h")
    exclude_patterns+=(":(exclude)$dir/$base.tab.c")
    exclude_patterns+=(":(exclude)$dir/$base.tab.h")
    exclude_patterns+=(":(exclude)$dir/y.tab.c")
    exclude_patterns+=(":(exclude)$dir/y.tab.h")
done < <(git ls-tree -r -z --name-only "$last_commit" -- "$project_dir" | while IFS= read -r -d '' path; do
    [[ "$path" != *.y ]] || printf '%s\0' "$path"
done)

# Find .l files and exclude their generated .c counterparts
while IFS= read -r -d '' lfile; do
    dir=$(dirname "$lfile")
    base=$(basename "$lfile" .l)
    # Common generated file patterns from lex/flex
    exclude_patterns+=(":(exclude)$dir/$base.c")
    exclude_patterns+=(":(exclude)$dir/lex.$base.c")
    exclude_patterns+=(":(exclude)$dir/lex.yy.c")
done < <(git ls-tree -r -z --name-only "$last_commit" -- "$project_dir" | while IFS= read -r -d '' path; do
    [[ "$path" != *.l ]] || printf '%s\0' "$path"
done)

# Generate the patch, removing the projects/$PROJECT/ path prefix and excluding generated files
git diff --no-ext-diff --no-textconv --no-renames --src-prefix=a/ --dst-prefix=b/ "$first_commit" "$last_commit" -- "$project_dir" "${exclude_patterns[@]}" | \
    sed "s|a/projects/$PROJECT/|a/|g" | \
    sed "s|b/projects/$PROJECT/|b/|g" > "$patch_tmp"

# Check if patch is empty
if [[ ! -s "$patch_tmp" ]]; then
    echo "$PROJECT: No changes (empty patch)"
    rm -f "$patch_file"
    exit 0
fi

chmod 644 "$patch_tmp"
mv "$patch_tmp" "$patch_file"
lines=$(wc -l < "$patch_file")
echo "$PROJECT: Generated patch ($lines lines)"
