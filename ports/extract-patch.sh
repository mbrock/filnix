#!/usr/bin/env bash
#
# Extract Fil-C patch for a single project
# Usage: extract-patch.sh PROJECT_NAME REPO_DIR OUTPUT_DIR
#

set -e

PROJECT="$1"
REPO_DIR="${2:-$HOME/fil-c-projects}"
OUTPUT_DIR="${3:-./patch}"

if [[ -z "$PROJECT" ]]; then
    echo "Usage: $0 PROJECT_NAME [REPO_DIR] [OUTPUT_DIR]"
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

if [[ ! -d "$project_dir" ]]; then
    echo "Error: Project $PROJECT not found in $REPO_DIR/projects/"
    exit 1
fi

# Get commit history for this project
commits=$(git log --oneline --all "$project_dir" 2>/dev/null || true)

if [[ -z "$commits" ]]; then
    echo "$PROJECT: No git history"
    exit 0
fi

# Get first and last commit that touched this directory
first_commit=$(git log --oneline --all --reverse "$project_dir" | head -1 | awk '{print $1}')
last_commit=$(git log --oneline --all "$project_dir" | head -1 | awk '{print $1}')

if [[ -z "$first_commit" ]] || [[ -z "$last_commit" ]]; then
    echo "$PROJECT: Couldn't find commits"
    exit 0
fi

# If first and last are the same, no changes were made
if [[ "$first_commit" == "$last_commit" ]]; then
    echo "$PROJECT: No changes after initial import"
    exit 0
fi

# Generate patch between first and last commit
patch_file="$OUTPUT_DIR/${PROJECT}.patch"

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

# Dynamically exclude yacc/bison/flex generated files
# Find .y files and exclude their generated .c/.h counterparts
while IFS= read -r yfile; do
    dir=$(dirname "$yfile")
    base=$(basename "$yfile" .y)
    # Common generated file patterns from yacc/bison
    exclude_patterns+=(":(exclude)$dir/$base.c")
    exclude_patterns+=(":(exclude)$dir/$base.h")
    exclude_patterns+=(":(exclude)$dir/$base.tab.c")
    exclude_patterns+=(":(exclude)$dir/$base.tab.h")
    exclude_patterns+=(":(exclude)$dir/y.tab.c")
    exclude_patterns+=(":(exclude)$dir/y.tab.h")
done < <(find "$project_dir" -name '*.y' -type f 2>/dev/null)

# Find .l files and exclude their generated .c counterparts
while IFS= read -r lfile; do
    dir=$(dirname "$lfile")
    base=$(basename "$lfile" .l)
    # Common generated file patterns from lex/flex
    exclude_patterns+=(":(exclude)$dir/$base.c")
    exclude_patterns+=(":(exclude)$dir/lex.$base.c")
    exclude_patterns+=(":(exclude)$dir/lex.yy.c")
done < <(find "$project_dir" -name '*.l' -type f 2>/dev/null)

# Generate the patch, removing the projects/$PROJECT/ path prefix and excluding generated files
git diff "$first_commit" "$last_commit" -- "$project_dir" "${exclude_patterns[@]}" | \
    sed "s|a/projects/$PROJECT/|a/|g" | \
    sed "s|b/projects/$PROJECT/|b/|g" > "$patch_file"

# Check if patch is empty
if [[ ! -s "$patch_file" ]]; then
    echo "$PROJECT: No changes (empty patch)"
    rm "$patch_file"
    exit 0
fi

lines=$(wc -l < "$patch_file")
echo "$PROJECT: Generated patch ($lines lines)"
