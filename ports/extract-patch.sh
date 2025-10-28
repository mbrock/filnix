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

# Skip glibc projects - these are built directly from fil-c source tree
case "$PROJECT" in
    yolo-glibc-*|user-glibc-*|yolomusl|usermusl)
        echo "$PROJECT: Skipping (glibc project, built from fil-c source)"
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
    ":(exclude)*/m4/libtool.m4"
    ":(exclude)*/m4/ltoptions.m4"
    ":(exclude)*/m4/ltsugar.m4"
    ":(exclude)*/m4/ltversion.m4"
    ":(exclude)*/m4/lt~obsolete.m4"
    ":(exclude)*/m4/gettext.m4"
    ":(exclude)*/m4/host-cpu-c-abi.m4"
    ":(exclude)*/m4/iconv.m4"
    ":(exclude)*/m4/intlmacosx.m4"
    ":(exclude)*/m4/lib-ld.m4"
    ":(exclude)*/m4/lib-link.m4"
    ":(exclude)*/m4/lib-prefix.m4"
    ":(exclude)*/m4/nls.m4"
    ":(exclude)*/m4/po.m4"
    ":(exclude)*/m4/progtest.m4"
    ":(exclude)*/po/Makefile.in.in"
    ":(exclude)*/po/Makevars.template"
    ":(exclude)*/po/Rules-quot"
    ":(exclude)*/po/boldquot.sed"
    ":(exclude)*/po/en@boldquot.header"
    ":(exclude)*/po/en@quot.header"
    ":(exclude)*/po/insert-header.sin"
    ":(exclude)*/po/quot.sed"
    ":(exclude)*/po/remove-potcdate.sin"
    ":(exclude)*/ABOUT-NLS"
    ":(exclude)*/config.rpath"
    # Repository infrastructure
    ":(exclude)*/.github/*"
    ":(exclude)*/.git/*"
    ":(exclude)*/.gitignore"
    ":(exclude)*/.gitattributes"
    ":(exclude)*/.gitlab-ci.yml"
    ":(exclude)*/.travis.yml"
    ":(exclude)*/.circleci/*"
    ":(exclude)*/appveyor.yml"
    ":(exclude)*/.editorconfig"
    ":(exclude)*/flist"
    # Fil-C test files (added by Filip, not needed for building)
    ":(exclude)*/fil-tests/*"
)

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
