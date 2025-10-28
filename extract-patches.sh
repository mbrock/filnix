#!/usr/bin/env bash
#
# Extract Fil-C patches for each project in the monorepo
# This creates .patch files that can be applied to upstream sources
#

set -e

REPO_DIR="${1:-$HOME/fil-c-projects}"
OUTPUT_DIR="${2:-./patches}"

if [[ ! -d "$REPO_DIR" ]]; then
    echo "Error: Repository directory $REPO_DIR does not exist"
    exit 1
fi

# Make OUTPUT_DIR absolute before changing directory
OUTPUT_DIR="$(realpath "$OUTPUT_DIR")"
mkdir -p "$OUTPUT_DIR"

cd "$REPO_DIR"

echo "Extracting patches from $REPO_DIR to $OUTPUT_DIR"
echo ""

# Find all project directories
for project_dir in projects/*/; do
    project=$(basename "$project_dir")

    # Get commit history for this project
    commits=$(git log --oneline --all "$project_dir" 2>/dev/null || true)

    if [[ -z "$commits" ]]; then
        echo "Skipping $project (no git history)"
        continue
    fi

    # Get first and last commit that touched this directory
    first_commit=$(git log --oneline --all --reverse "$project_dir" | head -1 | awk '{print $1}')
    last_commit=$(git log --oneline --all "$project_dir" | head -1 | awk '{print $1}')

    if [[ -z "$first_commit" ]] || [[ -z "$last_commit" ]]; then
        echo "Skipping $project (couldn't find commits)"
        continue
    fi

    # If first and last are the same, no changes were made
    if [[ "$first_commit" == "$last_commit" ]]; then
        echo "Skipping $project (no changes after initial import)"
        continue
    fi

    # Generate patch between initial and fil-c commit
    patch_file="$OUTPUT_DIR/${project}.patch"

    echo "Generating patch for $project..."
    echo "  First commit: $first_commit"
    echo "  Last commit:  $last_commit"

    # Generate the patch, removing the projects/$project/ path prefix
    git diff "$first_commit" "$last_commit" -- "$project_dir" | \
        sed "s|a/projects/$project/|a/|g" | \
        sed "s|b/projects/$project/|b/|g" > "$patch_file"

    # Check if patch is empty
    if [[ ! -s "$patch_file" ]]; then
        echo "  -> No changes (empty patch), removing"
        rm "$patch_file"
    else
        lines=$(wc -l < "$patch_file")
        echo "  -> Patch saved: $patch_file ($lines lines)"
    fi
    echo ""
done

echo "Done! Patches saved to $OUTPUT_DIR"
echo ""
echo "Patches with changes:"
ls -lh "$OUTPUT_DIR"/*.patch 2>/dev/null || echo "  (none)"
