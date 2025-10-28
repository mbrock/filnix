#!/bin/bash

REPO_DIR="${1:-$HOME/fil-c-projects}"
OUTPUT_FILE="info/commits.md"
TEMP_DIR=$(mktemp -d)

echo "Using temp dir: $TEMP_DIR"

cd "$REPO_DIR/projects" || exit 1

# Function to process a single project
process_project() {
    local project="$1"
    local temp_dir="$2"
    local output="$temp_dir/$project.md"
    
    echo "## $project" > "$output"
    echo "" >> "$output"
    
    cd "$REPO_DIR/projects/$project" || return
    
    if git rev-parse --git-dir > /dev/null 2>&1; then
        git log --oneline --all >> "$output"
    else
        echo "No git repository found." >> "$output"
    fi
    
    echo "" >> "$output"
}

export -f process_project
export REPO_DIR

# Process all projects in parallel
find . -maxdepth 1 -type d ! -name '.' | sed 's|^\./||' | \
    xargs -P 8 -I {} bash -c 'process_project "$1" "$2"' _ {} "$TEMP_DIR"

# Concatenate results
cd "$OLDPWD" || exit 1
echo "# Fil-C Project Commit Logs" > "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"
echo "Commit history for all ported projects from $REPO_DIR/projects/" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Sort and concatenate all temp files
for file in $(ls "$TEMP_DIR"/*.md 2>/dev/null | sort); do
    cat "$file" >> "$OUTPUT_FILE"
done

rm -rf "$TEMP_DIR"
echo "Done! Commits written to $OUTPUT_FILE"
