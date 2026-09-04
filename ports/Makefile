# Regenerate patches from the pinned upstream tree (never the worktree).
REPO_DIR ?= $(HOME)/fil-c
OUTPUT_DIR ?= patch
REV ?= $(shell python3 -c 'import json; print(json.load(open("upstream.json"))["portsRev"])')

PROJECTS = $(shell git -C "$(REPO_DIR)" ls-tree -d --name-only "$(REV):projects")
PATCHES = $(addprefix $(OUTPUT_DIR)/,$(addsuffix .patch,$(PROJECTS)))

.PHONY: all clean list test FORCE
all: $(PATCHES)

# Always regenerate requested patches, including ones that already exist.
$(OUTPUT_DIR)/%.patch: FORCE
	@./extract-patch.sh "$*" "$(REPO_DIR)" "$(OUTPUT_DIR)" "$(REV)"

FORCE:

clean:
	rm -rf "$(OUTPUT_DIR)"

list:
	@git -C "$(REPO_DIR)" ls-tree -d --name-only "$(REV):projects"

test:
	@python3 ../tests/upstream-sources.py
