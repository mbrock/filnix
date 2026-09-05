# Regenerate patches from the pinned upstream tree (never the worktree).
REPO_DIR ?= $(HOME)/fil-c
OUTPUT_DIR ?= patch
REV ?= $(shell python3 -c 'import json; print(json.load(open("upstream.json"))["portsRev"])')

PROJECTS = $(shell git -C "$(REPO_DIR)" ls-tree -d --name-only "$(REV):projects")
PROJENY_PROJECTS = $(shell git -C "$(REPO_DIR)" ls-tree --name-only "$(REV):projects" | sed -n '/\.projeny$$/p')
PATCHES = $(addprefix $(OUTPUT_DIR)/,$(addsuffix .patch,$(PROJECTS)))

.PHONY: all clean list test FORCE $(PROJENY_PROJECTS)
all: $(PATCHES) $(PROJENY_PROJECTS)

# Always regenerate requested patches, including ones that already exist.
$(OUTPUT_DIR)/%.patch: FORCE
	@./extract-patch.sh "$*" "$(REPO_DIR)" "$(OUTPUT_DIR)" "$(REV)"

$(PROJENY_PROJECTS):
	@./extract-patch.sh "$@" "$(REPO_DIR)" "$(OUTPUT_DIR)" "$(REV)"

FORCE:

clean:
	rm -rf "$(OUTPUT_DIR)"

list:
	@printf '%s\n' $(PROJECTS) $(PROJENY_PROJECTS)

test:
	@python3 ../tests/upstream-sources.py
