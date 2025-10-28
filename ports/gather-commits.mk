# Makefile for gathering commit logs in parallel

REPO_DIR ?= $(HOME)/fil-c-projects
PROJECTS_DIR = $(REPO_DIR)/projects
OUTPUT_DIR = /tmp/filnix-commits
FINAL_OUTPUT = info/commits.org

# Find all project directories
PROJECTS := $(notdir $(wildcard $(PROJECTS_DIR)/*))
COMMIT_FILES := $(addprefix $(OUTPUT_DIR)/,$(addsuffix .org,$(PROJECTS)))

.PHONY: all clean

all: $(FINAL_OUTPUT)

$(OUTPUT_DIR):
	@mkdir -p $(OUTPUT_DIR)

# Pattern rule to extract commits for each project
$(OUTPUT_DIR)/%.org: | $(OUTPUT_DIR)
	@echo "Processing $*..."
	@python3 format-commits.py $(PROJECTS_DIR)/$* $* > $@

# Concatenate all commit files
$(FINAL_OUTPUT): $(COMMIT_FILES)
	@echo "#+TITLE: Fil-C Project Commit Logs" > $@
	@echo "#+AUTHOR: Auto-generated" >> $@
	@echo "" >> $@
	@echo "Commit history for all ported projects from fil-c repository." >> $@
	@echo "" >> $@
	@echo "* Projects" >> $@
	@echo "" >> $@
	@cat $(sort $(COMMIT_FILES)) >> $@
	@echo "Done! Commits written to $@"

clean:
	rm -rf $(OUTPUT_DIR)
	rm -f $(FINAL_OUTPUT)
