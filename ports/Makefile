# Makefile for extracting Fil-C patches in parallel

REPO_DIR ?= $(HOME)/fil-c-projects
OUTPUT_DIR ?= patch

# Discover all projects
PROJECTS := $(notdir $(wildcard $(REPO_DIR)/projects/*))

# Generate patch file targets
PATCHES := $(addprefix $(OUTPUT_DIR)/,$(addsuffix .patch,$(PROJECTS)))

.PHONY: all clean list test

all: $(PATCHES)

# Pattern rule to generate a patch for each project
$(OUTPUT_DIR)/%.patch: | $(OUTPUT_DIR)
	@./extract-patch.sh $* $(REPO_DIR) $(OUTPUT_DIR)

$(OUTPUT_DIR):
	@mkdir -p $(OUTPUT_DIR)

clean:
	rm -rf $(OUTPUT_DIR)

list:
	@echo "Projects found: $(words $(PROJECTS))"
	@echo $(PROJECTS) | tr ' ' '\n' | sort

# Test with a single project
test:
	@./extract-patch.sh perl-5.40.0 $(REPO_DIR) $(OUTPUT_DIR)
