# Build the Gallina backend (docs/gallina-backend.md).
#   make            compile, extract, link ./nanofil-backend
#   make clean
# Needs rocq, the Rocq stdlib, ocamlfind and zarith (nix/backend.nix).
#
# The backend imports the model's definitions (../theories). Only the
# model files it imports are compiled, each with its own imports, so a
# build does not wait for the model's proofs; a model file that is
# already compiled is not compiled again. Each file's time is printed.
FLAGS = -R ../theories Nanofil -R . Backend
SOURCES = $(shell grep '\.v$$' _RocqProject)

all: nanofil-backend

# No Admitted and no axioms, in any backend file.
words:
	@if grep -nwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' $(SOURCES); then \
	  echo "backend: no Admitted and no axioms" >&2; exit 1; fi

# What each file imports, the model's files included. rocq dep warns
# about the libraries of model files the backend does not import.
MODEL = $(shell find ../theories -name '*.v' | sort)

.deps: _RocqProject $(SOURCES) $(MODEL)
	rocq dep $(FLAGS) $(MODEL) $(SOURCES) >$@ 2>/dev/null

%.vo: %.v
	@start=$$(date +%s%N); rocq compile $(FLAGS) $< && \
	ms=$$((($$(date +%s%N) - start) / 1000000)) && \
	printf '@@nanofil-backend %4d.%01ds %5d lines %s\n' \
	  $$((ms / 1000)) $$((ms % 1000 / 100)) "$$(wc -l <$<)" $<

# Compiling Extract.v extracts; the driver is linked against it.
nanofil-backend: words Extract.vo extraction/main.ml
	cd extraction && ocamlfind ocamlopt -w -a -package zarith -linkpkg \
	  nanofil_backend.mli nanofil_backend.ml main.ml -o ../nanofil-backend

clean:
	rm -f .deps *.vo *.vok *.vos *.glob .*.aux nanofil-backend
	rm -f extraction/nanofil_backend.ml extraction/nanofil_backend.mli extraction/*.cm* extraction/*.o

.PHONY: all words clean

-include .deps
