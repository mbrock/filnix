# Build the Gallina C frontend and extract ./nanofil-frontend.
FLAGS = -R ../theories Nanofil -R ../backend Backend -R . Frontend
SOURCES = $(shell grep '\.v$$' _RocqProject)
MODEL = $(shell find ../theories -name '*.v' | sort)
BACKEND = $(shell awk '/\.v$$/' ../backend/_RocqProject | sed 's|^|../backend/|')

all: nanofil-frontend

words:
	@if grep -nwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' $(SOURCES); then \
	  echo "frontend: no Admitted and no axioms" >&2; exit 1; fi

.deps: _RocqProject $(SOURCES) $(MODEL) $(BACKEND)
	rocq dep $(FLAGS) $(MODEL) $(BACKEND) $(SOURCES) >$@ 2>/dev/null

%.vo: %.v
	rocq compile $(FLAGS) $<

nanofil-frontend: words Extract.vo extraction/main.ml
	cd extraction && ocamlfind ocamlopt -w -a -package zarith,unix -linkpkg \
	  nanofil_frontend.mli nanofil_frontend.ml main.ml -o ../nanofil-frontend

clean:
	rm -f .deps *.vo *.vok *.vos *.glob .*.aux nanofil-frontend
	rm -f extraction/nanofil_frontend.ml extraction/nanofil_frontend.mli extraction/*.cm* extraction/*.o

.PHONY: all words clean

-include .deps
