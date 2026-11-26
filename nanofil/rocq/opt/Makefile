# Build the Gallina middle-end optimizer modules (Opt.*).
FLAGS = -R ../theories Nanofil -R ../backend Backend -R . Opt
SOURCES = $(shell grep '\.v$$' _RocqProject)
MODEL = $(shell find ../theories -name '*.v' | sort)
BACKEND = $(shell awk '/\.v$$/' ../backend/_RocqProject | sed 's|^|../backend/|')

all: words $(SOURCES:.v=.vo)

words:
	@if grep -nwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' $(SOURCES); then \
	  echo "opt: no Admitted and no axioms" >&2; exit 1; fi

.deps: _RocqProject $(SOURCES) $(MODEL) $(BACKEND)
	rocq dep $(FLAGS) $(MODEL) $(BACKEND) $(SOURCES) >$@ 2>/dev/null

%.vo: %.v
	rocq compile $(FLAGS) $<

clean:
	rm -f .deps *.vo *.vok *.vos *.glob .*.aux

.PHONY: all words clean

-include .deps
