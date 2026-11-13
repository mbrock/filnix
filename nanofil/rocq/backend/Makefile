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

# The integer semantics of the emitted x86-64 (docs/gallina-backend.md),
# in the order the files import each other.
AMD64 = Amd64Word Amd64Memory Amd64Machine Amd64Step Amd64Asm Amd64Total \
  Amd64DivisionCode Amd64Division Amd64Frame Amd64Layout Amd64DivisionStep

PROOFS = RegsProof.vo NfbProof.vo NfbTotal.vo $(AMD64:=.vo)

all: nanofil-backend RegsProof.vo .regs-assumptions .amd64-assumptions

# No Admitted and no axioms, in any backend file.
words:
	@if grep -nwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' $(SOURCES); then \
	  echo "backend: no Admitted and no axioms" >&2; exit 1; fi

# $(call closed,NAMES): every theorem, lemma, corollary and example in
# each NAME.v must be closed under the global context (no transitive
# dependence on Runtime axioms).
define closed
@for m in $(1); do \
  thms=$$(awk '/^(Theorem|Lemma|Corollary|Example)[[:space:]]+[A-Za-z0-9_'\'']+/ { sub(/:/, "", $$2); print $$2 }' $$m.v); \
  [ -n "$$thms" ] || { echo "backend: no theorems found in $$m.v" >&2; exit 1; }; \
  out=$$({ echo "From Backend Require Import $$m."; \
           for t in $$thms; do echo "Print Assumptions $$t."; done; } \
         | rocq repl -q $(FLAGS) 2>&1 | sed -E 's/^(Rocq < )+//'); \
  if printf '%s\n' "$$out" | grep -vE '^(Welcome|Skipping|\[Loading|Fetching opaque|Closed under the global context$$|[[:space:]]*$$)' >&2; then \
    echo "backend: $$m.v has open assumptions or Print Assumptions errors" >&2; exit 1; fi; \
  closed=$$(printf '%s\n' "$$out" | grep -c '^Closed under the global context$$'); \
  expected=$$(printf '%s\n' "$$thms" | wc -w); \
  [ "$$closed" -eq "$$expected" ] || { echo "backend: $$m.v: closed $$closed != expected $$expected" >&2; exit 1; }; \
done
endef

.regs-assumptions: words RegsProof.vo
	$(call closed,RegsProof)
	@touch $@

.amd64-assumptions: words $(AMD64:=.vo)
	$(call closed,$(AMD64))
	@touch $@

proofs: words $(PROOFS) .regs-assumptions .amd64-assumptions

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
	rm -f .deps .regs-assumptions .amd64-assumptions *.vo *.vok *.vos *.glob .*.aux nanofil-backend
	rm -f extraction/nanofil_backend.ml extraction/nanofil_backend.mli extraction/*.cm* extraction/*.o

.PHONY: all words proofs clean

-include .deps
