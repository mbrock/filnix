# Build the Gallina middle-end optimizer modules (Opt.*) and soundness proofs.
FLAGS = -R ../theories Nanofil -R ../backend Backend -R . Opt
SOURCES = $(shell grep '\.v$$' _RocqProject)
MODEL = $(shell find ../theories -name '*.v' | sort)
BACKEND = $(shell awk '/\.v$$/' ../backend/_RocqProject | sed 's|^|../backend/|')

PROOFS = OptAluProof AliasProof CopyLocalProof SimplifyArithProof SimplifyRebaseProof SimplifyCfgProof

all: words $(SOURCES:.v=.vo) .opt-assumptions

words:
	@if grep -nwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' $(SOURCES); then \
	  echo "opt: no Admitted and no axioms" >&2; exit 1; fi

# $(call closed,NAMES): every theorem, lemma, corollary and example in
# each NAME.v must be closed under the global context (no transitive
# dependence on Runtime axioms).
define closed
@for m in $(1); do \
  thms=$$(awk '/^(Theorem|Lemma|Corollary|Example)[[:space:]]+[A-Za-z0-9_'\'']+/ { sub(/[:({].*/, "", $$2); print $$2 }' $$m.v); \
  [ -n "$$thms" ] || { echo "opt: no theorems found in $$m.v" >&2; exit 1; }; \
  out=$$({ echo "From Opt Require Import $$m."; \
           for t in $$thms; do echo "Print Assumptions $$t."; done; } \
         | rocq repl -q $(FLAGS) 2>&1 | sed -E 's/^(Rocq < )+//'); \
  if printf '%s\n' "$$out" | grep -vE '^(Welcome|Skipping|\[Loading|Fetching opaque|Closed under the global context$$|[[:space:]]*$$)' >&2; then \
    echo "opt: $$m.v has open assumptions or Print Assumptions errors" >&2; exit 1; fi; \
  closed=$$(printf '%s\n' "$$out" | grep -c '^Closed under the global context$$'); \
  expected=$$(printf '%s\n' "$$thms" | wc -w); \
  [ "$$closed" -eq "$$expected" ] || { echo "opt: $$m.v: closed $$closed != expected $$expected" >&2; exit 1; }; \
  printf '@@nanofil-opt-proofs %s: %d/%d closed under the global context\n' "$$m" "$$closed" "$$expected"; \
done
endef

.opt-assumptions: words $(PROOFS:=.vo)
	$(call closed,$(PROOFS))
	@touch $@

proofs: words $(PROOFS:=.vo) .opt-assumptions

.deps: _RocqProject $(SOURCES) $(MODEL) $(BACKEND)
	rocq dep $(FLAGS) $(MODEL) $(BACKEND) $(SOURCES) >$@ 2>/dev/null

%.vo: %.v
	@start=$$(date +%s%N); rocq compile $(FLAGS) $< && \
	ms=$$((($$(date +%s%N) - start) / 1000000)) && \
	printf '@@nanofil-opt %4d.%01ds %5d lines %s\n' \
	  $$((ms / 1000)) $$((ms % 1000 / 100)) "$$(wc -l <$<)" $<

clean:
	rm -f .deps .opt-assumptions *.vo *.vok *.vos *.glob .*.aux

.PHONY: all words proofs clean

-include .deps
