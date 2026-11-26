# Build the Gallina C frontend (CLex.v + CParse.v + CCanon.v) and extract ./nanofil-frontend.
FLAGS = -R . Frontend
SOURCES = $(shell grep '\.v$$' _RocqProject)

all: nanofil-frontend

words:
	@if grep -nwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' $(SOURCES); then \
	  echo "frontend: no Admitted and no axioms" >&2; exit 1; fi

%.vo: %.v
	rocq compile $(FLAGS) $<

CAst.vo: CAst.v
CAttrs.vo: CAttrs.v CAst.vo
CLex.vo: CLex.v CAst.vo CAttrs.vo
CParse.vo: CParse.v CAst.vo CAttrs.vo CLex.vo
CCanon.vo: CCanon.v CAst.vo CAttrs.vo CLex.vo
CPp.vo: CPp.v CAst.vo CAttrs.vo CLex.vo CParse.vo
Extract.vo: Extract.v CAst.vo CAttrs.vo CLex.vo CParse.vo CCanon.vo CPp.vo

nanofil-frontend: words Extract.vo extraction/main.ml
	cd extraction && ocamlfind ocamlopt -w -a -package zarith,unix -linkpkg \
	  nanofil_frontend.mli nanofil_frontend.ml main.ml -o ../nanofil-frontend

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux nanofil-frontend
	rm -f extraction/nanofil_frontend.ml extraction/nanofil_frontend.mli extraction/*.cm* extraction/*.o

.PHONY: all words clean
