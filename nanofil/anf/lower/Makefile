# Build the λANF lowering (AnfLower.v) and its driver ./anf-lower.
#   make            compile, extract, link ./anf-lower
#   make clean
# Needs rocq, the Rocq stdlib, ocamlfind and zarith, as the Gallina
# backend does (rocq/backend/Makefile, whose files it imports).
BACKEND = ../../rocq/backend
FLAGS = -R ../../rocq/theories Nanofil -R $(BACKEND) Backend -R . Anf

all: anf-lower

backend:
	$(MAKE) -C $(BACKEND) Text.vo Order.vo IrText.vo ../theories/core/Maps.vo

AnfLower.vo: AnfLower.v backend
	rocq compile $(FLAGS) AnfLower.v

AnfExtract.vo: AnfExtract.v AnfLower.vo
	mkdir -p extraction
	rocq compile $(FLAGS) AnfExtract.v

anf-lower: AnfExtract.vo main.ml
	cd extraction && ocamlfind ocamlopt -w -a -package zarith -linkpkg \
	  anf_lower.mli anf_lower.ml ../main.ml -o ../anf-lower

clean:
	rm -rf *.vo *.vok *.vos *.glob .*.aux anf-lower extraction

.PHONY: all backend clean
