# Build the Rocq model and its extracted driver (docs/formal.md, Campaign 1).
#   make            compile theories/, extract, link ./nanofil-model
#   make clean
# Needs rocq, the Rocq stdlib, ocamlfind and zarith (nix/rocq.nix).
all: nanofil-model

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

theories: Makefile.rocq
	$(MAKE) -f Makefile.rocq

extraction/nanofil_model.ml: theories

nanofil-model: extraction/nanofil_model.ml extraction/main.ml
	cd extraction && ocamlfind ocamlopt -w -a -package zarith -linkpkg \
	  nanofil_model.mli nanofil_model.ml main.ml -o ../nanofil-model

clean:
	if [ -f Makefile.rocq ]; then $(MAKE) -f Makefile.rocq clean; fi
	rm -f Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d nanofil-model
	rm -f extraction/nanofil_model.ml extraction/nanofil_model.mli extraction/*.cm* extraction/*.o

.PHONY: all theories clean
