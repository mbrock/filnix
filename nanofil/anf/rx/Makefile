# Build the Gallina regex compiler (Rx.v) and the gate's program
# ./rx-gallina, which prints what rx.pl's rx_file/1 prints.
#   make            compile, extract, link ./rx-gallina
#   make clean
# Needs rocq, the Rocq stdlib, ocamlfind and zarith, as the Gallina
# backend does (nix-shell ../lower/shell.nix), and the backend's Text.vo and
# IrText.vo and the model's Maps.vo, which are made there when missing.
BACKEND = ../../rocq/backend
FLAGS = -R ../../rocq/theories Nanofil -R $(BACKEND) Backend -R . Rx
DEPS = $(BACKEND)/Text.vo $(BACKEND)/IrText.vo ../../rocq/theories/core/Maps.vo

all: rx-gallina

$(DEPS):
	$(MAKE) -C $(BACKEND) Text.vo IrText.vo ../theories/core/Maps.vo

Rx.vo: Rx.v $(DEPS)
	rocq compile $(FLAGS) Rx.v

Extract.vo extraction/rx.ml: Extract.v Rx.vo
	mkdir -p extraction
	rocq compile $(FLAGS) Extract.v

rx-gallina: extraction/rx.ml main.ml
	cd extraction && ocamlfind ocamlopt -w -a -package zarith -linkpkg \
	  rx.mli rx.ml ../main.ml -o ../rx-gallina

clean:
	rm -rf *.vo *.vok *.vos *.glob .*.aux rx-gallina extraction main.cm* main.o

.PHONY: all clean
