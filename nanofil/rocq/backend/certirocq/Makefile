# Build the CertiRocq C compilation of the Gallina backend
# (docs/gallina-backend.md, M8).
#   make            compile with CertiRocq, build ./nanofil-backend-c
#   make clean
# Needs the backend compiled (make -C .. Compile.vo IrText.vo) by the
# Rocq that CertiRocq's plugin was built against, the plugin on
# OCAMLPATH and CertiRocq's theory on ROCQPATH, and CERTIROCQ_RUNTIME
# naming CertiRocq's runtime directory (nix/certirocq.nix,
# nix/backend-certirocq.nix).
FLAGS = -w -overriding-logical-loadpath \
  -R ../../theories Nanofil -R .. Backend -R . BackendCertiRocq
SOURCES = $(shell grep '\.v$$' _RocqProject)
CC ?= clang
CFLAGS ?= -O1 -w -Wno-int-conversion -Wno-incompatible-pointer-types -Wno-implicit-function-declaration
CPPFLAGS += -I. $(if $(CERTIROCQ_RUNTIME),-I$(CERTIROCQ_RUNTIME))

SHARDS = nb_0.o nb_1.o nb_2.o nb_3.o nb_4.o nb_5.o nb_6.o nb_7.o \
         nb_8.o nb_9.o nb_10.o nb_11.o nb_12.o nb_13.o nb_14.o nb_15.o

all: nanofil-backend-c

# No Admitted and no axioms, as in the backend.
words:
	@if grep -nwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' $(SOURCES); then \
	  echo "backend/certirocq: no Admitted and no axioms" >&2; exit 1; fi

%.vo: %.v
	@start=$$(date +%s%N); rocq compile $(FLAGS) $< && \
	ms=$$((($$(date +%s%N) - start) / 1000000)) && \
	printf '@@nanofil-backend-certirocq %4d.%01ds %s\n' $$((ms / 1000)) $$((ms % 1000 / 100)) $<

CertiExtract.vo: ../Compile.vo ../IrText.vo

nb.c glue.c glue.h nb.h: CertiExtract.vo

nb_0.c nb_1.c nb_2.c nb_3.c nb_4.c nb_5.c nb_6.c nb_7.c \
nb_8.c nb_9.c nb_10.c nb_11.c nb_12.c nb_13.c nb_14.c nb_15.c \
nb_decls.h const_strs.c const_strs.h &: nb.c split_nb.py
	python3 ./split_nb.py 16

gc_stack.o: $(CERTIROCQ_RUNTIME)/gc_stack.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

%.o: %.c nb_decls.h const_strs.h glue.h nb.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

nanofil-backend-c: words $(SHARDS) const_strs.o overrides.o glue.o gc_stack.o main.o
	$(CC) $(CFLAGS) $(SHARDS) const_strs.o overrides.o glue.o gc_stack.o main.o -o $@

clean:
	rm -rf *.vo *.vok *.vos *.glob .*.aux nb.c nb.h glue.c glue.h \
	  nb_*.c nb_*.o nb_decls.h const_strs.c const_strs.h *.o nanofil-backend-c

.PHONY: all words clean
