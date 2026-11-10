# Build the C++ extraction of the Gallina backend
# (docs/gallina-backend.md, M6).
#   make            extract with Crane, compile ./nanofil-backend-cpp
#   make check      also build and run the self-test of the mappings
#   make clean
# Needs the backend compiled (make -C .. Compile.vo IrText.vo Order.vo) by the
# Rocq that Crane's plugin was built against, the plugin on OCAMLPATH
# and Crane's theory on ROCQPATH, a C++23 compiler, gmpxx, and
# CRANE_INCLUDE naming the directory of Crane's headers
# (nix/crane.nix, nix/backend-crane.nix).
FLAGS = -w -crane-extraction-reserved-identifier,-overriding-logical-loadpath \
  -R ../../theories Nanofil -R .. Backend -R . BackendCrane
SOURCES = $(shell grep '\.v$$' _RocqProject)
CXX = clang++
CXXFLAGS ?= -O2
CPPFLAGS += -std=c++23 -I. -IBackendCrane $(if $(CRANE_INCLUDE),-I$(CRANE_INCLUDE))
LDLIBS = -lgmpxx -lgmp

all: nanofil-backend-cpp

# No Admitted and no axioms, as in the backend.
words:
	@if grep -nwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' $(SOURCES); then \
	  echo "backend/crane: no Admitted and no axioms" >&2; exit 1; fi

%.vo: %.v
	@start=$$(date +%s%N); rocq compile $(FLAGS) $< && \
	ms=$$((($$(date +%s%N) - start) / 1000000)) && \
	printf '@@nanofil-backend-crane %4d.%01ds %s\n' $$((ms / 1000)) $$((ms % 1000 / 100)) $<

# Compiling CraneExtract.v writes nb.h and nb.cpp, and CraneSelfTest.v
# st.h and st.cpp, into BackendCrane, the directory Crane names after
# the files' logical path.
CraneExtract.vo: CraneMap.vo ../Compile.vo ../IrText.vo
CraneSelfTest.vo: CraneMap.vo ../Order.vo ../IrText.vo

nanofil-backend-cpp: words CraneExtract.vo main.cpp nfrt.h
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) main.cpp -o $@ $(LDLIBS)

selftest: CraneSelfTest.vo selftest.cpp nfrt.h
	$(CXX) $(CPPFLAGS) -O1 selftest.cpp -o $@ $(LDLIBS)

check: nanofil-backend-cpp selftest
	./selftest

clean:
	rm -rf *.vo *.vok *.vos *.glob .*.aux BackendCrane nanofil-backend-cpp selftest

.PHONY: all words check clean
