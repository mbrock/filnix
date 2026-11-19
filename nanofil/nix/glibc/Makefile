sources := $(shell find glibc -name '*.v' | sort)
objects := $(sources:.v=.vo)

.PHONY: all
all: $(objects)

glibc/%.vo: glibc/%.v
	@bash $(compile) $<

include rocq.dep
