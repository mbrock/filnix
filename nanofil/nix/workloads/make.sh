# A deterministic GNU make workload: `bash make.sh MAKE` prints each
# command's exit status and output, with the working directory replaced
# by DIR, so two builds' transcripts can be compared byte for byte.
# make forks and execs recipes (posix_spawn), runs pattern, static and
# archive-member rules, its functions ($(shell), $(eval), $(let),
# $(intcmp), $(file)...), remakes included makefiles, and reports
# errors. Under -j1 to -j8 it hands out job slots through the jobserver,
# fifo and pipe style, to recursive makes, and keeps -O output grouped;
# a recipe's signals (SIGTERM, SIGHUP to make, SIGSEGV of a child)
# delete the target being built. Parallel output is sorted, and the
# jobserver's limit checked, rather than printed in completion order.
# Run it in an empty directory.
set -u
make=$1
export LC_ALL=C
unset MAKEFLAGS MFLAGS MAKELEVEL
here=$PWD

run() {
  echo "### make $*"
  # bash's own report of a make killed by a signal names its pid.
  { ("$make" "$@") >out 2>&1; } 2>/dev/null && status=0 || status=$?
  sed "s|$here|DIR|g; s|^$make|make|; s|^make\[[0-9]*\]|make[N]|" out
  echo "### exit $status"
}
# For parallel runs: the lines in a stable order.
runs() {
  echo "### make $* (sorted)"
  ("$make" "$@") >out 2>&1 && status=0 || status=$?
  sed "s|$here|DIR|g; s|^$make|make|; s|^make\[[0-9]*\]|make[N]|" out | sort
  echo "### exit $status"
}
tree() { find "$@" -type f | sort | xargs sha256sum | cut -c1-16,64-; }

# Rules: pattern, static pattern, order-only, VPATH, automatic variables,
# an intermediate file and its removal, a target-specific variable.
mkdir -p src gen
for i in $(seq 1 40); do printf 'unit %d\nvalue %d\n' $i $((i * i % 97)) >src/u$i.in; done
cat >rules.mk <<'EOF'
VPATH = src
UNITS := $(sort $(patsubst src/%.in,%,$(wildcard src/*.in)))
all: gen/index
gen/%.up: %.in | gen
	tr a-z A-Z <$< >$@
gen/%.out: gen/%.up
	{ echo "$(@F) from $(<F) ($(words $^) prerequisite)"; cat $<; } >$@
$(UNITS:%=gen/%.sum): gen/%.sum: gen/%.out
	cksum <$< | sed 's/ .*//' >$@
gen/index: $(UNITS:%=gen/%.sum)
	cat $^ | sort -n | head -3 >$@; echo "$(words $?) changed" >>$@
gen:
	mkdir -p $@
gen/u7.sum: EXTRA = seven
gen/u7.sum: ; echo $(EXTRA) >$@
.PHONY: all
EOF
run -f rules.mk
run -f rules.mk
run -f rules.mk -q; run -f rules.mk -n -W src/u3.in
touch src/u3.in; run -f rules.mk
runs -f rules.mk -B -j4 --output-sync=target gen/u1.sum gen/u2.sum
tree gen

# Functions, including 4.4's $(let) and $(intcmp), $(file) and $(eval).
cat >fun.mk <<'EOF'
words := the quick brown fox jumps over the lazy dog
define tmpl
v_$(1) := $$(words $(2)) $(2)
endef
$(foreach w,fox dog,$(eval $(call tmpl,$(w),$(w) $(w)s)))
rev = $(if $(1),$(call rev,$(wordlist 2,$(words $(1)),$(1))) $(firstword $(1)))
$(file >list.txt,$(words))
$(file >>list.txt,more)
$(info sort: $(sort $(words)))
$(info rev: $(strip $(call rev,$(words))))
$(info subst: $(subst o,0,$(words)) | $(patsubst %o%,[%],$(words)))
$(info filter: $(filter %o%,$(words)) | $(filter-out the,$(words)))
$(info word: $(word 3,$(words)) $(lastword $(words)) $(words $(words)))
$(info eval: $(v_fox) / $(v_dog) / $(origin v_fox) $(flavor rev))
$(info let: $(let a b,1 2 3,<$(a)><$(b)>))
$(info intcmp: $(intcmp 3,5,lt,eq,gt) $(intcmp 12,12,lt,eq,gt) $(intcmp -2,-9,lt,eq,gt))
$(info shell: $(shell printf 'a\nb\n' | tr a-z A-Z) $(.SHELLSTATUS))
$(info file: $(file <list.txt))
$(info value: $(value rev))
$(info join: $(join a b c,1 2) $(addprefix x/,y z) $(addsuffix .c,p q) $(dir a/b c) $(notdir a/b c) $(basename a.b/c.d e) $(suffix x.c y))
$(info andor: [$(and a,,b)] [$(or ,b,c)] [$(if ,y,n)])
$(warning a warning)
all: ; @echo done $(MAKE_VERSION) $(.FEATURES)
EOF
run -f fun.mk
run -f fun.mk -e words="override me" 'words+=too'
cat >err.mk <<'EOF'
x = $(x) loop
all: ; @echo $(x)
EOF
run -f err.mk
printf 'all:\n\t@echo $(error stop here)\n' >stop.mk
run -f stop.mk

# Included makefiles that make regenerates, then restarts.
cat >inc.mk <<'EOF'
include gen.d
all: ; @echo "generated: $(GENERATED) (restarts: $(MAKE_RESTARTS))"
gen.d: ; echo 'GENERATED := yes' >$@
EOF
run -f inc.mk
run -f inc.mk

# Errors: no rule, -k, -i, a failing recipe, .DELETE_ON_ERROR.
cat >fail.mk <<'EOF'
.DELETE_ON_ERROR:
all: a b c
a: ; echo a >$@; false
b: missing ; touch $@
c: ; -false; echo c >$@
EOF
run -f fail.mk
run -f fail.mk -k
run -f fail.mk -i
ls a b c 2>&1; rm -f a b c

# Archive members: arscan.c reads the archive's member table.
printf 'one\n' >m1.o; printf 'two\n' >m2.o
cat >ar.mk <<'EOF'
lib.a: lib.a(m1.o m2.o)
lib.a(%.o): %.o ; $(AR) rU $@ $<
EOF
touch -d '2001-01-01 00:00' m1.o m2.o
run -f ar.mk
run -f ar.mk
touch -d '2002-01-01 00:00' m2.o; run -f ar.mk
ar t lib.a

# Parallel builds through the jobserver: 120 jobs, recursive makes in
# four subdirectories, both jobserver styles. Each job records its start
# and end; the most jobs running at once must not exceed -j.
mkdir -p par
cat >par/Makefile <<'EOF'
N := $(shell seq 1 30)
all: $(N:%=t%)
t%:
	@echo + >>../active.$(J); \
	echo "$(SUB) $@ $(if $(findstring jobserver-auth,$(MAKEFLAGS)),js,nojs)"; \
	echo "$(SUB) $@" >$@; \
	echo - >>../active.$(J)
EOF
cat >top.mk <<'EOF'
SUBS := s1 s2 s3 s4
all: $(SUBS)
$(SUBS):
	@mkdir -p $@ && cp par/Makefile $@/
	+@$(MAKE) --no-print-directory -C $@ SUB=$@ J=$(J)
.PHONY: all $(SUBS)
EOF
for j in 1 2 4 8; do
  for style in fifo pipe; do
    rm -rf s1 s2 s3 s4 active.$j
    runs -f top.mk -j$j --jobserver-style=$style J=$j
    awk -v j=$j '/\+/ { n++; if (n > m) m = n } /-/ { n-- }
      END { print "jobs at once <= " j ": " (m <= j ? "yes" : "no (" m ")") }' active.$j
    cat s*/t* | sort | sha256sum | cut -c1-16
  done
done
# -O keeps each target's lines together.
cat >sync.mk <<'EOF'
all: $(shell seq 1 24)
%: ; @echo "$@ begin"; echo "$@ middle" >&2; echo "$@ end"
EOF
"$make" -f sync.mk -j8 -Otarget >sync.out 2>&1 && status=0 || status=$?
awk '{ split($0, w); if (w[2] == "begin") { cur = w[1] } else if (w[1] != cur) bad++ }
  END { print "-Otarget grouped lines: " (bad ? "no" : "yes") ", " NR " lines" }' sync.out
echo "### exit $status"

# Signals: a recipe that signals make, and a child that dies of one.
cat >sig.mk <<'EOF'
term: ; echo partial >$@; kill -TERM $$PPID; sleep 2
hup: ; echo partial >$@; kill -HUP $$PPID; sleep 2
segv: ; echo partial >$@; kill -SEGV $$$$
EOF
for t in term hup segv; do
  run -f sig.mk $t
  ls $t 2>&1 || true
done
