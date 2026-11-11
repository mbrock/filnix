#!/usr/bin/env bash
# The backend extracted by Crane's joom/refactor branch, file by file
# (docs/gallina-backend.md, "Crane's joom/refactor branch"). An
# experiment that no check builds: the checked C++ build is ../Makefile
# on nix/crane.nix's pin.
#
#   CRANE=/path/to/crane ROCQ=/path/to/built/nanofil/rocq build.sh OUT
#
# CRANE is bloomberg/crane at fa70df57 (joom/refactor) with crane.patch
# applied and `dune build src theories` run against Rocq 9.1. ROCQ is
# this repository's nanofil/rocq with theories/ and backend/ compiled.
# `rocq` (9.1) must be on PATH with Crane's plugin on OCAMLPATH.
#
# CXX and STD pick the C++ compiler: clang 21 at c++2c natively, or
# Fil-C's clang++ at c++2c with CXXFLAGS and LDFLAGS naming its gmp.
# OUT/nanofil-backend-cpp is the program; OUT/obj/NAME.time has each
# file's seconds and peak memory.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1
crane=$(cd "$CRANE" && pwd)
rocq=$(cd "$ROCQ" && pwd)
cxx=${CXX:-clang++} std=${STD:-c++2c} jobs=${JOBS:-$(nproc)}

mkdir -p "$out/obj"
cd "$out"
cp "$here"/../{CraneExtract.v,CraneMap.v,main.cpp,nfrt.h} .
patch -s -p1 <"$here/backend.patch"

flags="-w -crane-extraction-reserved-identifier,-overriding-logical-loadpath"
flags="$flags -R $crane/_build/default/theories Crane"
flags="$flags -R $rocq/theories Nanofil -R $rocq/backend Backend -R . BackendCrane"
rm -rf x
# shellcheck disable=SC2086
rocq compile $flags CraneMap.v
# shellcheck disable=SC2086
rocq compile $flags CraneExtract.v
src=x/BackendCrane

# Three repairs to what Crane writes.
# Layout::float_class and Syntax::float_class both take a Syntax::Class_,
# so an unqualified call inside Layout is ambiguous.
sed -i 's/\([^:A-Za-z_]\)float_class(/\1Layout::float_class(/g' $src/Layout.cpp
# A method value's receiver type is written without its namespace.
sed -i 's/\[\](const Term &_x)/[](const Term::Term \&_x)/g' $src/Transport.cpp
# A global built from a variable template (Maps::nm_empty<T>) can be
# initialized before it, and then copies a null box.
sed -i 's/Maps::template nm_empty<Syntax::Value>, Maps::template nm_empty<Datatypes::List<Term::name>>}/Maps::ZMap::template empty<Datatypes::List<std::pair<Term::name, Syntax::Value>>>(), Maps::ZMap::template empty<Datatypes::List<std::pair<Term::name, Datatypes::List<Term::name>>>>()}/' $src/Fuse.h

cat >obj/one.py <<'EOF'
import os, subprocess, sys, time
cmd, f = sys.argv[1:-1], sys.argv[-1]
b = os.path.basename(f)[:-4]
s = time.time()
with open("obj/" + b + ".log", "wb") as log:
    p = subprocess.Popen(cmd + ["-c", f, "-o", "obj/" + b + ".o"], stdout=log, stderr=log)
    _, st, ru = os.wait4(p.pid, 0)
rc = os.waitstatus_to_exitcode(st)
with open("obj/" + b + ".time", "w") as t:
    t.write("%s rc=%d %.1f s %d MB\n" % (b, rc, time.time() - s, ru.ru_maxrss // 1024))
sys.exit(rc)
EOF
inc="-I. -I$src -I$crane/theories/cpp"
# shellcheck disable=SC2086
ls $src/*.cpp | xargs -P "$jobs" -n1 \
  python3 obj/one.py "$cxx" -std="$std" -O2 -w $inc ${CXXFLAGS:-}
# Crane defines functions that are not inline in its headers, so the
# linker is told to take the first definition of each.
# shellcheck disable=SC2086
"$cxx" -std="$std" -O2 -w -Wl,-z,muldefs $inc ${CXXFLAGS:-} main.cpp obj/*.o \
  -o nanofil-backend-cpp ${LDFLAGS:-} -lgmpxx -lgmp
