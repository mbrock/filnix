#!/bin/sh
# usage: run.sh <clang> <outdir>   (OPT defaults to -O2)
# Builds liba.so (linked into main) and libb.so (dlopened RTLD_LOCAL); both
# define which(). Prints what each kind of reference resolves to.
set -e
CC=$1; O=$2; OPT=${OPT:--O2}; D=$(dirname "$0"); mkdir -p "$O"
$CC $OPT -shared -fPIC "$D/a.c" -o "$O/liba.so"
$CC $OPT -shared -fPIC "$D/b.c" -o "$O/libb.so"
$CC $OPT -shared -fPIC -Wl,-Bsymbolic "$D/b.c" -o "$O/libb-sym.so"
$CC $OPT "$D/main.c" -L"$O" -la -Wl,-rpath,"$O" -o "$O/main"
printf 'plain:     '; "$O/main" "$O/libb.so"
printf 'Bsymbolic: '; "$O/main" "$O/libb-sym.so"
