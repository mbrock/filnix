{
  pkgs,
  filcc,
  trealla,
}:
pkgs.runCommand "filc-trealla-runtime-check" { } ''
  mkdir source
  tar -xf ${trealla.src} -C source --strip-components=1
  cd source
  ln -s ${trealla}/bin/tpl tpl
  for test in clpz_regression dcg_consult dcg_corpus dcg_differential dcg_quads \
    dcg_tabling tabling tabling_incremental tabling_reconstruct \
    tabling_restraints tabling_shared tabling_subsumption; do
    echo "Checking $test"
    timeout 60 ./tpl -q -f -g halt tests/sundry/$test.pl > actual
    diff -u tests/sundry/$test.expected actual
  done
  cd ..
  # Exercise the installed libraries away from the source checkout.
  timeout 30 ${trealla}/bin/tpl -q -f -g \
    'use_module(library(assoc)),empty_assoc(A),put_assoc(key,A,value,B),get_assoc(key,B,value),X is 2^100,X =:= 1267650600228229401496703205376,write(ok),nl,halt.' \
    > actual
  echo ok > expected
  diff -u expected actual
  echo 'int trealla_test_increment(int x) { return x + 1; }' > ffi.c
  ${filcc}/bin/clang -shared -fPIC ffi.c -o ffi.so
  cat > ffi.pl <<EOF
  :- use_foreign_module('$PWD/ffi.so', [trealla_test_increment([sint], sint)]).
  :- initialization(main).
  main :- trealla_test_increment(41, 42), write(ok), nl.
  EOF
  timeout 30 ${trealla}/bin/tpl -q -f -g halt ffi.pl > actual
  diff -u expected actual
  touch $out
''
