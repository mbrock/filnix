# A deterministic bash workload: `bash bash.sh BASH` runs each script
# under BASH and prints its stdout, stderr and exit status, so two
# builds' transcripts can be compared byte for byte. It covers bash's
# own language beyond POSIX sh: indexed and associative arrays, namerefs,
# parameter transformations, [[ ]] and regular expressions, arithmetic
# and (( )), brace expansion, extglob, globstar and nocaseglob, here-
# strings, process substitution, coprocesses, mapfile and read -a,
# printf -v and %q, job control (set -m, jobs, %N, wait -n), signals and
# traps (EXIT, ERR, DEBUG, RETURN, a killed child's status), pipefail
# and PIPESTATUS, the seeded $RANDOM, and error messages. Run it in an
# empty directory; it needs coreutils.
set -u
bash=$1
n=0

run() {
  n=$((n + 1))
  printf '%s\n' "$1" >script$n.sh
  echo "### script $n"
  cat script$n.sh
  echo "### output"
  (export BASHBIN=$bash; exec -a bash "$bash" script$n.sh a1 'b 2' c3) 2>&1 </dev/null &&
    status=0 || status=$?
  echo "### exit $status"
}

run 'echo "$0" $# "$@"; a=(zero one "two three" four); echo ${#a[@]} "${a[2]}" "${a[@]:1:2}"
a+=(five); a[10]=ten; echo "${!a[@]}"; unset "a[1]"; echo "${a[@]}"; echo ${#a[@]}
b=("${a[@]/o/0}"); printf "<%s>" "${b[@]}"; echo; declare -p a'
run 'declare -A m=([one]=1 [two]=2); m[three]=3; m[two]=22
for k in one two three; do echo "$k=${m[$k]}"; done; echo ${#m[@]}
unset "m[one]"; [[ -v m[one] ]] || echo gone; [[ -v m[two] ]] && echo present
declare -A n; n[a b]=space; echo "${n[a b]}"; declare -p n'
run 's="Hello, World"; echo ${s^^} ${s,,} ${s^} ${s~~} ${s//o/0} ${s/#H/J} ${s/%d/D}
echo ${s:7} ${s: -5:3} ${#s} ${s@Q}; t=abcabc; echo ${t#*b} ${t##*b} ${t%b*} ${t%%b*}
p=/usr/local/lib/libfoo.so.1; echo ${p##*/} ${p%/*}; arr=(x y z); echo ${arr[@]^} ${arr[*]@Q}
v=name; name=indirect; echo ${!v}; declare -n r=name; r=changed; echo $name'
run 'x=5; (( x += 3, y = x * 2 )); echo $x $y $(( x ** 3 % 7 )) $(( 1 << 40 )) $(( -17 / 5 )) $(( -17 % 5 ))
echo $(( 16#ff + 2#1010 + 8#17 + 36#zz )) $(( x > 3 ? 100 : 200 )) $(( ~0 )) $(( 0x7fffffffffffffff + 1 ))
for ((i = 0, s = 0; i < 100; i++)); do (( s += i * i )); done; echo $i $s
let "z = 7 * 6" "w = z / 4"; echo $z $w; (( 0 )) || echo "zero is false"; echo $(( 3 / 0 ))'
run 'echo {a,b,c}{1,2} {1..10} {10..1..3} {a..e} x{,y,z}w {01..12..4}
f() { local -i n=$1; (( n <= 1 )) && { echo 1; return; }; echo $(( n * $(f $((n - 1))) )); }; f 20
fib() { local a=0 b=1 i; for ((i = 0; i < $1; i++)); do (( b = a + b, a = b - a )); done; echo $a; }; fib 90'
run 's=foobar123; [[ $s == foo* ]] && echo glob; [[ $s =~ ^([a-z]+)([0-9]+)$ ]] && echo "${BASH_REMATCH[@]}"
[[ abc < abd && ! -z $s ]] && echo less; [[ -n "" || 3 -gt 2 ]] && echo or
re="([0-9]+)-([0-9]+)"; [[ "10-20 30-40" =~ $re ]] && echo "${BASH_REMATCH[2]}${BASH_REMATCH[1]}"
[[ x =~ [ ]] ; echo "bad regex $?"'
run 'shopt -s extglob nullglob; touch a.c b.c c.h dd.txt e.tar.gz
echo *.@(c|h); echo !(*.c); echo +([a-d]).*; echo ?(a|b).c; echo *.none
shopt -s globstar; mkdir -p d/e/f; touch d/x.c d/e/y.c d/e/f/z.c; echo **/*.c
shopt -s nocaseglob; touch Upper.TXT; echo *.txt; GLOBIGNORE="*.c"; echo *; unset GLOBIGNORE
case e.tar.gz in *.@(gz|bz2)) echo compressed;; esac'
run 'read -r w1 w2 <<< "here string"; echo "[$w2][$w1]"; cat <<< "$((6 * 7))"
diff <(printf "a\nb\nc\n") <(printf "a\nc\n"); echo "diff $?"
while read -r l; do echo "got $l"; done < <(printf "p\nq\n")
mapfile -t lines < <(seq 1 5); echo ${#lines[@]} "${lines[-1]}"; IFS=: read -ra parts <<< "a:b::c"; declare -p parts
printf -v out "%05d|%-6s|%x|%q" 42 ab 255 "it'"'"'s here"; echo "$out"; printf "%s,%s\n" 1 2 3 4 5'
run 'coproc up { while read -r l; do echo "${l^^}"; done; }
echo hello >&"${up[1]}"; read -r ans <&"${up[0]}"; echo "$ans"; exec {up[1]}>&-; wait $up_PID; echo "coproc $?"
exec {fd}>out.txt; echo via fd >&$fd; exec {fd}>&-; cat out.txt
{ echo err >&2; echo out; } 2>&1 >/dev/null | cat; echo both &>both.txt; cat both.txt'
run 'set -m; sleep 30 & sleep 31 & jobs | sed "s/  */ /g"; kill %1; wait %1; echo "killed $?"
kill -STOP %2; until [[ $(jobs -s) ]]; do sleep 0.05; done; jobs -s | sed "s/  */ /g"; kill -CONT %2; kill %2; wait; echo "all $?"'
run '(exit 3) & (sleep 2; exit 5) & wait -n; echo "first $?"; wait -n; echo "second $?"
true | false | true; echo "${PIPESTATUS[@]}"; set -o pipefail; true | false | true; echo "pipefail $?"'
run 'trap "echo exit trap \$?" EXIT; trap "echo err at \$LINENO" ERR
false; echo after; f() { trap "echo returning" RETURN; return 4; }; f; echo "f $?"
trap "echo got USR1" USR1; kill -USR1 $$; trap - ERR
( trap "echo child TERM; exit 9" TERM; : >ready; while :; do :; done ) &
until [[ -e ready ]]; do :; done; kill -TERM $!; wait $!; echo "child $?"
sleep 5 & kill -KILL $!; wait $! 2>/dev/null; echo "killed $?"; exit 6'
run 'n=0; trap "(( n++ ))" DEBUG; a=1; b=2; c=3; trap - DEBUG; echo "debug ran $n times"
set -e; f() { false; echo "not here"; }; f || echo "f failed"; (false); echo "not reached"'
run 'RANDOM=42; echo $RANDOM $RANDOM $RANDOM; RANDOM=42; r1=$RANDOM; echo $r1
declare -i i=10; i+=5; i="i * 2"; echo $i; declare -u up=shout; declare -l lo=QUIET; echo $up $lo
readonly ro=1; ro=2 2>/dev/null; echo "ro $?"; declare -r -x RX=y; bash_cmd=$BASHBIN; "$bash_cmd" -c "echo \$RX"
f() { local x=local; g; }; g() { echo "g sees $x"; }; x=global; f; echo $x; echo ${FUNCNAME:-none}'
run 'h=""; for ((i = 0; i < 3000; i++)); do h+="$((i % 10))"; done; echo ${#h} ${h:2990}
declare -A cnt; for w in $(for ((i = 0; i < 500; i++)); do echo w$((i * 7 % 13)); done); do (( cnt[$w]++ )); done
for k in $(printf "%s\n" "${!cnt[@]}" | sort); do printf "%s:%d " $k ${cnt[$k]}; done; echo
big=(); for ((i = 0; i < 2000; i++)); do big+=("item$i"); done; echo ${#big[@]} ${big[1999]}; unset "big[@]"; echo ${#big[@]}
primes=(); for ((c = 2; ${#primes[@]} < 60; c++)); do for p in "${primes[@]}"; do (( p * p > c )) && break; (( c % p )) || continue 2; done; primes+=($c); done; echo ${primes[@]: -5}'
run 'select x in a b; do echo $x; break; done <<< 2
printf "%(%Y)T\n" 0 2>/dev/null | wc -c; type -t cd ls nosuch f 2>&1; command -V echo
alias greet="echo hi"; shopt -s expand_aliases; eval greet; hash -r; enable -n echo; type -t echo; enable echo
echo "${BASH_VERSINFO[0]}.${BASH_VERSINFO[1]}"; compgen -W "alpha beta alpine" -- al; caller 2>&1; echo $((BASH_SUBSHELL)) $(echo $BASH_SUBSHELL)'
run 'set -u; echo "${undefined_var}"'
run 'echo ${bad substitution}'
run 'if then fi'
run 'f() { f; }; FUNCNEST=100; f'
run 'x=( [1]=a [3]=b ); echo "${x[@]}" ${x[-1]}; x[-5]=c'
run 'nosuchcommand; echo "status $?"; ./nofile; echo "status $?"; exit 300'
