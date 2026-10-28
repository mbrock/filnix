# A deterministic dash workload: `bash dash.sh DASH` runs each script
# under DASH and prints its stdout, stderr and exit status, so two
# builds' transcripts can be compared byte for byte. It covers the
# parser and expansions (parameters, arithmetic, globbing, here-
# documents, quoting), functions and local, fork and exec (pipelines,
# subshells, command substitution, background jobs and wait), signals
# (trap, kill to self and children, EXIT traps, exit statuses of
# killed processes), redirections and file descriptors, builtins (read,
# printf, test, getopts, cd, umask, eval, set), file operations and
# errors. Run it in an empty directory; it needs coreutils and sed.
set -u
dash=$1
n=0

run() {
  n=$((n + 1))
  printf '%s\n' "$1" >script$n.sh
  echo "### script $n"
  cat script$n.sh
  echo "### output"
  (export DASHBIN=$dash; exec -a dash "$dash" script$n.sh a1 'b 2' c3) 2>&1 </dev/null &&
    status=0 || status=$?
  echo "### exit $status"
}

run 'echo "$0" $# "$@"; for a in "$@"; do printf "<%s>" "$a"; done; echo
shift; echo "$*"; set -- x y z; echo $# ${2} ${10:-none}'
run 'x=hello; y=${x#he} z=${x%lo} w=${x##*l} v=${#x}; echo $y $z $w $v
u=${unset:-default} ${unset2:=assigned}; echo $u $unset2; echo ${x:+set} ${nope:+set}
p=/usr/local/lib/libfoo.so.1; echo ${p##*/} ${p%/*} ${p%%.*}'
run 'echo $((7 * 6)) $((2 ** 10)) $((17 % 5)) $((1 << 20)) $((-7 / 2)) $((0x1f + 010))
i=0; while [ $i -lt 5 ]; do i=$((i + 1)); s=$((${s:-0} + i * i)); done; echo $i $s
echo $(( (3 > 2) && (2 > 3) || 7 )) $(( ~5 ^ 3 )) $(( i += 10 )) $i'
run 'f() { local a=inner; echo "f: $1 $a $#"; return 3; }
a=outer; f one two; echo "status $? a=$a"
g() { echo "g$1"; [ "$1" -gt 0 ] && g $(($1 - 1)); }; g 3
h() { echo "$@" | while read x y; do echo "[$y][$x]"; done; }; h first second'
run 'echo one | cat | cat -n; printf "a\nb\nc\n" | wc -l
v=$(echo inner $(echo nested)); echo "$v"; echo "`echo backquote`"
( cd /; pwd; exit 4 ); echo "sub $?"; pwd >/dev/null
{ echo grouped; echo block; } | cat'
run 'trap "echo got USR1" USR1; kill -USR1 $$; echo after
trap "echo exiting" EXIT; trap "echo got TERM; exit 7" TERM
kill -TERM $$; echo not reached'
run '( trap "echo child USR1; exit 9" USR1; : >ready; while :; do :; done ) &
until [ -e ready ]; do :; done; kill -USR1 $!; wait $!; echo "child status $?"
sleep 5 & kill -TERM $!; wait $!; echo "killed status $?"
false & wait $!; echo "bg false $?"; true & wait; echo "all done $?"'
run 'cat <<EOF
here $HOME is not expanded? no: ${0##*/}
	tab kept
EOF
cat <<"EOF"
quoted $HOME stays
EOF
cat <<-EOF
	leading tabs stripped
	EOF'
run 'echo out >f1; echo more >>f1; cat f1; cat <f1 | wc -l
exec 3>f2; echo fd3 >&3; echo again >&3; exec 3>&-; cat f2
ls nonexistent 2>/dev/null || echo "ls failed $?"
{ echo to stderr >&2; } 2>&1 | cat; echo x >/dev/null; cat <f1 >f3 && cat f3
set -C; echo clobber >f1 || echo "noclobber"; set +C; echo ok >f1; cat f1'
run 'printf "%s|%5d|%-4s|%x|%o|%c|%%\n" str 42 ab 255 8 zed
printf "%s\n" a b c; printf "%b\n" "tab\there"; printf "%.3s|%05.1f\n" abcdef 3.14159'
run 'echo "a b  c" | { read x y; echo "[$x][$y]"; }
IFS=: read -r p q r <<EOF
one:two:three:four
EOF
echo "$p/$q/$r"; IFS=,; set -- $(echo "x,y,z"); echo $# "$2"; unset IFS
while read line; do echo "line=$line"; done <<EOF
l1
l2
EOF'
run 'while getopts "ab:c" opt -a -b val -c rest; do echo "opt=$opt arg=${OPTARG:-}"; done
OPTIND=1; set -- -x -b; while getopts ":b:" o; do echo "o=$o ${OPTARG:-}"; done'
run 'test 5 -gt 3 && echo gt; [ abc = abc ] && echo eq; [ -z "" ] && echo empty
[ -n x -a 1 -eq 1 ] && echo and; [ ! -e /nonexistent ] && echo missing
mkdir d; [ -d d ] && echo dir; : >d/file; [ -f d/file -a -s d/file ] || echo "empty file"
rm -r d; [ -e d ] || echo removed'
run 'touch_() { : >"$1"; }; for f in b.txt a.txt c.log; do touch_ "$f"; done
echo *.txt; echo *.none; echo [ab].*; set -f; echo *.txt; set +f
case "file.tar.gz" in *.gz) echo gzip;; *) echo other;; esac
case x in a|b) echo ab;; [x-z]) echo xyz;; esac; rm -f *.txt *.log'
run 'umask 027; umask; : >m; ls -l m | cut -c1-10; rm m
eval "a=1; b=\$((a + 41))"; echo $b; cmd="echo evaluated"; eval $cmd
set -e; false || echo "or saves"; (set +e; false; echo "sub continues"); echo end'
run 'x=1; readonly x; (x=2) 2>/dev/null || echo "readonly"
unset y; echo ${y-unset}; y=; echo ${y-unset} ${y:-empty}
export E=exported; "$DASHBIN" -c "echo \$E"; env -i "$DASHBIN" -c "echo [\${E-none}]"'
run 'cd /tmp && cd - >/dev/null && echo back; cd /nonexistent; echo "cd $?"
type cd echo | sed "s/ is .*//"; command -v printf; alias ll="ls -l"; alias ll'
run 'f() { echo "${1:?missing}"; }; f present; f'
run 'echo ${unterminated'
run 'if then fi'
run 'exit 300'
run 'nosuchcommand; echo "status $?"; ./nofile; echo "status $?"'
run 'i=0; while :; do i=$((i+1)); [ $i -ge 1000 ] && break; continue; done; echo $i
for i in 1 2 3; do for j in a b; do [ $j = b ] && continue 2; echo $i$j; done; done
until [ ${k:=0} -ge 3 ]; do k=$((k+1)); done; echo $k'
run 'seq_() { i=0; while [ $i -lt $1 ]; do echo $i; i=$((i+1)); done; }
seq_ 200 | while read v; do [ $((v % 50)) = 0 ] && echo "v=$v"; done
s=; for w in $(seq_ 30); do s="$s$w,"; done; echo "${#s} $s"'
