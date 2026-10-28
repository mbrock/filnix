# A deterministic GNU sed workload: `bash sed.sh SED` prints each
# command's stdout, stderr and exit status, so two builds' transcripts
# can be compared byte for byte. It covers BRE and ERE matching
# (gnulib's regex, back-references, intervals, classes), s///
# flags, y, addresses and ranges, the hold space, branches, -n, -s, -z,
# in-place editing with a backup, w files, multibyte text under
# C.UTF-8 and errors. Run it in an empty directory.
set -u
sed=$1
export LC_ALL=C.UTF-8
seq 1 200 >nums
printf '%s\n' 'The quick brown fox' 'jumps over the lazy dog.' '' \
  'Grüße, мир → 世界' 'tab	separated	fields' 'a,b,,c' \
  'foo123bar456' '   leading and trailing   ' 'ALL CAPS line' \
  'email: user@example.com, other@test.org' >text
for i in $(seq 1 300); do echo "line $i: $((i * 7919 % 1000)) $((i % 13))"; done >big

run() {
  echo "### sed $*"
  (exec -a sed "$sed" "$@") 2>&1 && status=0 || status=$?
  echo "### exit $status"
}

run -n '5,10p;/^1[0-9]7$/p;$=' nums
run 's/o/0/g;s/\(qu\)\(ick\)/\2\1/' text
run -E 's/([a-z]+)@([a-z]+)\.(com|org)/<\2:\1>/g' text
run -E 's/[0-9]{2,3}/[&]/2;s/^ +| +$//g' text
run 's/[[:upper:]]\+/\L&/g;s/\b\w/\u&/g' text
run 's/x*/-/g' text
run 'y/abcdefghij/ABCDEFGHIJ/' text
run -n '/fox/,/lazy/{=;p}' text
run '1~3d;$!N;s/\n/ + /' nums
run -n 'h;n;G;p' nums
run ':a;N;$!ba;s/\n/,/g' nums
run '/^$/d;s/\(.\)\(.\)/\2\1/' text
run -E ':x;s/^([^,]*),,/\1,<empty>,/;tx' text
run -n '/line 1[0-9]:/{s/line \([0-9]*\): \([0-9]*\) \([0-9]*\)/\3 \2 \1/;p}' big
run -E 's/^line ([0-9]+): ([0-9]+) ([0-9]+)$/\2/' big
run -n '$!{h;d};x;G;p' text
run 's/./&\n/3;P;D' text
run -s -n '$p' nums text big
run -z 's/\n/|/g' text
run '0~50a\
--- fifty ---' nums
run '3i\inserted' text
run '/dog/c\changed' text
run -n 'l 20' text
run 's/[^[:alnum:] ]//g;s/ \+/ /g' text
run -E 's/(.)(.)(.)(.)(.)(.)(.)(.)(.)(.)/\9\8\7\6\5\4\3\2\1/' text
run 's/\(a\|b\)\{2\}/<&>/g' text
run -E 's/(ab|a)(bc|c)?/[\1|\2]/g' text
run 's/е/E/g;s/世/W/' text
run -n '/мир/=' text
run 'w out.txt' text
cat out.txt
cp big inplace
run -i.bak 's/: \([0-9]*\) /: <\1> /;10q' inplace
cat inplace
cmp big inplace.bak && echo backup kept
run -n '/[0-9]\{3\} 1[02]$/{s/ /_/gp}' big
run 's/\([0-9]\)\1/<\1\1>/g' big
run -E 's/^(line )(1|2)(0+):/\1\3\2:/' big
run 'unknown command' text
run 's/unterminated' text
run -E 's/(/x/' text
run 'p' /nonexistent
run --posix -n '/a\{1,2\}/p' text
run --version
