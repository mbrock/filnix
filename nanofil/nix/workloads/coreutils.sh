# A deterministic GNU coreutils workload: `bash coreutils.sh BINDIR`
# runs BINDIR's programs and prints each command's exit status, stderr
# and output (or, when it is large, a checksum of it), so two builds'
# transcripts can be compared byte for byte. It covers sort (-n, -k,
# -t, -u, -s, -h, -V, -R with a fixed random source, --parallel,
# merging, a temporary-file spill), ls -l on a fixed tree with a fixed
# TZ, cp, mv, ln, rm, od, tr, wc, cut, join, seq, factor, the checksum
# programs, date -d, stat, dd and many smaller programs, in the C and
# C.UTF-8 locales. Nothing it prints depends on the builder: owners,
# inode and block numbers, directory sizes and timings are left out.
# Some commands stop with a Fil-C safety error in either build (seq and
# printf's floating formats reach gnulib's x87 control-word asm, yes
# into a pipe reaches libc's vmsplice): its wording, backtrace and pid
# differ between clang's and nanofil's code, so only its first words
# and the exit status are compared. Run it in an empty directory.
set -u
bin=$1
export LC_ALL=C TZ=UTC0
umask 022
here=$PWD

# norm: stderr without the build-dependent parts of a Fil-C error.
norm() {
  sed "s|$here|DIR|g; s|$bin/||g
       s|^\(filc safety error: [^:(]*([^)]*)\).*|\1|
       /^    (/d
       s|^\[[0-9]*\] filc panic|filc panic|"
}
run() {
  local prog=$1; shift
  echo "### $prog $*" | sed "s|$bin/||g"
  { ("$bin/$prog" "$@") >out 2>err; } 2>/dev/null && status=0 || status=$?
  norm <err
  if [ "$(wc -c <out)" -le 2000 ]; then
    sed "s|$here|DIR|g" out
  else
    echo "### $(wc -c <out) bytes, sha256 $(sha256sum <out | cut -c1-16)"
  fi
  echo "### exit $status"
}
# runi FILE PROG ARGS: run with stdin from FILE.
runi() { local f=$1; shift; run "$@" <"$f"; }

# Inputs: text, numbers, fields.
awk 'BEGIN {
  x = 12345
  for (i = 0; i < 30000; i++) {
    x = (x * 1103515245 + 12345) % 2147483648
    printf "%d\t%s %d\t%.3f\tk%d\n", x % 1000, substr("the quick brown fox jumps over the lazy dog", 1 + x % 37, 6), i, (x % 100000) / 7.0, x % 17
  }
}' >table
awk 'BEGIN { for (i = 0; i < 2000; i++) print (i * 7919) % 2003 }' >nums
printf '10K\n2M\n512\n1G\n3k\n0.5M\n' >human
printf 'v1.10\nv1.2\nv1.9.1\nv10\nv1.2a\nfoo-2.0\nfoo-10.0\n' >versions
printf 'b 2\na 1\nc 3\na 0\nb 1\n' >pairs
printf '1 one\n2 two\n4 four\n5 five\n' >left
printf '1 uno\n3 tres\n4 cuatro\n5 cinco\n6 seis\n' >right
printf 'h\xc3\xa9llo w\xc3\xb6rld \xe2\x82\xac\nna\xc3\xafve caf\xc3\xa9\n' >utf8
head -c 4096 /dev/zero | tr '\0' 'z' >zeros
awk 'BEGIN { for (i = 0; i < 256; i++) printf "%c", i }' >bytes

# sort
runi nums sort -n
run sort -t "$(printf '\t')" -k1,1n -k3,3gr table
run sort -k2,2 -s table
run sort -u -k5,5 table
run sort -h human
run sort -V versions
run sort -k1,1 -k2,2n pairs
run sort -R --random-source=table pairs
for p in 1 2 4 8; do run sort --parallel=$p -S 64K -T . -n -k4 table; done
sort -n nums >s1; sort -n -r nums >s2
run sort -m -n s1 nums
run sort -c -n s1
run sort -c -n s2
run sort -o sorted -k3,3n table
run sha256sum sorted
run sort -z -n nums
run sort --debug -k2,2 pairs
LC_ALL=C.UTF-8 run sort utf8 pairs

# ls -l on a fixed tree. Directory sizes and totals depend on the file
# system; -g -G drops owner and group.
mkdir -p tree/sub tree/.hidden
printf 'hello\n' >tree/a.txt
head -c 1234 table >tree/b.dat
: >tree/empty
printf '#!/bin/sh\n' >tree/run.sh
chmod 755 tree/run.sh
chmod 600 tree/b.dat
ln -s a.txt tree/link
ln tree/a.txt tree/hard
mkfifo tree/fifo
printf 'x\n' >tree/sub/inner
i=0
for f in tree/a.txt tree/b.dat tree/empty tree/run.sh tree/hard tree/sub/inner tree/fifo tree/sub tree/.hidden; do
  touch -d "2021-0$((i % 9 + 1))-1$i 1$i:0$i:3$i" "$f"; i=$((i + 1))
done
touch -h -d '2020-02-29 12:00:00' tree/link
# The tree's own entries (. and ..) carry the workload's run times.
nodirsize() {
  awk '/^d/ { $3 = "N" } /^total/ { next } $NF == "." || $NF == ".." { print $1, $NF; next } { print }'
}
for opts in "-l" "-la" "-lt" "-lS" "-lr" "-l --time-style=full-iso" "-l --time-style=+%Y%j" "-lR" "-li1"; do
  echo "### ls -gG ${opts#-l} tree"
  # shellcheck disable=SC2086
  "$bin/ls" -gG $opts tree 2>&1 | nodirsize | sed '/^[0-9]* /s/^[0-9]* /INODE /'
done
run ls -1F tree
run ls -A --color=always tree
run ls -d tree/*
TZ=EST5EDT,M3.2.0,M11.1.0 run ls -gG --time-style=long-iso tree/a.txt tree/b.dat

# stat, with fields that do not depend on the file system.
run stat --format='%n %s %a %A %F %h %y %Y' tree/a.txt tree/b.dat tree/empty tree/link tree/fifo
run stat -L --format='%n %s %F' tree/link
run stat --printf='%n:%s\n' tree/missing tree/a.txt

# cp, mv, ln, rm
mkdir work
run cp tree/a.txt work/c1
run cp -p tree/b.dat work/c2
run cp -r tree/sub work/sub2
run cp -a tree/link work/link2
run cp --backup=numbered tree/a.txt work/c1
run cp --backup=numbered tree/b.dat work/c1
run cp -n tree/b.dat work/c1
run cp tree/missing work/
run cp -r tree work/tree2
run mv work/c2 work/moved
run mv -b work/moved work/c1
run mv work/sub2 work/sub3
run ln -s ../tree/a.txt work/sym
run ln -sf c1 work/sym
run ln work/c1 work/hardc1
run ln work/c1 work/hardc1
run readlink work/sym work/link2
run rm work/hardc1
run rm work/nonexistent
run rm -f work/nonexistent
run rm -r work/tree2/sub
run rmdir work/sub3
run rm -rf work/sub3 work/tree2
( cd work && find . | sort | while read -r f; do
    if [ -f "$f" ] && [ ! -L "$f" ]; then echo "$f $(sha256sum <"$f" | cut -c1-16)"; else echo "$f"; fi
  done )
run stat --format='%n %s %a %h %F' work/c1 work/c1.~1~ work/c1.~2~ work/sym

# od, tr, wc, cut, join, paste, comm, uniq
run od -An -tx1 -v bytes
run od -c -N 64 bytes
run od -t d4 -t u2 -j 16 -N 48 bytes
run od -t f8 -t f4 -N 32 table
run od -t o2 -w8 -A x -N 40 table
run od -t a -N 32 bytes
run od -t f2 -N 4 bytes
runi table tr a-z A-Z
runi table tr -d '[:digit:]'
runi table tr -s ' \t' '\n'
runi left tr -c '[:alnum:]\n' '_'
runi utf8 tr '[:lower:]' '[:upper:]'
runi bytes tr -d '\000-\037'
runi left tr 'a-c' 'xyz-'
run wc table nums utf8
run wc -l -w -c -m -L utf8
LC_ALL=C.UTF-8 run wc -m -L utf8
runi table wc
run cut -f 2,4 table
run cut -d ' ' -f 2- left
run cut -c 3-7 table
run cut -b 1-3,8 --output-delimiter=: table
run cut -f 9 -s table
run cut -c 2-4 utf8
run join left right
run join -a 1 -a 2 -e NONE -o 0,1.2,2.2 left right
run join -v 2 left right
run join -t ' ' -1 1 -2 1 --nocheck-order right left
run paste left right
run paste -s -d ',' left
run comm left right
run comm -12 s1 s1
sort -n nums | uniq -c | sort -k1,1nr -k2,2n >uc
run head -5 uc
run uniq -d -c pairs
run uniq -f 1 -i pairs

# seq, factor, numfmt, expr, printf
run seq 10
run seq -w 7 3 40
run seq -s , 0.5 0.25 3
run seq -f '%08.3f' 1 0.5 3
run seq 1e3 1e3 5e3
run seq 18446744073709551610 18446744073709551615
run seq 1 0
run seq -- -3 -1
run factor 1 2 3 4 97 1000000007 600851475143 18446744073709551615 170141183460469231731687303715884105727
run factor 340282366920938463463374607431768211455
run factor abc -5
runi nums factor
run numfmt --to=si 1000 1500000 3500000000
run numfmt --from=iec --to=iec-i 1K 1.5M 2G
run numfmt --format='%10.2f' --from=auto 12K
run expr 7 \* 6 + 1
run expr length 'hello world'
run expr '(' 12 % 5 ')' '<' 3
run expr substr abcdef 2 3
run expr 999999999999999999999 + 1
run printf '%d %5.2f %x %o %e %s|%-6s|%c\n' 42 3.14159 255 8 12345.678 str ab x
run printf '%b' 'a\tb\n\x41\0102\n'
run printf '%q\n' "it's a \$test"
run printf '%.3s %*d %ld\n' abcdef 5 7 -9223372036854775808

# checksums
for p in md5sum sha1sum sha224sum sha256sum sha384sum sha512sum b2sum; do
  run $p table nums empty-missing
done
run cksum table nums
run cksum -a crc32b table
run cksum -a sha3 --length=256 table
run cksum -a blake2b -l 128 table
run sum table
run sum -s table
sha256sum table nums >sums
run sha256sum -c sums
printf 'x' >>nums
run sha256sum -c sums
run base64 bytes
run base32 left
run basenc --base16 left
base64 bytes >b64
run base64 -d b64
run md5sum --tag left
run b2sum -l 160 left

# date, with a fixed date
run date -d '2024-02-29 13:45:07' '+%Y-%m-%d %H:%M:%S %j %u %V %Z %s'
run date -u -d @1700000000
run date -d '2021-03-14 01:59:59 UTC + 1 second' +%s
TZ=EST5EDT,M3.2.0,M11.1.0 run date -d '2021-03-14 01:30' '+%F %T %Z %z'
TZ=EST5EDT,M3.2.0,M11.1.0 run date -d '2021-11-07 12:00 UTC' '+%F %T %Z'
run date -d 'next thursday' +%A
run date -d '2000-01-01 + 3 months 2 days' +%F
run date -d 'yesterday 2019-07-01' +%F
run date -R -d '1999-12-31 23:59:60'
run date --iso-8601=ns -d '2010-10-10 10:10:10.123456789'
run date -d 'not a date'
run date -r tree/a.txt '+%F %T'

# dd
run dd if=table of=dd1 bs=1000 count=7 skip=3 status=none
run dd if=table of=dd2 bs=512 conv=ucase,sync count=3 status=none
run dd if=bytes ibs=7 obs=13 status=none conv=swab
run dd if=zeros bs=1 skip=4000 count=200 status=none
run dd if=/nonexistent status=none
run sha256sum dd1 dd2

# Smaller programs
run head -c 100 table
run head -n -29990 table
run tail -n 3 table
run tail -c +118000 table
run tac left
run nl -ba -w3 left
run fold -w 7 left
run fmt -w 20 table
run pr -2 -t -w 60 left
run split -l 7000 -d table part-
run wc -l part-00 part-01 part-02 part-03 part-04
run csplit -s -f cs- left '/4/'
run cat cs-00 cs-01
run shuf -n 5 --random-source=table nums
run shuf -i 1-20 --random-source=nums
run truncate -s 10 work/c1
run stat --format='%s' work/c1
run touch -d '2001-02-03 04:05:06' work/t
run stat --format='%y' work/t
run chmod u=rwx,g=rx,o= work/t
run stat --format='%a %A' work/t
run chmod 4755 work/t
run stat --format='%a %A' work/t
run basename /usr/lib/libc.so.6 .6
run dirname /usr/lib/ a/b c
run realpath -m tree/../tree/./link nowhere/../x
run test -f tree/a.txt
run test 3 -gt 4
run [ -d tree -a -L tree/link ]
run env -i A=1 B=2 "$bin/printenv"
run echo -e 'a\tb\c'
echo "### yes abc | head -3"
{ "$bin/yes" abc 2>yerr | "$bin/head" -3; } 2>/dev/null
norm <yerr
run tsort pairs
run ptx left
run unexpand -a left
run expand -t 4 table
run true
run false
run sleep 0.01
run timeout 0.2 "$bin/sleep" 5
run nproc --ignore=10000
run printenv LC_ALL TZ
"$bin/seq" 3 | "$bin/tee" teeout >/dev/null
run cat teeout
run link left left2
run unlink left2
run mknod pipe2 p
run stat --format='%F' pipe2
run pathchk -p 'ok/name' 'bad\name'
run join --header left right
run sort --version
