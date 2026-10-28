# A deterministic xz workload: `bash xz.sh XZ` prints each command's
# exit status and stderr, and a checksum of its output, so two builds'
# transcripts can be compared byte for byte. liblzma's threaded encoder
# and decoder run at 1 to 8 threads on inputs of many small blocks
# (pthread mutexes and condition variables, worker threads handing
# blocks back in order), and the single-threaded coders, the BCJ and
# delta filters, the crc32, crc64 and sha256 checks, .lzma and raw
# streams, --list and --test, and errors on corrupt and truncated input
# run too. Run it in an empty directory.
set -u
xz=$1
export LC_ALL=C

# Text with long repeats and a pseudo-random binary tail, about 3 MB.
awk 'BEGIN {
  x = 12345
  for (i = 0; i < 40000; i++) {
    x = (x * 1103515245 + 12345) % 2147483648
    printf "line %d: %s %d\n", i, substr("the quick brown fox jumps over the lazy dog", 1 + x % 30), x % 977
  }
}' >text
awk 'BEGIN {
  x = 7
  for (i = 0; i < 400000; i++) {
    x = (x * 1103515245 + 12345) % 2147483648
    printf "%c", 32 + int(x / 65536) % 95
  }
}' >noise
cat text noise text >input
: >empty

run() {
  echo "### xz $*"
  (exec -a xz "$xz" "$@") >out 2>err && status=0 || status=$?
  cat err
  echo "### exit $status, stdout $(wc -c <out) bytes, sha256 $(sha256sum <out | cut -c1-16)"
}

for t in 1 2 3 4 8; do
  run -c -T$t --block-size=65536 -1 input
  cp out "blocks.T$t.xz"
done
cmp blocks.T2.xz blocks.T8.xz && echo "### T2 and T8 streams are identical"
run -c -T4 --block-size=200000 -6e --check=sha256 input
cp out sha.xz
run -c -T1 -0 --check=crc32 input
run -c -T1 -3 --check=crc64 input
cp out single.xz
run -c -T1 --format=lzma -2 text
cp out text.lzma
run -c -T1 --format=raw --lzma2=preset=1,dict=64KiB text
cp out text.raw
run -c -T2 --block-size=50000 --x86 --lzma2=preset=0 input
cp out bcj.xz
run -c -T1 --delta=dist=4 --lzma2=preset=1 noise
cp out delta.xz
run -c -T3 empty
cp out empty.xz

for t in 1 2 4 8; do
  run -dc -T$t blocks.T4.xz
  run -dc -T$t sha.xz
done
run -dc single.xz
run -dc text.lzma
run -dc --format=raw --lzma2=preset=1,dict=64KiB text.raw
run -dc bcj.xz
run -dc delta.xz
run -dc empty.xz
run -t blocks.T8.xz sha.xz single.xz
run -l blocks.T4.xz sha.xz empty.xz
run -lvv bcj.xz

# Errors: a flipped byte inside a block, a truncated stream, not xz.
head -c 30000 blocks.T4.xz >truncated.xz
{ head -c 20000 blocks.T4.xz; printf 'X'; tail -c +20002 blocks.T4.xz; } >corrupt.xz
run -dc -T1 corrupt.xz
run -dc -T4 corrupt.xz
run -dc -T4 truncated.xz
run -t text
run -dc --single-stream empty
run --bogus-option
