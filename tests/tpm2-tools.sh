set -euo pipefail

# Everything, including D-Bus, belongs to this test. No hardware TPM is used.
mkdir state
swtpm socket --tpm2 --tpmstate dir="$PWD/state" \
  --server type=unixio,path="$PWD/tpm.sock" \
  --ctrl type=unixio,path="$PWD/tpm.sock.ctrl" \
  --flags not-need-init,startup-clear >swtpm.log 2>&1 &
simulator=$!
broker=""
cleanup() {
  if [ -n "$broker" ]; then kill "$broker" 2>/dev/null || true; fi
  kill "$simulator" 2>/dev/null || true
  wait || true
}
trap cleanup EXIT
for attempt in $(seq 1 100); do
  [ -S tpm.sock ] && break
  kill -0 "$simulator"
  sleep 0.05
done
test -S tpm.sock

tpm2-abrmd --session --tcti="swtpm:path=$PWD/tpm.sock" >abrmd.log 2>&1 &
broker=$!
export TPM2TOOLS_TCTI=tabrmd:bus_type=session
ready=0
for attempt in $(seq 1 100); do
  if tpm2_getrandom 32 -o random.bin >client.log 2>&1; then
    ready=1
    break
  fi
  if ! kill -0 "$broker"; then cat abrmd.log client.log; exit 1; fi
  sleep 0.05
done
if [ "$ready" != 1 ]; then cat abrmd.log client.log; exit 1; fi
test "$(wc -c <random.bin)" = 32

printf 'Fil-C TPM smoke test' >message.txt
tpm2_hash -g sha256 -o digest.bin message.txt >>client.log 2>&1
expected=$(sha256sum message.txt | cut -d ' ' -f 1)
actual=$(od -An -v -tx1 digest.bin | tr -d ' \n')
test "$actual" = "$expected"
tpm2_createprimary -C o -G ecc -c primary.ctx >>client.log 2>&1
tpm2_readpublic -c primary.ctx -f pem -o public.pem >>client.log 2>&1
grep -q 'BEGIN PUBLIC KEY' public.pem
tpm2_flushcontext -t >>client.log 2>&1
