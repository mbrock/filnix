#!/bin/sh
# Runs inside a container without Nix: inside.sh DIST_DIR. Signs a zone,
# serves it with an authoritative named, resolves through a validating
# named that forwards to it, and drives both with dig, nsupdate and rndc.
set -eu
dist=$1
b=$dist/bin

echo "== $(. /etc/os-release && echo "$PRETTY_NAME"), uid $(id -u), dist at '$dist'"
test ! -e /nix || { echo "FAIL /nix exists"; exit 1; }
ls /lib*/ld-fil1* 2>/dev/null && { echo "FAIL host has a Fil-C loader"; exit 1; }

"$b/named" -V | head -3
w=$(mktemp -d)
cd "$w"
mkdir auth res

cat > example.test.in <<'EOF'
$TTL 300
@    IN SOA ns1.example.test. admin.example.test. ( 1 3600 600 86400 300 )
     IN NS  ns1.example.test.
ns1  IN A   127.0.0.1
www  IN A   192.0.2.10
EOF
zsk=$("$b/dnssec-keygen" -q -a ECDSAP256SHA256 -K auth example.test)
ksk=$("$b/dnssec-keygen" -q -a ECDSAP256SHA256 -f KSK -K auth example.test)
cat "auth/$zsk.key" "auth/$ksk.key" >> example.test.in
"$b/dnssec-signzone" -q -o example.test -f auth/example.test.db example.test.in "auth/$zsk" "auth/$ksk"
"$b/named-checkzone" example.test auth/example.test.db
anchor=$(grep -v "^;" "auth/$ksk.key" | awk '{for (i = 7; i <= NF; i++) printf "%s", $i}')

"$b/rndc-confgen" -a -c rndc.key -k rndc-key
"$b/tsig-keygen" upd > upd.key
common="pid-file \"$w/%s/pid\"; session-keyfile \"$w/%s/session.key\";
  listen-on-v6 { none; }; dnssec-validation %s;"
cat > auth.conf <<EOF
options { directory "$w/auth"; listen-on port 5301 { 127.0.0.1; };
  $(printf "$common" auth auth no) recursion no; allow-transfer { 127.0.0.1; }; };
include "$w/rndc.key";
include "$w/upd.key";
controls { inet 127.0.0.1 port 9501 allow { 127.0.0.1; } keys { rndc-key; }; };
zone "example.test" { type primary; file "example.test.db"; allow-update { key upd; }; };
EOF
cat > res.conf <<EOF
options { directory "$w/res"; listen-on port 5302 { 127.0.0.1; };
  $(printf "$common" res res yes) recursion yes; query-source address 127.0.0.1; };
trust-anchors { example.test. static-key 257 3 13 "$anchor"; };
include "$w/rndc.key";
controls { inet 127.0.0.1 port 9502 allow { 127.0.0.1; } keys { rndc-key; }; };
zone "example.test" { type forward; forward only; forwarders { 127.0.0.1 port 5301; }; };
EOF
"$b/named-checkconf" auth.conf
"$b/named-checkconf" res.conf

"$b/named" -g -n 2 -c "$w/auth.conf" > auth.log 2>&1 &
"$b/named" -g -n 2 -c "$w/res.conf" > res.log 2>&1 &
for i in 1 2 3 4 5 6 7 8 9 10; do
    grep -q running auth.log && grep -q running res.log && break
    sleep 1
done

check() {
    printf '%s: ' "$1"
    shift
    out=$("$@" 2>&1) || { echo "FAIL"; echo "$out"; cat auth.log res.log; exit 1; }
    echo "$out" | head -1
}
dig() { "$b/dig" @127.0.0.1 "$@"; }
has() { pattern=$1; shift; "$@" | grep -e "$pattern"; }
check "authoritative" has '^192.0.2.10$' dig -p 5301 +norec +short www.example.test
check "validated (ad)" has 'flags: qr rd ra ad' dig -p 5302 +dnssec www.example.test
check "NXDOMAIN" has 'status: NXDOMAIN' dig -p 5302 nope.example.test
check "TCP" has '^192.0.2.10$' dig -p 5302 +tcp +short www.example.test
check "AXFR" has 'RRSIG' dig -p 5301 example.test AXFR
printf 'server 127.0.0.1 5301\nzone example.test\nupdate add new.example.test 300 A 198.51.100.7\nsend\n' |
    "$b/nsupdate" -k upd.key
check "nsupdate" has '^198.51.100.7$' dig -p 5301 +norec +short new.example.test
check "rndc status" "$b/rndc" -k rndc.key -s 127.0.0.1 -p 9502 status
check "rndc flush" "$b/rndc" -k rndc.key -s 127.0.0.1 -p 9502 flush
check "host" has 192.0.2.10 "$b/host" -p 5302 www.example.test 127.0.0.1

"$b/rndc" -k rndc.key -s 127.0.0.1 -p 9501 stop
"$b/rndc" -k rndc.key -s 127.0.0.1 -p 9502 stop
wait
if grep -Ei 'filc|panic|assert|critical' auth.log res.log; then
    echo "FAIL named log"
    exit 1
fi
echo "== all passed"
