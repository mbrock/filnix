#!/bin/sh
# Runs inside a container without Nix: inside.sh TEST_DIR ROOT OTHER_ROOT.
# ROOT and OTHER_ROOT are the same read-only tree mounted at two paths.
set -eu
t=$1 root=$2 other=$3
export PATH="$root/bin:$PATH"
cd "$(mktemp -d)"

echo "== $(. /etc/os-release && echo "$PRETTY_NAME"), uid $(id -u), root at '$root'"
test ! -e /nix || { echo "FAIL /nix exists"; exit 1; }
test ! -e /opt/fil || { echo "FAIL /opt/fil exists"; exit 1; }

check() { # check NAME EXPECTED COMMAND...: COMMAND's output must contain EXPECTED.
    name=$1 expected=$2
    shift 2
    if out=$("$@" 2>&1) && case $out in *"$expected"*) true ;; *) false ;; esac; then
        echo "ok   $name"
    else
        echo "FAIL $name: $out"
        exit 1
    fi
}

echo "-- compiler"
printf '#include <stdio.h>\nint main(void) { puts("hello from filcc"); return 0; }\n' > hello.c
filcc -O2 -o hello hello.c
check "C hello" "hello from filcc" fil-run ./hello
check "C hello from the root's bash" "hello from filcc" bash -c ./hello
check "C uses the loader through descriptor 987" "/proc/self/fd/987/lib/ld-fil1-x86_64.so" readelf -l hello
check "C hello with the root elsewhere" "hello from filcc" "$other/bin/fil-run" ./hello
if out=$(./hello 2>&1); then
    echo "FAIL compiled program ran without descriptor 987: $out"
    exit 1
fi
echo "ok   compiled program needs descriptor 987 ($out)"
fil++ -O2 -o hellocc "$t/hello.cc"
check "C++ hello" "caught fil=2 sum=500500" fil-run ./hellocc
filcc -O2 -o libs "$t/libs.c" -lz -lcrypto
check "zlib, OpenSSL, iconv, locale" "libs ok" fil-run ./libs
filcc -c -o hello.o hello.c && filcc -o hello2 hello.o
check "separate link" "hello from filcc" fil-run ./hello2
printf 'int twice(int x) { return 2 * x; }\n' > twice.c
printf '#include <stdio.h>\nint twice(int);\nint main(void) { printf("%%d\\n", twice(21)); }\n' > use.c
filcc -shared -fPIC -o libtwice.so twice.c
filcc -o use use.c -L. -ltwice -Wl,-rpath,"$PWD"
check "shared library" "42" fil-run ./use
check pkg-config "-lssl" pkg-config --cflags --libs zlib openssl libcurl sqlite3
filcc -o libs2 "$t/libs.c" $(pkg-config --cflags --libs zlib libcrypto)
check "pkg-config build" "libs ok" fil-run ./libs2
printf 'all: hi\n\t./hi\nhi: hello.c\n\tfilcc -o $@ $<\n' > Makefile
check "make builds and runs" "hello from filcc" make

echo "-- memory safety"
filcc -O2 -o unsafe "$t/unsafe.c"
for kind in oob uaf; do
    if out=$(fil-run ./unsafe $kind 2>&1); then
        echo "FAIL $kind was not stopped: $out"
        exit 1
    fi
    case $out in
    *"filc panic"*) echo "ok   $kind panics: $(echo "$out" | grep -m1 'filc safety error')" ;;
    *) echo "FAIL $kind: $out"; exit 1 ;;
    esac
done

echo "-- programs"
check bash "5.3" bash -c 'echo $BASH_VERSION'
check "bash runs host programs" "hello.c" bash -c '/bin/ls'
check ls "hello.c" ls
check grep "stdio" grep -o stdio hello.c
check sed "hullo" sh -c 'echo hello | sed s/e/u/'
check gawk "6" gawk 'BEGIN { print 2 * 3 }'
check find "./hello.c" find . -name hello.c
check diff "+bye" sh -c 'echo hi > a; echo bye > b; diff -u a b || true'
check sha256sum "e3b0c442" sh -c 'printf "" | sha256sum'
for z in gzip xz zstd bzip2; do
    check "tar $z" "hello.c" sh -c "tar -cf - hello.c | $z | $z -d | tar -tf -"
done
check jq "3" sh -c 'echo "[1,2]" | jq "add"'
check sqlite3 "42" sqlite3 :memory: "select 6 * 7"
check lua "Lua" lua -e 'print(_VERSION)'
check python3 "e015" python3 -c 'import hashlib, sqlite3, ssl, zlib; print(hashlib.sha256(b"fil").hexdigest()[:4])'
check "python3 prefix" "$root" python3 -c 'import sys; print(sys.prefix)'
check "python3 subprocess" "hello.c" python3 -c 'import subprocess; print(subprocess.run(["ls"], capture_output=True, text=True).stdout)'
check perl "olleh" perl -e 'print scalar reverse "hello"'
check "perl module" "c9bfff4b" perl -MDigest::MD5=md5_hex -e 'print md5_hex("fil")'
check m4 "yes" sh -c 'echo "define(x, yes)x" | m4'
check bison "GNU Bison" bison --version
check flex "flex" flex --version
check file "C source" file hello.c
check which "$root/bin/bash" which bash
check iconv "351" sh -c 'printf "caf\303\251\n" | iconv -f UTF-8 -t ISO-8859-1 | od -c'
check "no environment" "C source" env -i "$root/bin/file" hello.c
check openssl "OpenSSL 3" openssl version
check "openssl dgst" "SHA2-256" sh -c 'echo hi | openssl dgst -sha256'
check curl "curl 8" curl --version
check "curl file:" "hello from filcc" curl -s "file://$PWD/hello.c"
check "script in bin" "-lcurl" curl-config --libs
if [ -n "${FILROOT_TEST_NET-}" ]; then
    check "curl https:" "200" curl -sS -o /dev/null -w '%{http_code}' https://example.com/
    check "git https:" "HEAD" git ls-remote https://github.com/mbrock/filnix HEAD
fi
check ssh "OpenSSH" ssh -V
check rsync "rsync  version" rsync --version
check nano "nano" nano --version
check tmux "tmux" tmux -V
check less "less" less --version
export HOME=$PWD
git config --global user.email t@example.com
git config --global user.name t
git init -q repo
cp hello.c repo/
git -C repo add hello.c
check "git commit" "first" sh -c 'git -C repo commit -q -m first && git -C repo log --oneline'
check "git shell alias" "via sh" git -c alias.hi='!echo via sh' hi
echo "all ok"
