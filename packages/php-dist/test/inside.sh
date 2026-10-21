#!/bin/sh
# Runs inside a container without Nix: inside.sh DIST_DIR TEST_DIR.
# DIST_DIR is the unpacked distribution, TEST_DIR this directory.
set -eu
dist=$1
t=$2
php="$dist/bin/php"

echo "== $(. /etc/os-release && echo "$PRETTY_NAME"), uid $(id -u), dist at '$dist'"
test ! -e /nix || { echo "FAIL /nix exists"; exit 1; }
ls /lib*/ld-fil1* 2>/dev/null && { echo "FAIL host has a Fil-C loader"; exit 1; }

"$php" -v
"$php" "$t/smoke.php"

www=$(mktemp -d)
cp "$t/www/index.php" "$t/www/static.txt" "$www/"
chmod -R a+rX "$www"
# Opcache skips files changed in the last opcache.file_update_protection (2) seconds.
touch -t 202001010000 "$www"/*

echo "-- built-in server"
PHP_CLI_SERVER_WORKERS=4 "$php" -S 127.0.0.1:8080 -t "$www" >"$www.server.log" 2>&1 &
server=$!
"$php" "$t/http-check.php" 127.0.0.1:8080 || { cat "$www.server.log"; exit 1; }
kill $server

echo "-- php-fpm"
if [ "$(id -u)" = 0 ]; then
    # The shipped configuration: var/ in the distribution, workers as nobody.
    "$dist/bin/php-fpm" --nodaemonize &
    fpm=$!
    log="$dist/var/log/php-fpm.log"
else
    # An unprivileged user cannot write to the distribution; use a prefix.
    prefix=$(mktemp -d)
    mkdir -p "$prefix/var/log" "$prefix/var/run" "$prefix/etc/php-fpm.d"
    cp "$dist/etc/php-fpm.d/www.conf" "$prefix/etc/php-fpm.d/"
    "$dist/bin/php-fpm" --nodaemonize --prefix "$prefix" --fpm-config "$dist/etc/php-fpm.conf" &
    fpm=$!
    log="$prefix/var/log/php-fpm.log"
fi
"$php" "$t/fpm-check.php" 127.0.0.1 9000 "$www/index.php" || { cat "$log"; exit 1; }
kill -QUIT $fpm
wait $fpm || true
cat "$log"
if grep -Ei 'filc|panic|segfault|SIGSEGV|exited on signal|ERROR' "$log"; then
    echo "FAIL fpm log"
    exit 1
fi
echo "== all passed"
