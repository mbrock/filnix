#!/bin/sh
# Unpacks the distribution and tests it in containers without Nix, as root
# and as an unprivileged user.
#
#   nix build .#php-dist
#   packages/php-dist/test/run.sh result debian:13 ubuntu:22.04 alpine:3
#
# The same works for php74-dist, which runs smoke74.php instead of smoke.php.
set -eu
tarball=$1
shift
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'chmod -R u+w "$work"; rm -rf "$work"' EXIT

tar -xJf "$tarball" -C "$work"
# Also checks that the tree does not depend on where it was unpacked.
mv "$work"/php-*-filc-x86_64-linux "$work/my php"

for image in "$@"; do
    for user in 0 65534; do
        podman run --rm --user $user:$user \
            -v "$work/my php:/opt/my php" -v "$here:/t:ro" \
            "$image" sh /t/inside.sh "/opt/my php" /t
    done
done
