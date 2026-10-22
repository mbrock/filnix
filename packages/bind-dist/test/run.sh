#!/bin/sh
# Unpacks the distribution and tests it in containers without Nix, as root
# and as an unprivileged user.
#
#   nix build .#bind-dist
#   packages/bind-dist/test/run.sh result debian:13 alpine:3
set -eu
tarball=$1
shift
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'chmod -R u+w "$work"; rm -rf "$work"' EXIT

tar -xJf "$tarball" -C "$work"
# Also checks that the tree does not depend on where it was unpacked.
mv "$work"/bind-*-filc-x86_64-linux "$work/my bind"

for image in "$@"; do
    for user in 0 65534; do
        podman run --rm --user $user:$user \
            -v "$work/my bind:/opt/my bind:ro" -v "$here:/t:ro" \
            "$image" sh /t/inside.sh "/opt/my bind"
    done
done
