#!/bin/sh
# Unpacks the root and tests it in containers without Nix, as root and as an
# unprivileged user. The tree is mounted read-only at a path with spaces,
# and at a second path to check that programs built with it are not tied to
# where it was.
#
#   nix build .#filroot
#   packages/filroot/test/run.sh result debian:13 ubuntu:22.04 alpine:3
#
# With FILROOT_TEST_NET=1, curl and git also fetch over HTTPS.
set -eu
tarball=$1
shift
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'chmod -R u+w "$work"; rm -rf "$work"' EXIT

tar -xJf "$tarball" -C "$work"
tree=$(echo "$work"/filroot-*)
root="/srv/my fil root/$(basename "$tree")"

for image in "$@"; do
    for user in 0 65534; do
        podman run --rm --user $user:$user --tmpfs /tmp:exec \
            -e FILROOT_TEST_NET="${FILROOT_TEST_NET-}" \
            -v "$tree:$root:ro" -v "$tree:/elsewhere:ro" -v "$here:/t:ro" \
            "$image" sh /t/inside.sh /t "$root" /elsewhere
    done
done
