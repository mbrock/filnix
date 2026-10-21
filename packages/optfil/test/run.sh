#!/bin/sh
# Unpacks the distribution and tests it in containers without Nix, as root
# and as an unprivileged user, with the tree mounted read-only at /opt/fil.
#
#   nix build .#optfil
#   packages/optfil/test/run.sh result debian:13 ubuntu:22.04 alpine:3
#
# With OPTFIL_TEST_NET=1, curl and git also fetch over HTTPS.
set -eu
tarball=$1
shift
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'chmod -R u+w "$work"; rm -rf "$work"' EXIT

tar -xJf "$tarball" -C "$work"

for image in "$@"; do
    for user in 0 65534; do
        podman run --rm --user $user:$user --tmpfs /tmp:exec \
            -e OPTFIL_TEST_NET="${OPTFIL_TEST_NET-}" \
            -v "$work/fil:/opt/fil:ro" -v "$here:/t:ro" \
            "$image" sh /t/inside.sh /t
    done
done
