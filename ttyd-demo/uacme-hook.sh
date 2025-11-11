#!/bin/sh
CHALLENGE_DIR="/var/www/html/.well-known/acme-challenge"
case "$1" in
    begin) mkdir -p "$CHALLENGE_DIR" ;;
    done|failed) rm -rf "$CHALLENGE_DIR" ;;
    *) printf '%s\n' "$3" > "$CHALLENGE_DIR/$2" ;;
esac
