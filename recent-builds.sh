#!/usr/bin/env bash
# Query recent Nix builds from the Nix database
# Only shows paths that were actually built from derivations (not just copied files/scripts)

set -euo pipefail

HOURS="${1:-24}"
PATTERN="${2:-}"

SECONDS=$((HOURS * 3600))

if [ -n "$PATTERN" ]; then
    QUERY="SELECT datetime(registrationTime, 'unixepoch') as time, path
           FROM ValidPaths
           WHERE registrationTime > (strftime('%s', 'now') - $SECONDS)
             AND path LIKE '%${PATTERN}%'
             AND path NOT LIKE '%.drv'
             AND deriver IS NOT NULL
           ORDER BY registrationTime DESC;"
else
    QUERY="SELECT datetime(registrationTime, 'unixepoch') as time, path
           FROM ValidPaths
           WHERE registrationTime > (strftime('%s', 'now') - $SECONDS)
             AND path NOT LIKE '%.drv'
             AND deriver IS NOT NULL
           ORDER BY registrationTime DESC
           LIMIT 100;"
fi

nix-shell -p sqlite --run "sqlite3 /nix/var/nix/db/db.sqlite \"$QUERY\"" 2>/dev/null | \
    column -t -s '|'

