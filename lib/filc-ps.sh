# filc-ps: is every running process on this machine Fil-C, or an allowed
# native exception?
#
#   sudo filc-ps               # a table of processes; exit 1 if one is not allowed
#   ... --allow FILE           # store paths also allowed, one per line, for
#                              # a machine whose Nix database lacks the
#                              # exceptions' closures (finix's test VM)
#
# A process is Fil-C if it maps libpizlo, the Fil-C runtime: the loader
# maps it into every Fil-C program and nothing else loads it. A native
# process is allowed if its program is in the closure of a native exception
# (`roots`, which lib/filc-system.nix writes above this text) or is a setuid
# wrapper (from pkgsStatic). Kernel threads map nothing and are skipped.
# Other users' maps are readable only by root; without them the exit
# status is 2.
set -uo pipefail

declare -A allowed=()
if [ "${1:-}" = --allow ]; then
  while read -r p; do allowed[$p]=1; done <"$2"
fi
for r in "${roots[@]}"; do
  [ -e "$r" ] || continue
  # The closure, where the Nix database has the path; else the path itself.
  closure=$(nix-store -qR "$r" 2>/dev/null) || closure=$r
  while read -r p; do allowed[$p]=1; done <<<"$closure"
done

filc=0 native=0 bad=0 unknown=0
rows=()
for d in /proc/[0-9]*; do
  pid=${d#/proc/}
  [ "$pid" = $$ ] && continue
  if ! maps=$(cat "$d/maps" 2>/dev/null); then
    if [ -e "$d" ]; then
      rows+=("? $pid maps unreadable; run as root")
      unknown=$((unknown + 1))
    fi
    continue
  fi
  [ -n "$maps" ] || continue # a kernel thread, or exiting
  exe=$(readlink "$d/exe" 2>/dev/null) || exe='?'
  storePath=${exe%"${exe#/nix/store/*/}"}
  storePath=${storePath%/}
  if grep -q libpizlo <<<"$maps"; then
    rows+=("Fil-C $pid $exe")
    filc=$((filc + 1))
  elif [ -n "${allowed[$storePath]:-}" ] || [[ $exe == /run/wrappers/* ]]; then
    rows+=("native $pid $exe")
    native=$((native + 1))
  else
    rows+=("NATIVE $pid $exe  <- not an allowed native exception")
    bad=$((bad + 1))
  fi
done

printf '%s\n' "${rows[@]}" | sort -k1,1 -k2,2n | while read -r kind pid rest; do
  printf '%-7s %7s  %s\n' "$kind" "$pid" "$rest"
done
echo "$filc Fil-C, $native allowed native, $bad not allowed, $unknown unreadable"
[ "$bad" -eq 0 ] || exit 1
[ "$unknown" -eq 0 ] || exit 2
