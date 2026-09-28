# Fil-C keeps each function's source file path for stack traces outside the
# debug sections, so code inlined from a dependency's headers leaves that
# dependency's -dev output in the binary and hence in the runtime closure (and
# trips outputChecks). Those strings only label stack-trace frames; rewrite
# them like remove-references-to does.
filcStripHeaderReferences() {
    [ -e "$prefix" ] || return 0
    local dep devs=()
    for dep in ${pkgsHostTarget+"${pkgsHostTarget[@]}"} ${pkgsHostHost+"${pkgsHostHost[@]}"}; do
        case "$dep" in
            */nix/store/*-dev) [ "$dep" != "$prefix" ] && devs+=("$dep") ;;
        esac
    done
    ((${#devs[@]})) || return 0
    local args=() f
    for dep in "${devs[@]}"; do args+=(-t "$dep"); done
    while IFS= read -r -d '' f; do
        if head -c 4 "$f" 2>/dev/null | grep -q $'\x7fELF'; then
            @removeReferencesTo@ "${args[@]}" "$f"
        fi
    done < <(find "$prefix" -type f -print0)
}
fixupOutputHooks+=(filcStripHeaderReferences)
