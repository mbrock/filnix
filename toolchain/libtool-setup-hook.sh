# Run after patching/autoreconf, including configure scripts in bundled projects.
# The selected host compiler must be this wrapper: merely using Fil-C as a
# build-time tool must not alter a native compiler's configure probes.
filcFixLibtoolSymbols() {
    if [[ ${NIX_CC-} == @out@ ]]; then
        @python@ @patcher@ "${configureScript-}"
    fi
}

preConfigureHooks+=(filcFixLibtoolSymbols)
