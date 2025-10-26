# Setup hook to make autotools recognize the filc ABI
# This patches config.sub to accept x86_64-unknown-linux-filc
# Must run AFTER updateAutotoolsGnuConfigScriptsPhase

updateAutotoolsFilcPhase() {
    if [ -n "${dontUpdateAutotoolsFilc-}" ]; then return; fi

    for file in $(find . -type f -name config.sub); do
        echo "Patching $file to recognize filc ABI"
        
        # The config.sub script validates the kernel-os combination in a case statement
        # around line 1830. We need to add 'linux-filc*-' alongside linux-musl*-, etc.
        
        sed -i 's/linux-musl\*-/linux-filc*- | linux-musl*-/' "$file"
    done
}

# Run after preConfigurePhases (which includes updateAutotoolsGnuConfigScriptsPhase)
appendToVar preConfigurePhases updateAutotoolsFilcPhase
