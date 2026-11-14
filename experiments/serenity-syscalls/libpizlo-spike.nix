# libpizlo with the SerenityOS typed-syscall natives from runtime/, emulated
# on Linux. Build: nix build --impure -f experiments/serenity-syscalls/libpizlo-spike.nix
{
  filcc ? (builtins.getFlake (toString ../..)).packages.x86_64-linux.filcc,
}:
filcc.components.libpizlo.overrideAttrs (old: {
  pname = "libpizlo-serenity-spike";
  postPatch = (old.postPatch or "") + ''
    cp ${./generated/SyscallParams.h} libpas/src/libpas/SyscallParams.h
    cp ${./runtime/filc_serenity_marshal.h} libpas/src/libpas/filc_serenity_marshal.h
    cp ${./runtime/filc_serenity_spike.c} libpas/src/libpas/filc_serenity_spike.c
    echo '#include "filc_serenity_spike.c"' >> libpas/src/libpas/filc_runtime.c
    awk '/^case ARGV\[0\]/ { while ((getline line < "${./runtime/addsig.rb}") > 0) print line } { print }' \
      libpas/src/libpas/generate_pizlonated_forwarders.rb > forwarders.rb
    mv forwarders.rb libpas/src/libpas/generate_pizlonated_forwarders.rb
  '';
})
