# SerenityOS typed syscalls (spike). libpizlo-spike.nix inserts these lines
# into generate_pizlonated_forwarders.rb before it writes its outputs.
addSig nil, "long", "zsys_serenity_getpid"
addSig nil, "long", "zsys_serenity_write", "int", "filc_ptr", "size_t"
addSig nil, "long", "zsys_serenity_read", "int", "filc_ptr", "size_t"
addSig nil, "long", "zsys_serenity_open", "filc_ptr"
addSig nil, "long", "zsys_serenity_readlink", "filc_ptr"
addSig nil, "long", "zsys_serenity_stat", "filc_ptr"
addSig nil, "long", "zsys_serenity_getsockname", "filc_ptr"
