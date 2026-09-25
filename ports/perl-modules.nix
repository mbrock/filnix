# Fixes for CPAN modules in the Fil-C Perl package set (an overrideScope
# overlay, see perl5 in ../ports.nix).
self: super: {
  InlineC = super.InlineC.overrideAttrs (old: {
    # This test's own typemap stores a pointer in an IV with a C cast and
    # recovers it with INT2PTR, which Fil-C rightly refuses to dereference.
    postPatch =
      (old.postPatch or "")
      + "\n"
      + ''
        rm t/07typemap_multi.t
      '';
  });

  CompressBzip2 = super.CompressBzip2.overrideAttrs (old: {
    # Objects are made with sv_setref_iv(PTR2IV(...)) but read back through
    # T_PTROBJ, which decodes Fil-C's XS pointer table. Use the table both
    # ways.
    postPatch =
      (old.postPatch or "")
      + "\n"
      + ''
        sed -i Bzip2.xs \
          -e 's/sv_setref_iv( *\([^,]*\), *\([^,]*\), *PTR2IV(obj) *)/sv_setref_pv(\1, \2, (void *) obj)/' \
          -e 's/INT2PTR(bzFile\*, *tmp)/(bzFile *) zptrtable_decode(Perl_xsub_ptrtable, tmp)/'
        ! grep -n 'PTR2IV(obj)\|INT2PTR(bzFile' Bzip2.xs
      '';
  });

  AlienBuild = super.AlienBuild.overrideAttrs (old: {
    # The Fil-C runtime refuses handlers for SIGSEGV (and SIGBUS, SIGILL,
    # SIGFPE, SIGTRAP), so this subtest's self-inflicted SEGV kills perl.
    postPatch =
      (old.postPatch or "")
      + "\n"
      + ''
        sed -i "/subtest 'with_subtest SEGV' => sub {/a\\  skip_all 'Fil-C reserves SIGSEGV';" t/test_alien.t
        grep -q "Fil-C reserves SIGSEGV" t/test_alien.t
      '';
  });
}
