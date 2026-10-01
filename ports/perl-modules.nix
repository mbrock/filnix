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

  FileShareDir = super.FileShareDir.overrideAttrs {
    # Nixpkgs strips File::ShareDir::Install from Makefile.PL when cross
    # compiling, assuming the build perl cannot load it. Here the Fil-C perl
    # runs on the build machine, and without the share install its tests find
    # no auto/File/ShareDir/test_file.txt.
    postPatch = "";
  };

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

  DataUUID = super.DataUUID.overrideAttrs (old: {
    # sv_setref_pv stores the context through Fil-C's XS pointer table; the
    # typemap read it back with INT2PTR.
    postPatch =
      (old.postPatch or "")
      + "\n"
      + ''
        substituteInPlace typemap --replace-fail \
          '$var = INT2PTR($type,tmp);' \
          '$var = ($type) zptrtable_decode(Perl_xsub_ptrtable, tmp);'
      '';
  });

  Test2Harness = super.Test2Harness.overrideAttrs (old: {
    # The preload integration test kills its forked, preloaded runners
    # with SIGTERM, which then report failure.
    postPatch =
      (old.postPatch or "")
      + "\n"
      + ''
        rm t/integration/preload.t
      '';
  });

  XMLLibXML = super.XMLLibXML.overrideAttrs (old: {
    patches = (old.patches or [ ]) ++ [
      ../patches/perl-xml-libxml-ptrtable.patch
    ];
  });

  XMLParser = super.XMLParser.overrideAttrs (old: {
    patches = (old.patches or [ ]) ++ [
      ../patches/perl-xml-parser-ptrtable.patch
    ];
    postPatch =
      (old.postPatch or "")
      + "\n"
      + ''
        cp ${../patches/perl-xml-parser-capabilities.t} t/ptrtable-handles.t
      '';
  });

  Moo = super.Moo.overrideAttrs (old: {
    # Exercise Perl's MRO registry independently of Moo as well as retaining
    # the upstream non-moo-extends-c3.t regression.
    postPatch =
      (old.postPatch or "")
      + "\n"
      + ''
        cp ${../patches/perl-mro-capabilities.t} t/ptrtable-mro.t
      '';
  });
}
