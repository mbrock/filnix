# Perl XS modules that pass pointers to each other or back to Perl code:
# Encode's table encodings live in Encode::Byte and friends, which hand their
# encode_t pointers to Encode, and B::Deparse keys an op overlay by address.
{ pkgsFilc }:
pkgsFilc.runCommand "filc-perl-xs-pointers-check" { } ''
  ${pkgsFilc.perl}/bin/perl -MEncode -e '
    for my $e (qw(KOI8-R ISO-8859-5 cp1251 UTF-16LE latin1)) {
      my $s = "\x{43f}\x{440}\x{438}";
      $s = "abc" if $e eq "latin1";
      my $b = encode($e, $s);
      die "$e round trip" unless decode($e, $b) eq $s;
    }
    print "encode round trips ok\n";
  '
  # B::Deparse keys its op overlay by B'"'"'s encoded op addresses.
  ${pkgsFilc.perl}/bin/perl -MB::Deparse -e '
    my $t = B::Deparse->new->coderef2text(sub { my (%a) = @_; $a{x} });
    die $t unless $t =~ /my\(%a\) = \@_/;
    print "deparse ok\n";
  '
  touch $out
''
