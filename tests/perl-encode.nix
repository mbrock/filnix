# Table encodings live in Encode::Byte and friends, separate XS modules that
# hand their encode_t pointers to Encode itself.
{ pkgsFilc }:
pkgsFilc.runCommand "filc-perl-encode-check" { } ''
  ${pkgsFilc.perl}/bin/perl -MEncode -e '
    for my $e (qw(KOI8-R ISO-8859-5 cp1251 UTF-16LE latin1)) {
      my $s = "\x{43f}\x{440}\x{438}";
      $s = "abc" if $e eq "latin1";
      my $b = encode($e, $s);
      die "$e round trip" unless decode($e, $b) eq $s;
    }
    print "encode round trips ok\n";
  '
  touch $out
''
