use strict;
use warnings;
use Test::More;
use XML::Parser::Expat;

my $document = <<'XML';
<!DOCTYPE root [
  <!ENTITY outer SYSTEM "outer.ent">
  <!ENTITY inner SYSTEM "inner.ent">
]><root>before&outer;after</root>
XML

# Both the child handle passed to Do_External_Parse and the restored parent
# handle must be encoded. Only checking ordinary ParseString misses these.
for my $broken (0, 1) {
    my $parser = XML::Parser::Expat->new;
    my $parent = $parser->{Parser};
    my ($text, @external, @finished) = ('');
    $parser->setHandlers(
        ExternEnt => sub {
            my ($xp, $base, $system) = @_;
            push @external, $system;
            return '<nested>&inner;</nested>' if $system eq 'outer.ent';
            return $broken ? '<unclosed>' : 'inside';
        },
        ExternEntFin => sub { push @finished, $_[0]->{Parser} },
        Char => sub { $text .= $_[1] },
    );
    my $ok = eval { $parser->parse($document); 1 };
    my $error = $@;
    is_deeply(\@external, ['outer.ent', 'inner.ent'], 'nested external entities resolved');
    is(scalar @finished, 2, 'both external parsers cleaned up');
    isnt($finished[0], $parent, 'inner cleanup restores the outer entity parser');
    is($finished[1], $parent, 'outer cleanup restores the document parser');
    is($parser->{Parser}, $parent, 'parent handle survives external parsing');
    if ($broken) {
        ok(!$ok, 'malformed external entity raises a Perl exception');
        like($error, qr/error in processing external entity reference/,
            'parent parser reports external entity failure');
    } else {
        ok($ok, 'external parse succeeds');
        is($text, 'beforeinsideafter', 'content continues after external parser cleanup');
    }
    $parser->release;
    undef $parser; # ParserFree must decode the restored handle too.
    pass('parent parser released and destroyed');
}

# Exercise both the Encinfo read in unknownEncoding and its T_ENCOBJ
# destructor. Reloading catches mismatched producer/consumer table usage.
for (1 .. 2) {
    my $name = XML::Parser::Expat::load_encoding('windows-1252');
    isa_ok($XML::Parser::Expat::Encoding_Table{$name}, 'XML::Parser::Encinfo');
    my $parser = XML::Parser::Expat->new(ProtocolEncoding => 'windows-1252');
    my $text = '';
    $parser->setHandlers(Char => sub { $text .= $_[1] });
    $parser->parse("<root>\x80\x91\x94</root>");
    is($text, "\x{20ac}\x{2018}\x{201d}", 'custom encoding maps asymmetric code points');
    $parser->release;
    undef $parser;
    delete $XML::Parser::Expat::Encoding_Table{$name};
    pass('Encinfo destroyed through the custom typemap');
}
done_testing;
