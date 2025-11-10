#!/usr/bin/env perl
# Perl + C Integration with Fil-C Memory Safety
# Demonstrates C libraries (JSON, XML, SQLite, zlib) with memory safety

use strict;
use warnings;
use JSON::XS;
use XML::LibXML;
use DBI;
use Compress::Zlib;

print "=== Fil-C: Memory-Safe Perl + C Integration ===\n\n";

# 1. JSON (C library: JSON::XS)
print "1. JSON::XS - Fast C-based JSON Parser\n";
my $data = {
    project => "Fil-C",
    features => ["Memory Safety", "GIMSO", "No unsafe keyword"],
    performance => "1.5x-4x overhead",
};
my $json = JSON::XS->new->encode($data);
print "   Encoded: ", substr($json, 0, 60), "...\n";
print "   ✓ Fast C JSON parser with memory safety\n\n";

# 2. XML (C library: libxml2)
print "2. XML::LibXML - libxml2 C Library\n";
my $xml = '<packages><pkg>JSON-XS</pkg><pkg>DBD-SQLite</pkg></packages>';
my $doc = XML::LibXML->new->parse_string($xml);
my @pkgs = map { $_->textContent } $doc->findnodes('//pkg');
print "   Parsed packages: ", join(", ", @pkgs), "\n";
print "   ✓ XML parsing safe from buffer overflows\n\n";

# 3. SQLite (C library: SQLite + DBD driver)
print "3. DBI + DBD::SQLite - Memory-Safe Database\n";
my $dbh = DBI->connect("dbi:SQLite:dbname=:memory:", "", "", {RaiseError => 1});
$dbh->do('CREATE TABLE libs (name TEXT, language TEXT)');
$dbh->do("INSERT INTO libs VALUES (?, ?)", undef, "libxml2", "C");
$dbh->do("INSERT INTO libs VALUES (?, ?)", undef, "zlib", "C");
my ($count) = $dbh->selectrow_array('SELECT COUNT(*) FROM libs');
print "   Inserted $count C libraries into SQLite\n";
print "   ✓ SQL operations safe from memory corruption\n\n";

# 4. Compression (C library: zlib)
print "4. Compress::Zlib - Fast Compression\n";
my $text = "Fil-C provides complete memory safety for C and C++. " x 10;
my $compressed = compress($text);
my $ratio = sprintf("%.1f%%", 100 * length($compressed) / length($text));
print "   Original: ", length($text), " bytes\n";
print "   Compressed: ", length($compressed), " bytes ($ratio)\n";
print "   ✓ Compression safe from buffer exploits\n\n";

$dbh->disconnect;

print "═══════════════════════════════════════════════════\n";
print "All C libraries executed with Fil-C memory safety:\n";
print "  • No buffer overflows\n";
print "  • No use-after-free\n";
print "  • No type confusion\n";
print "  • GIMSO: Garbage In, Memory Safety Out\n";
print "═══════════════════════════════════════════════════\n";

