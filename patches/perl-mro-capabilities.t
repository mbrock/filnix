use strict;
use warnings;
use Test::More;
use mro ();

# C3's algorithm pointer crosses PL_registered_mros -> HV's mro metadata.
# DFS has a directly initialized pointer, so only testing DFS misses this.
{
    package Registry::Root;
    sub route { 'root' }
    package Registry::Left;
    our @ISA = ('Registry::Root');
    package Registry::Right;
    our @ISA = ('Registry::Root');
    sub route { 'right' }
    package Registry::Leaf;
    our @ISA = ('Registry::Left', 'Registry::Right');
}

is_deeply(mro::get_linear_isa('Registry::Leaf'),
    [qw(Registry::Leaf Registry::Left Registry::Root Registry::Right)],
    'DFS order before looking up a registered algorithm');
is(Registry::Leaf->route, 'root', 'DFS dispatches through the left branch');

for (1 .. 3) {
    mro::set_mro('Registry::Leaf', 'c3');
    is(mro::get_mro('Registry::Leaf'), 'c3', 'registered C3 algorithm selected');
    is_deeply(mro::get_linear_isa('Registry::Leaf'),
        [qw(Registry::Leaf Registry::Left Registry::Right Registry::Root)],
        'C3 order differs from DFS');
    is(Registry::Leaf->route, 'right', 'C3 method resolution uses the right branch');
    mro::set_mro('Registry::Leaf', 'dfs');
    is(Registry::Leaf->route, 'root', 'switching back invalidates the method cache');
}

mro::set_mro('Registry::Leaf', 'c3');
@Registry::Leaf::ISA = ('Registry::Right', 'Registry::Left');
is_deeply(mro::get_linear_isa('Registry::Leaf'),
    [qw(Registry::Leaf Registry::Right Registry::Left Registry::Root)],
    'ISA mutation re-enters the registered resolver');
eval { mro::set_mro('Registry::Leaf', 'unregistered') };
like($@, qr/Invalid mro name/, 'missing registry entry still raises a Perl error');
done_testing;
