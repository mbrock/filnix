# BIND 9 built with Fil-C

BIND 9.20 compiled with [Fil-C](https://github.com/pizlonator/fil-c), a
memory-safe implementation of C. It covers `named`, the tools, and every
library they use (OpenSSL, libuv, liburcu, nghttp2, libxml2 and the rest):
out-of-bounds accesses, use-after-free and other memory errors stop the
process with a Fil-C panic instead of corrupting memory.

This is a research build from <https://github.com/mbrock/filnix>, not an
ISC release. Fil-C turns memory corruption into a crash; it does not stop
BIND's own assertion failures, resource exhaustion, or DNS logic bugs such
as cache poisoning, so keep up with ISC's advisories as usual.

This directory is self-contained and relocatable. It carries its own C
runtime and libraries, so it runs on x86-64 Linux whatever its C library
and needs nothing from Nix. Put it anywhere and run the programs in `bin/`:

    bin/named -g -c /etc/bind/named.conf
    bin/dig @127.0.0.1 example.com
    bin/rndc status
    bin/named-checkconf
    bin/dnssec-keygen -a ECDSAP256SHA256 example.com

Symlinks to these programs work too, for example
`ln -s $PWD/bin/named /usr/local/sbin/named`.

## Configuration

The programs use the same paths as Debian's and ISC's builds:
`/etc/bind/named.conf`, `/etc/bind/rndc.conf` and `/etc/bind/rndc.key`, and
`/var/run/named/` for the pid file and session key. Plugins are in
`lib/bind/`; give their absolute path in `named.conf`:

    plugin query "/opt/bind/lib/bind/filter-aaaa.so" { filter-aaaa-on-v4 yes; };

## Differences from other BIND builds

- `named` is much slower and uses more memory than a native build: about
  5 to 6 times the CPU per query and 4 times the resident memory in our
  `dnsperf` measurements.
- qp-trie nodes are 16 bytes rather than 12, so zones and caches take
  somewhat more memory.
- BIND's memory pools keep no free lists, as in its AddressSanitizer
  builds, so that a use of a returned object is caught.
- LMDB, JSON statistics and GeoIP (MaxMind) support are not built in.
