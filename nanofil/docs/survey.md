# Package survey

How much of the C in filnix's ports builds with nanofil alone, and what
stops the rest. Unlike the program checks (PLAN.md, M4), the survey is
not part of the Nix check and fixes nothing: it measures.

## Method

[survey/default.nix](../survey/default.nix) defines `nanofilize`, a
package adapter over the Fil-C staging package set: the package's
`CC` is [survey/cc.sh](../survey/cc.sh), which hands every compile of C
to nanofil-cc, one source at a time (a compile-and-link `cc -o x x.c`,
as configure's probes do, too). Preprocessing, assembling and linking go
to filcc, since they compile no C. A C compile nanofil-cc cannot take
(`-S`, or C on stdin or in a file without a `.c` suffix) is logged as a
fallback and refused, never compiled by clang, so a package builds with
nanofil alone or fails. C++ still goes to filcc and is counted
([survey/cxx.sh](../survey/cxx.sh)). Libraries a package links with are
the staging set's, built by filcc; each package's own checkPhase and
installCheckPhase run as the port runs them.

[survey/run.py](../survey/run.py) takes the packages ports.nix names,
sets aside those that do not evaluate, those whose sources hold more
than half as many C++ files as C files, and those with no C sources,
builds each of the rest with filcc and then (where filcc's build
succeeds) with nanofil, and writes [survey/survey.tsv](../survey/survey.tsv)
and the table below. Rerun it from the repository root:

```sh
python3 nanofil/survey/run.py --jobs 16 --cores 4       # all of them, on swa
python3 nanofil/survey/run.py zlib xz                   # some
nix build -f nanofil/survey nf.zlib                     # one, by hand
python3 nanofil/survey/run.py --report                  # tables from survey.tsv
```

Builds already in the store are reused, and only `bin/` and `src/` of
nanofil enter the nanofil builds, so a rerun after a compiler change
rebuilds only those.

"filcc" and "nanofil" say `tests pass` when the build ran its own tests
and they passed, `built` when it has none (or the port skips them),
`tests fail` when the build failed in a check phase, and `fails in
PHASE` otherwise. The first error is the first of nanofil's own
messages, the wrapper's refusal, configure's verdict, or a compiler or
make error, in that order.

## Results

The survey of 2026-10-29, at `dd2ffee`: of the 300 packages ports.nix
names, 209 are C. filcc builds 202 of them. Of those 202, nanofil alone
builds 144 (71%; 141 at `a8e17b3`, 137 at `d3f1858`, 130 at `d91dd5e`),
compiling 36,685 objects. The 53 among them whose ports run tests pass
them, as filcc's builds do. Three build but fail their tests: libressl's
DTLS ssltest, on timing; nspr (`fegetround` at link); and cryptsetup,
whose `api-test-2.c` nanofil refuses (`unknown escape \%`).

New since `a8e17b3`: gnupg and zix build and pass their tests, and
cyrus_sasl and p11-kit build (`6e6f06a`; p11-kit's and gtk4's internal
error was its `function_name` crash). cryptsetup builds (case ranges,
`ba3f6a3`). gtk4 and ghostscript move on to vector types. Two
regressions: x264 stops at `common/macroblock.c:1521: no member named
i`, and libaom now reaches a function whose emission overflows the
stack in `filc_amd64:insts`. emacs30 again reaches its lisp stage and
hits the 90-minute build timeout. The run lost the Nix daemon twice and
rebuilt what it had lost.

### Causes

Each failure counts once, under its first error. Removing that cause
gets a package to its next error, not necessarily to a build.

Inline and top-level asm is now the largest row (31), among them glib
itself (`G_BREAKPOINT` in gmessages.c), openssl, openssh, xz, zstd and
util-linux. filcc accepts some of this asm, and reports at run time an
instruction it cannot run safely (dconf's and mbedtls's test failures
show that message), where nanofil refuses at compile time. Alignment
attributes (15) are the next row; gtk4's `gdkresources.c` is one.

Three causes are not syntax: a package whose build runs a program
nanofil built that traps (`nanofil-built program traps`, emacs30's and
gobject-introspection's build-time tools), a compile that hits the
stack or memory limit (`compiler resource limit`), and a test suite that
fails with no compiler error to point at (`package tests fail`). A
vector type named through an aligned typedef such as SSE2's `__m128i`
(xz, brotli in ghostscript) reports vector types, not its alignment.

libressl's one failing test is timing-dependent, not a miscompile.
Its ssltest runs both ends of each DTLS handshake in one process, and a
DTLS peer retransmits its flight when its 1 s timer expires; with RSA key
exchange the server's private-key decryption falls inside that window.
Without `-O` nanofil's code for libcrypto's Montgomery multiplication
(`bn/bn_mont.c`, word helpers that return through pointers to locals)
takes 0.541 s for one 1024-bit CRT half, against 0.139 s for filcc
`-O0`, 0.044 s for nanofil `-O` and 0.004 s for the port's filcc `-O3`,
so the two halves overrun the timer and the client reports an unexpected
message. Every other test passes, TLS and the ECDHE and DHE DTLS ciphers
included. Swapping object files with a filcc build pins it to
`bn_mont.c`, whose results are correct (Montgomery products and
exponentiation checked against `BN_mod_mul` over moduli of 2 to 640
bits), and ssltest passes when only `bn_mont.o` is built with nanofil
`-O`. The survey builds with the port's own flags, so this stays a
failure; run.py marks it `timing-dependent test`.

<!-- survey table -->

| Set aside | Packages |
| --- | ---: |
| C++ | 59 |
| evaluation fails | 20 |
| no C sources found | 12 |

| filcc | nanofil | Packages |
| --- | --- | ---: |
| built | built | 91 |
| tests pass | tests pass | 53 |
| tests pass | fails in buildPhase | 29 |
| built | fails in buildPhase | 26 |
| dependency fails | not tried | 4 |
| tests pass | tests fail | 3 |
| fails in buildPhase | not tried | 2 |
| tests fail | not tried | 1 |

| Cause | Packages | Which |
| --- | ---: | --- |
| inline or top-level asm | 17 | fftw, flac, fstrm, kbd, libblake3, libdeflate, libgcrypt, nettle, openssh, openssl, openssl-sarcasm, pcre2, physfs, quickjs, rhash, util-linux, zlib-ng |
| other syntax or typing gaps | 17 | binutils-unwrapped, btrfs-progs, elfutils, emacs30, finit, gettext, guile_3_0, imagemagick, kronosnet, libjpeg_turbo, libmbim, mbedtls, nss, parted, ruby_3_3, systemd, x264 |
| vector types | 12 | bind, ghostscript, gtk4, kittydoom, libopus, libpq, libtiff, libwebp, redis, tor, xz, zstd |
| other builtins | 4 | cogl, gnutls, isa-l, libgbm |
| unresolved Fil-C symbol at link | 3 | bison, keyutils, nspr |
| alignment attributes | 1 | libcdio |
| compiler resource limit | 1 | libaom |
| constant expressions not folded | 1 | libffi |
| package tests fail | 1 | cryptsetup |
| timing-dependent test | 1 | libressl |

| Package | Version | filcc | nanofil | nanofil objects | Cause | First error |
| --- | --- | --- | --- | ---: | --- | --- |
| a2ps | 4.15.7 | tests pass | tests pass | 319 |  |  |
| alsa-lib | 1.2.15.3 | built | built | 172 |  |  |
| at-spi2-core | 2.60.5 | built | built | 224 |  |  |
| bash | 5.3p9 | built | built | 568 |  |  |
| bashNonInteractive | 5.3p9 | built | built | 573 |  |  |
| bind | 9.20.30 | tests pass | fails in buildPhase |  | vector types | `nanofil: picohttpparser.c:117: vector types is not supported` |
| binutils-unwrapped | 2.43.1 | built | fails in buildPhase |  | other syntax or typing gaps | `checking for BSD- or MS-compatible name lister (nm)... grep: write error: Broken pipe` |
| bison | 3.8.2 | built | fails in buildPhase | 449 | unresolved Fil-C symbol at link | `src/bison-getargs.o:function pizlonatedFI12770_rpl_printf:(.text+0x436fd): error: undefined reference to 'pizlonated_rpl_printf'` |
| bluez | 5.86 | fails in buildPhase | not tried |  |  |  |
| btrfs-progs | 6.19.1 | tests pass | fails in buildPhase | 134 | other syntax or typing gaps | `nanofil: kernel-shared/print-tree.c:582: unknown escape \(` |
| busybox | 1.37.0 | built | built | 30 |  |  |
| cairo | 1.18.4 | built | built | 275 |  |  |
| capstone | 5.0.7 | tests pass | tests pass | 128 |  |  |
| cmocka | 2.0.1 | built | built | 82 |  |  |
| cogl | 1.22.8 | built | fails in buildPhase | 193 | other builtins | `nanofil: deprecated/cogl-fixed.c:744: undeclared identifier __builtin_sqrt` |
| coreutils | 9.11 | built | built | 1248 |  |  |
| cryptsetup | 2.8.6 | tests pass | tests fail | 186 | package tests fail | `nanofil: api-test-2.c:5774: unknown escape \%` |
| cups | 2.4.19 | built | built | 244 |  |  |
| curl | 8.22.0 | built | built | 466 |  |  |
| cyrus_sasl | 2.1.28 | built | built | 250 |  |  |
| dash | 0.5.12 | built | built | 97 |  |  |
| dav1d | 1.5.3 | tests pass | tests pass | 87 |  |  |
| db53 | 5.3.28 | tests pass | tests pass | 512 |  |  |
| dbus | 1.16.2 | tests pass | tests pass | 291 |  |  |
| dbus-glib | 0.114 | built | built | 68 |  |  |
| dconf | 0.49.0 | tests pass | tests pass | 84 |  |  |
| diffutils | 3.12 | built | built | 565 |  |  |
| duktape | 2.7.0 | tests pass | tests pass | 8 |  |  |
| e2fsprogs | 1.47.4 | built | built | 557 |  |  |
| elfutils | 0.194 | built | fails in buildPhase | 875 | other syntax or typing gaps | `nanofil: dwarf_getabbrev.c:89: sizeof: packed pointers` |
| ell | 0.83 | built | built | 117 |  |  |
| emacs30 | 30.1 | built | fails in buildPhase |  | other syntax or typing gaps | `Loading /build/source/lisp/cedet/semantic/grm-wy-boot.el (source)...` |
| expat | 2.7.1 | tests pass | tests pass | 89 |  |  |
| ffmpeg-headless | 8.1.2 | dependency fails | not tried |  |  |  |
| fftw | 3.3.11 | tests pass | fails in buildPhase | 183 | inline or top-level asm | `nanofil: ./cycle.h:226: inline asm "rdtsc" is not supported: nanofil cannot check its instructions` |
| file | 5.47 | built | built | 141 |  |  |
| finit | 4.17 | built | fails in buildPhase | 56 | other syntax or typing gaps | `nanofil: getty.c:407: bad number 1i` |
| flac | 1.5.0 | tests pass | fails in buildPhase | 37 | inline or top-level asm | `nanofil: /build/flac-1.5.0/src/libFLAC/cpu.c:80: inline asm "xgetbv" is not supported: nanofil cannot check its instructions` |
| fontconfig | 2.17.1 | built | built | 164 |  |  |
| freetype | 2.14.3 | tests pass | tests pass | 138 |  |  |
| fstrm | 0.6.1 | tests pass | fails in buildPhase | 60 | inline or top-level asm | `nanofil: libmy/my_queue_mb.c:132: inline asm "mfence" is not supported: nanofil cannot check its instructions` |
| gawk | 5.4.1 | built | built | 275 |  |  |
| gd | 2.3.3 | built | built | 112 |  |  |
| gdk-pixbuf | 2.44.7 | built | built | 91 |  |  |
| gettext | 1.0 | built | fails in buildPhase |  | other syntax or typing gaps | `/nix/store/8nz5b9a6z9rrf8r19b74jh7idaf4yyzy-nanofil-survey-cc/bin/cc -DLOCALEDIR=\"/nix/store/ny4p3874fms3n37spqm51vqpz8alpx50-gettext-x86_64-unknown-linux-gnufilc0-1.0/share/locale\" -DUSEJAVA=0 -DGETTEXTJAR=\"/nix/store/ny4p3874fms3n37spqm51vqpz8alpx50-gettext-x86_64-unknown-linux-gnufilc0-1.0/sha` |
| ghostscript | 10.07.1 | tests pass | fails in buildPhase | 353 | vector types | `nanofil: ./brotli/c/enc/matching_tag_mask.h:24: vector types is not supported` |
| git | 2.46.0 | built | built | 596 |  |  |
| glib | 2.80.4 | built | built | 879 |  |  |
| gmp | 6.3.0 | tests pass | tests pass | 861 |  |  |
| gnu-shepherd | 1.0.9 | built | built | 240 |  |  |
| gnugrep | 3.12 | built | built | 528 |  |  |
| gnum4 | 1.4.21 | built | built | 645 |  |  |
| gnumake | 4.4.1 | tests pass | tests pass | 153 |  |  |
| gnupg | 2.4.9 | tests pass | tests pass | 585 |  |  |
| gnused | 4.10 | built | built | 493 |  |  |
| gnutar | 1.35 | tests pass | tests pass | 593 |  |  |
| gnutls | 3.8.13 | built | fails in buildPhase | 664 | other builtins | `nanofil: key_share.c:256: undeclared identifier __builtin_return_address` |
| gobject-introspection-unwrapped | 1.80.1 | tests pass | tests pass | 169 |  |  |
| graphene | 1.10.8 | tests pass | tests pass | 66 |  |  |
| gsl | 2.8 | tests pass | tests pass | 1060 |  |  |
| gssdp_1_6 | 1.6.6 | tests pass | tests pass | 32 |  |  |
| gtk2 | 2.24.33 | built | built | 662 |  |  |
| gtk3 | 3.24.52 | built | built | 846 |  |  |
| gtk4 | 4.14.5 | built | fails in buildPhase | 224 | vector types | `nanofil: ../gsk/gskpath.c:521: member contour of a type nanofil does not support (vector types)` |
| gtksourceview3 | 3.24.11 | tests pass | tests pass | 181 |  |  |
| gtksourceview4 | 4.8.4 | tests pass | tests pass | 183 |  |  |
| guile-avahi | 0.4.1 | tests pass | tests pass | 49 |  |  |
| guile_3_0 | 3.0.11 | tests pass | fails in buildPhase | 688 | other syntax or typing gaps | `nanofil: foreign.c:942: bad number 1.0iF` |
| gupnp_1_6 | 1.6.10 | tests pass | tests pass | 57 |  |  |
| imagemagick | 7.1.2-31 | tests pass | fails in buildPhase | 337 | other syntax or typing gaps | `nanofil: MagickCore/fourier.c:1295: bad number 1.0iF` |
| imlib2 | 1.12.6 | built | built | 133 |  |  |
| isa-l | 2.32.0 | tests pass | fails in buildPhase | 51 | other builtins | `nanofil: /nix/store/asx904awk86a38cr62zyxqq1zf10603m-filc0-resource-dir/lib/clang/20/include/crc32intrin.h:73: undeclared identifier __builtin_ia32_crc32si` |
| jq | 1.8.2 | tests pass | tests pass | 152 |  |  |
| json-glib | 1.10.8 | tests pass | tests pass | 81 |  |  |
| kbd | 2.9.0 | built | fails in buildPhase | 154 | inline or top-level asm | `nanofil: resizecons.c:400: inline asm "inb %1,%0" is not supported: nanofil cannot check its instructions` |
| keyutils | 1.6.3 | built | fails in buildPhase | 8 | unresolved Fil-C symbol at link | `./libkeyutils.so: error: undefined reference to 'pizlonated_zargs'` |
| kittydoom | git | built | fails in buildPhase | 3 | vector types | `nanofil: src/arch/sse-base64.h:118: vector types is not supported` |
| krb5 | 1.22.2 | built | built | 1020 |  |  |
| kronosnet | 1.33 | built | fails in buildPhase | 95 | other syntax or typing gaps | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/bits/link.h:99: expected a member declaration, at __int128_t` |
| libaom | 3.12.1 | built | fails in buildPhase | 220 | compiler resource limit | `nanofil: error(resource_error(stack),stack_overflow{choicepoints:87868,depth:29663,environments:29648,globalused:705344,localused:34463,non_terminating:[frame(29662,filc_amd64:insts([47003],29624,'L50',ctx/5,_124,_126),[]),frame(29661,filc_amd64:insts([47004],29623,'L50',ctx/5,[6\|_184],_166),[])],st` |
| libapparmor | 4.1.7 | built | built | 63 |  |  |
| libarchive | 3.7.4 | built | built | 425 |  |  |
| libblake3 | 1.8.5 | built | fails in buildPhase | 4 | inline or top-level asm | `nanofil: /build/source/c/blake3_dispatch.c:70: inline asm "cpuid` |
| libcap | 2.70 | built | built | 16 |  |  |
| libcap_ng | 0.9.3 | tests pass | tests pass | 67 |  |  |
| libcbor | 0.13.0 | tests pass | tests pass | 134 |  |  |
| libcdio | 2.3.0 | tests pass | fails in buildPhase | 144 | alignment attributes | `nanofil: image/nrg.c:195: buf has a type nanofil does not support (alignment attributes)` |
| libdbusmenu | 16.04.0 | built | built | 55 |  |  |
| libdeflate | 1.25 | tests pass | fails in buildPhase | 21 | inline or top-level asm | `nanofil: /build/source/lib/x86/cpu_features.c:47: inline asm "cpuid" is not supported: nanofil cannot check its instructions` |
| libedit | 20240808-3.1 | built | built | 115 |  |  |
| libepoxy | 1.5.10 | tests pass | tests pass | 71 |  |  |
| libev | 4.33 | built | built | 56 |  |  |
| libevdev | 1.11.0 | built | built | 60 |  |  |
| libevent | 2.1.13 | built | built | 254 |  |  |
| libffi | 3.8.0 | tests pass | fails in buildPhase | 62 | constant expressions not folded | `nanofil: ../src/types.c:126: initializer is not a constant` |
| libgbm | 26.0.3 | built | fails in buildPhase | 148 | other builtins | `nanofil: ../src/util/cache_ops_x86.c:68: undeclared identifier __builtin_ia32_mfence` |
| libgcrypt | 1.12.2 | tests pass | fails in buildPhase | 123 | inline or top-level asm | `nanofil: mpiutil.c:150: an asm operand must have integer or floating type` |
| libgit2 | 1.9.7 | tests pass | tests pass | 698 |  |  |
| libglvnd | 1.7.0 | built | built | 85 |  |  |
| libgpg-error | 1.59 | tests pass | tests pass | 162 |  |  |
| libgsf | 1.14.58 | tests pass | tests pass | 164 |  |  |
| libgudev | 238 | built | built | 16 |  |  |
| libhandy | 1.8.3 | tests pass | tests pass | 145 |  |  |
| libhighscore | 0-unstable-2026-04-01 | tests pass | tests pass | 106 |  |  |
| libical | 3.0.20 | built | built | 228 |  |  |
| libiconv | 1.19 | built | built | 266 |  |  |
| libidn2 | 2.3.8 | built | built | 229 |  |  |
| libinput | 1.29.1 | tests pass | tests pass | 125 |  |  |
| libjpeg_turbo | 3.1.4 | tests pass | fails in buildPhase | 22 | other syntax or typing gaps | `nanofil: /nix/store/10xdyb6i0ahryz4a85xp747zwkh7g7xw-simde-0.8.2/include/simde/arm/neon/movl.h:54: expected an expression, at typeof` |
| liblc3 | 1.1.3 | built | built | 15 |  |  |
| libmbim | 1.34.0 | tests pass | fails in buildPhase | 56 | other syntax or typing gaps | `nanofil: ../src/libmbim-glib/mbim-device.c:2447: pointer arithmetic on struct(627) (packed pointers)` |
| libmhash | 0.9.9.9 | tests pass | tests pass | 140 |  |  |
| libmicrohttpd | 1.0.2 | built | built | 278 |  |  |
| libmpdclient | 2.24 | tests pass | tests pass | 98 |  |  |
| libopus | 1.6.1 | tests pass | fails in buildPhase | 24 | vector types | `nanofil: ../celt/float_cast.h:68: calls returning bad(vector types) are not supported yet` |
| libpng | 1.6.43 | built | built | 71 |  |  |
| libpq | 18.6 | built | fails in buildPhase | 304 | vector types | `nanofil: jsonapi.c:2218: vector types is not supported` |
| libraqm | 0.10.5 | tests pass | tests pass | 14 |  |  |
| libressl | 4.2.1 | tests pass | tests fail | 720 | timing-dependent test | `make: *** [Makefile:71: test] Error 8` |
| libseccomp | 2.6.1 | tests pass | tests pass | 161 |  |  |
| libselinux | 3.10 | built | built | 155 |  |  |
| libsepol | 3.10 | built | built | 142 |  |  |
| libshout | 2.4.6 | built | built | 92 |  |  |
| libsodium | 1.0.22-unstable-2026-04-09 | tests pass | tests pass | 376 |  |  |
| libsoup_3 | 3.6.6 | built | built | 235 |  |  |
| libssh2 | 1.11.1 | built | built | 88 |  |  |
| libtasn1 | 4.21.0 | built | built | 224 |  |  |
| libtiff | 4.7.2 | tests pass | fails in buildPhase | 62 | vector types | `nanofil: /build/source/libtiff/tif_predict.c:605: vector types is not supported` |
| libtirpc | 1.3.7 | tests pass | tests pass | 131 |  |  |
| liburcu | 0.15.6 | tests pass | tests pass | 242 |  |  |
| libuv | 1.52.1 | built | built | 94 |  |  |
| libvmaf | 3.0.0 | tests pass | tests pass | 129 |  |  |
| libvpx | 1.16.0 | built | built | 225 |  |  |
| libwebp | 1.6.0 | built | fails in buildPhase | 33 | vector types | `nanofil: /build/source/sharpyuv/sharpyuv_sse2.c:85: vector types is not supported` |
| libxcrypt | 4.5.2 | built | built | 129 |  |  |
| libxkbcommon | 1.13.1 | built | built | 393 |  |  |
| libxml2 | 2.15.4 | built | built | 82 |  |  |
| lighttpd | 1.4.85 | built | built | 295 |  |  |
| lttng-ust | 2.14.0 | tests fail | not tried |  |  |  |
| lzo | 2.10 | built | built | 289 |  |  |
| mailutils | 3.21 | tests pass | tests pass | 1157 |  |  |
| mariadb-connector-c_3_3 | 3.3.5 | built | built | 159 |  |  |
| mbedtls | 3.6.6 | tests pass | fails in buildPhase | 16 | other syntax or typing gaps | `nanofil: /build/source/library/bignum_core.c:480: mode TI (__int128) is not supported` |
| minizip | 1.3.2 | built | built | 35 |  |  |
| mpdecimal | 4.0.1 | built | built | 44 |  |  |
| mpfr | 4.2.2 | tests pass | tests pass | 540 |  |  |
| mpg123 | 1.33.7 | dependency fails | not tried |  |  |  |
| netcdf | 4.9.3 | tests pass | tests pass | 705 |  |  |
| nettle | 3.10.2 | tests pass | fails in buildPhase | 465 | inline or top-level asm | `nanofil: nettle-benchmark.c:888: inline asm "xorl %%eax,%%eax` |
| nghttp2 | 1.69.0 | built | built | 127 |  |  |
| nspr | 4.40 | tests pass | tests fail | 98 | unresolved Fil-C symbol at link | `../../dist/lib/libnspr4.so: error: undefined reference to 'pizlonated_fegetround'` |
| nss | 3.112.5 | tests pass | fails in buildPhase | 365 | other syntax or typing gaps | `nanofil: ../../lib/freebl/gcm.c:135: __int128 is not supported` |
| oniguruma | 6.9.10 | built | built | 104 |  |  |
| openssh | 10.5p1 | tests pass | fails in buildPhase | 661 | inline or top-level asm | `nanofil: sntrup761.c:62: inline asm "sarw $15,%0" is not supported: nanofil cannot check its instructions` |
| openssl | 3.5.7 | built | fails in buildPhase | 495 | inline or top-level asm | `nanofil: crypto/cpuid.c:96: top-level asm ".filc_unsafe_export OPENSSL_ia32cap_P" is not supported; only .symver is` |
| openssl-sarcasm | 3.6.4 | tests pass | fails in buildPhase | 140 | inline or top-level asm | `nanofil: crypto/bn/bn_div.c:388: inline asm "divq   %4" is not supported: nanofil cannot check its instructions` |
| p11-kit | 0.26.2 | built | built | 289 |  |  |
| pam | 1.7.2 | built | built | 239 |  |  |
| pango | 1.56.3 | built | built | 163 |  |  |
| parted | 3.7 | tests pass | fails in buildPhase | 329 | other syntax or typing gaps | `nanofil: gpt.c:1195: member Signature of a type nanofil does not support (packed pointers)` |
| pcre2 | 10.48 | built | fails in buildPhase | 73 | inline or top-level asm | `nanofil: src/../deps/sljit/sljit_src/sljitNativeX86_common.c:462: inline asm "cpuid` |
| perl5 | 5.40.0 | built | built | 745 |  |  |
| physfs | 3.2.0 | tests pass | fails in buildPhase | 42 | inline or top-level asm | `nanofil: /build/source/src/physfs_lzmasdk.h:1495: inline asm "cpuid" is not supported: nanofil cannot check its instructions` |
| pixman | 0.46.4 | built | built | 119 |  |  |
| polkit | 127 | tests pass | tests pass | 71 |  |  |
| potrace | 1.16 | tests pass | tests pass | 67 |  |  |
| procps | 4.0.6 | built | built | 187 |  |  |
| pth | 2.0.7 | tests pass | tests pass | 112 |  |  |
| pulseaudio | 17.0 | dependency fails | not tried |  |  |  |
| python312 | 3.12.5 | built | built | 858 |  |  |
| quickjs | 2026-06-04 | tests pass | fails in buildPhase | 12 | inline or top-level asm | `nanofil: quickjs.c:60630: inline asm "pause" is not supported: nanofil cannot check its instructions` |
| rdkafka | 2.13.0 | built | built | 239 |  |  |
| recode | 3.7.15 | tests pass | tests pass | 293 |  |  |
| redis | 8.8.2 | tests pass | fails in buildPhase | 91 | vector types | `nanofil: ./xxhash.h:5220: vector types is not supported` |
| rhash | 1.4.6 | tests pass | fails in buildPhase | 6 | inline or top-level asm | `nanofil: calc_sums.c:555: inline asm "rdtsc" is not supported: nanofil cannot check its instructions` |
| rpcbind | 1.2.6 | built | built | 31 |  |  |
| rsync | 3.5.0 | tests pass | tests pass | 378 |  |  |
| ruby_3_3 | 3.3.10 | tests pass | fails in buildPhase | 601 | other syntax or typing gaps | `nanofil: error.c:2842: incompatible ?: operands int and ptr(struct(88))` |
| runit | 2.3.1 | tests pass | tests pass | 98 |  |  |
| scrypt | 1.3.3 | built | built | 106 |  |  |
| seatd | 0.9.3 | built | built | 62 |  |  |
| spandsp | 0.0.6 | built | built | 93 |  |  |
| sqlite | 3.51.2 | built | built | 64 |  |  |
| strace | 7.2 | fails in buildPhase | not tried |  |  |  |
| svt-av1 | 3.1.2 | built | built | 148 |  |  |
| systemd | 256.4 | tests pass | fails in buildPhase | 253 | other syntax or typing gaps | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/bits/link.h:99: expected a member declaration, at __int128_t` |
| timidity | 2.15.0 | dependency fails | not tried |  |  |  |
| tinycc | 0.9.27-unstable-2025-01-06 | built | built | 14 |  |  |
| tor | 0.4.9.12 | built | fails in buildPhase | 499 | vector types | `nanofil: src/core/crypto/relay_crypto_cgo.c:55: member kb of a type nanofil does not support (vector types)` |
| torsocks | 2.5.0 | built | built | 116 |  |  |
| tpm2-abrmd | 3.0.0 | built | built | 94 |  |  |
| tpm2-tss | 4.2.0 | tests pass | tests pass | 1278 |  |  |
| trealla | unstable-2026-09-05 | built | built | 99 |  |  |
| ttyd | 1.7.7 | built | built | 9 |  |  |
| unbound | 1.26.0 | tests pass | tests pass | 734 |  |  |
| util-linux | 2.42.3 | built | fails in buildPhase | 363 | inline or top-level asm | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/sys/io.h:47: inline asm "inb %w1,%0" is not supported: nanofil cannot check its instructions` |
| uwimap | 2007f | built | built | 38 |  |  |
| vala | 0.56.19 | built | built | 488 |  |  |
| wasm3 | 0.5.0 | built | built | 19 |  |  |
| wavpack | 5.9.0 | built | built | 87 |  |  |
| wayland | 1.25.0 | built | built | 73 |  |  |
| weston | 15.0.1 | built | built | 349 |  |  |
| x264 | 0-unstable-2025-01-03 | built | fails in buildPhase | 36 | other syntax or typing gaps | `nanofil: common/macroblock.c:1521: no member named i` |
| xvidcore | 1.3.7 | built | built | 71 |  |  |
| xz | 5.8.4 | built | fails in buildPhase | 206 | vector types | `nanofil: ../../src/liblzma/lz/lz_decoder.h:243: vector types is not supported` |
| zix | 0.6.2 | tests pass | tests pass | 59 |  |  |
| zlib | 1.3.2 | tests pass | tests pass | 47 |  |  |
| zlib-ng | 2.2.4 | built | fails in buildPhase | 61 | inline or top-level asm | `nanofil: /build/zlib-ng-2.2.4/arch/x86/x86_features.c:64: inline asm ".byte 0x0f, 0x01, 0xd0" is not supported: nanofil cannot check its instructions` |
| zstd | 1.5.7 | built | fails in buildPhase | 24 | vector types | `nanofil: /build/source/lib/compress/../common/zstd_internal.h:187: calls returning bad(vector types) are not supported yet` |

<!-- end survey table -->
