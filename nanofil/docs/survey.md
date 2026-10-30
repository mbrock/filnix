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

The survey runs on the campaign service at <https://nix.swa.sh/>
([docs/campaign-service.md](../../docs/campaign-service.md)), which keeps
every build's time, machine, outcome and complete log.
[survey/run.py](../survey/run.py) `manifest` takes the packages ports.nix
names and sets aside those that do not evaluate, those whose sources hold
more than half as many C++ files as C files, those with no C sources, and
the slow ones (`slow` in survey/default.nix: emacs30, libgcrypt). Each of
the rest becomes two roots, `ref.NAME` (filcc) and `nf.NAME` (nanofil),
which is only tried where filcc's build succeeds. `run.py report` writes
[survey/survey.tsv](../survey/survey.tsv) and the table below from the
campaign's results. From swa:

```sh
campaignctl submit nanofil-survey --opt plain     # at origin/main; or --rev REV, --opt -O, --opt --vectors
campaignctl list                                  # or https://nix.swa.sh/
python3 nanofil/survey/run.py report CAMPAIGN-ID  # survey.tsv, survey-OPT.tsv and the tables below
nix build -f nanofil/survey nf.zlib               # one, by hand
python3 nanofil/survey/run.py --report            # tables from survey.tsv
campaignctl submit bench                          # the slow packages, one at a time, local, rebuilt
```

A campaign's page at `/c/ID/survey` shows each package's filcc and
nanofil builds side by side, with build times and the machine that built
them; times compare only within one machine. Builds already in the store
are reused, and only `bin/` and `src/` of nanofil enter the nanofil
builds, so a survey after a compiler change rebuilds only those.

"filcc" and "nanofil" say `tests pass` when the build ran its own tests
and they passed, `built` when it has none (or the port skips them),
`tests fail` when the build failed in a check phase, and `fails in
PHASE` otherwise. The first error is the first of nanofil's own
messages, the wrapper's refusal, configure's verdict, or a compiler or
make error, in that order.

## Results

The survey of 2026-10-30 at `746154d`, the first run through the
campaign service
([`20261030-1136-nanofil-survey-746154d-plain`](https://nix.swa.sh/c/20261030-1136-nanofil-survey-746154d-plain/survey)),
sets emacs30 and libgcrypt aside as slow (see above) and covers the
other 207 C packages. filcc builds 200 of them, and nanofil alone
builds 160, as at `6bc0f74`. x264 is not among them: its
`common/x86/util.h` declares a union with an `__m128 i` member under
`#ifdef __SSE__`, so plain mode refuses it
(`common/macroblock.c:1521: no member named i`) and it builds only with
`--vectors`. The `6bc0f74` survey counted it as built from an output
that a vectors-on build had left in the store, so that survey's true
count is 160, not 161. btrfs-progs gets
past `__builtin_cpu_init` to its SSE2 BLAKE2b. The table's timings are
wall-clock seconds on the named builder (igloo or chapel), which are
not comparable across machines.

The survey of 2026-10-30, at `6bc0f74`: of the 300 packages ports.nix
names, 209 are C. filcc builds 202 of them. Of those 202, nanofil alone
builds 160 (79%, x264 corrected, see above; 144 at `dd2ffee`, 141 at `a8e17b3`, 137 at `d3f1858`,
130 at `d91dd5e`), compiling 44,903 objects. The 60 among them whose
ports run tests pass them, as filcc's builds do. Two build but fail
their tests: libressl's DTLS ssltest, on timing, and nspr
(`fegetround` at link).

New since `dd2ffee`: asm that filcc traps on now compiles to filcc's
trap (`4379478`), and cpuid, xgetbv, rdtsc, rdtscp, lfence, sfence and
pause compile to checked `asm_fixed` (`f20ffe5`, `ba3d7a6`), which takes
the inline-asm row from 31 to 3. fstrm, nettle, libmbim, parted, physfs
and rhash build and pass their tests; binutils, cogl, elfutils, gettext,
kbd, libblake3, pcre2, util-linux and zlib-ng build; cryptsetup
now passes its tests. libgcrypt gets past its asm and its plain build
hits the 90-minute timeout in its tests, as emacs30 does in its lisp
stage (libgcrypt builds and passes at `-O`). No package regressed.

With `--vectors` (GNU vector types and the SSE through SSE4.2 and
PCLMULQDQ intrinsics, off by default; `16620be`), ghostscript, libopus
and libtiff also pass their tests and kittydoom, libpq, xz and zstd
build, plain and at `-O`, for 168 of 202 (x264 with them). The other vector packages
stop at `__builtin_ia32_shufpd` (fftw, flac), the SSE4.2 string
compares (bind, gtk4), 32-byte vectors (libdeflate, libwebp),
`long double` classification (redis) and `__int128` (tor).

The `-O` survey at `b7a9651` built 154 of 202; its four `-O`-only
failures (gsl, libgit2, netcdf, unbound) build and pass their tests
since `c7e94e8`.

### Causes

Each failure counts once, under its first error. Removing that cause
gets a package to its next error, not necessarily to a build.

Vector types are now the largest row (16); `--vectors` builds seven of
them (see above), and the release default stays off until the rest are
measured. The 3 inline-asm packages left need asm filcc checks and runs
natively (openssh's `sarw`, openssl-sarcasm's `divq`) or openssl's
`.filc_unsafe_export`. Of the 10 other syntax or typing gaps, x264's is a vector type
reported as a missing member, four are
`__int128` or GNU complex literals (`1.0iF`), two glibc's `link.h`, and
quickjs's `__builtin_frame_address(0)`, which stays out by decision.

Two rows are not syntax: a test suite that fails with no compiler error
to point at (`timing-dependent test`, below) and a build that hits the
90-minute limit (`build timeout`).

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
| slow | 2 |

| filcc | nanofil | Packages |
| --- | --- | ---: |
| built | built | 100 |
| tests pass | tests pass | 60 |
| tests pass | fails in buildPhase | 22 |
| built | fails in buildPhase | 16 |
| dependency fails | not tried | 4 |
| fails in buildPhase | not tried | 2 |
| tests pass | tests fail | 2 |
| tests fail | not tried | 1 |

| Cause | Packages | Which |
| --- | ---: | --- |
| vector types | 16 | bind, btrfs-progs, fftw, flac, ghostscript, gtk4, kittydoom, libdeflate, libopus, libpq, libtiff, libwebp, redis, tor, xz, zstd |
| other syntax or typing gaps | 10 | finit, guile_3_0, imagemagick, kronosnet, mbedtls, nss, quickjs, ruby_3_3, systemd, x264 |
| unresolved Fil-C symbol at link | 4 | bison, keyutils, libaom, nspr |
| inline or top-level asm | 3 | openssh, openssl, openssl-sarcasm |
| other builtins | 3 | gnutls, isa-l, libgbm |
| constant expressions not folded | 2 | libffi, libjpeg_turbo |
| alignment attributes | 1 | libcdio |
| timing-dependent test | 1 | libressl |

| Package | Version | filcc | nanofil | nanofil s | nanofil objects | Cause | First error |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| a2ps | 4.15.7 | tests pass | tests pass | 212 | 319 |  |  |
| alsa-lib | 1.2.15.3 | built | built | 46 | 172 |  |  |
| at-spi2-core | 2.60.5 | built | built | 49 | 224 |  |  |
| bash | 5.3p9 | built | built | 131 | 568 |  |  |
| bashNonInteractive | 5.3p9 | built | built | 128 | 573 |  |  |
| bind | 9.20.30 | tests pass | fails in buildPhase | 80 | 275 | vector types | `nanofil: picohttpparser.c:117: vector types is not supported` |
| binutils-unwrapped | 2.43.1 | built | built | 331 | 1060 |  |  |
| bison | 3.8.2 | built | fails in buildPhase | 97 | 449 | unresolved Fil-C symbol at link | `src/bison-getargs.o:function pizlonatedFI12770_rpl_printf:(.text+0x4271d): error: undefined reference to 'pizlonated_rpl_printf'` |
| bluez | 5.86 | fails in buildPhase | not tried |  |  |  |  |
| btrfs-progs | 6.19.1 | tests pass | fails in buildPhase | 65 | 186 | vector types | `nanofil: crypto/blake2b-sse2.c:44: vector types is not supported` |
| busybox | 1.37.0 | built | built | 77 | 30 |  |  |
| cairo | 1.18.4 | built | built | 93 | 275 |  |  |
| capstone | 5.0.7 | tests pass | tests pass | 65 | 128 |  |  |
| cmocka | 2.0.1 | built | built | 45 | 82 |  |  |
| cogl | 1.22.8 | built | built | 660 | 293 |  |  |
| coreutils | 9.11 | built | built | 231 | 1248 |  |  |
| cryptsetup | 2.8.6 | tests pass | tests pass | 87 | 188 |  |  |
| cups | 2.4.19 | built | built | 129 | 244 |  |  |
| curl | 8.22.0 | built | built | 139 | 466 |  |  |
| cyrus_sasl | 2.1.28 | built | built | 172 | 250 |  |  |
| dash | 0.5.12 | built | built | 17 | 97 |  |  |
| dav1d | 1.5.3 | tests pass | tests pass | 41 | 87 |  |  |
| db53 | 5.3.28 | tests pass | tests pass | 199 | 512 |  |  |
| dbus | 1.16.2 | tests pass | tests pass | 56 | 291 |  |  |
| dbus-glib | 0.114 | built | built | 60 | 68 |  |  |
| dconf | 0.49.0 | tests pass | tests pass | 44 | 84 |  |  |
| diffutils | 3.12 | built | built | 201 | 565 |  |  |
| duktape | 2.7.0 | tests pass | tests pass | 157 | 8 |  |  |
| e2fsprogs | 1.47.4 | built | built | 149 | 557 |  |  |
| elfutils | 0.194 | built | built | 131 | 1196 |  |  |
| ell | 0.83 | built | built | 17 | 117 |  |  |
| expat | 2.7.1 | tests pass | tests pass | 219 | 89 |  |  |
| ffmpeg-headless | 8.1.2 | dependency fails | not tried |  |  |  |  |
| fftw | 3.3.11 | tests pass | fails in buildPhase | 91 | 250 | vector types | `nanofil: ./../common/n1fv_12.c:153: vector types is not supported` |
| file | 5.47 | built | built | 29 | 141 |  |  |
| finit | 4.17 | built | fails in buildPhase | 21 | 56 | other syntax or typing gaps | `nanofil: getty.c:407: bad number 1i` |
| flac | 1.5.0 | tests pass | fails in buildPhase | 17 | 49 | vector types | `nanofil: /build/flac-1.5.0/src/libFLAC/deduplication/lpc_compute_autocorrelation_intrin_sse2.c:4: vector types is not supported` |
| fontconfig | 2.17.1 | built | built | 61 | 164 |  |  |
| freetype | 2.14.3 | tests pass | tests pass | 37 | 138 |  |  |
| fstrm | 0.6.1 | tests pass | tests pass | 63 | 74 |  |  |
| gawk | 5.4.1 | built | built | 219 | 275 |  |  |
| gd | 2.3.3 | built | built | 17 | 112 |  |  |
| gdk-pixbuf | 2.44.7 | built | built | 34 | 91 |  |  |
| gettext | 1.0 | built | built | 1605 | 3030 |  |  |
| ghostscript | 10.07.1 | tests pass | fails in buildPhase | 210 | 447 | vector types | `nanofil: ./brotli/c/enc/matching_tag_mask.h:24: vector types is not supported` |
| git | 2.46.0 | built | built | 370 | 596 |  |  |
| glib | 2.80.4 | built | built | 221 | 842 |  |  |
| gmp | 6.3.0 | tests pass | tests pass | 757 | 861 |  |  |
| gnu-shepherd | 1.0.9 | built | built | 410 | 240 |  |  |
| gnugrep | 3.12 | built | built | 126 | 528 |  |  |
| gnum4 | 1.4.21 | built | built | 146 | 645 |  |  |
| gnumake | 4.4.1 | tests pass | tests pass | 54 | 153 |  |  |
| gnupg | 2.4.9 | tests pass | tests pass | 1027 | 585 |  |  |
| gnused | 4.10 | built | built | 117 | 493 |  |  |
| gnutar | 1.35 | tests pass | tests pass | 1005 | 593 |  |  |
| gnutls | 3.8.13 | built | fails in buildPhase | 189 | 673 | other builtins | `nanofil: key_share.c:256: undeclared identifier __builtin_return_address` |
| gobject-introspection-unwrapped | 1.80.1 | tests pass | tests pass | 136 | 169 |  |  |
| graphene | 1.10.8 | tests pass | tests pass | 23 | 66 |  |  |
| gsl | 2.8 | tests pass | tests pass | 2419 | 1060 |  |  |
| gssdp_1_6 | 1.6.6 | tests pass | tests pass | 44 | 32 |  |  |
| gtk2 | 2.24.33 | built | built | 721 | 662 |  |  |
| gtk3 | 3.24.52 | built | built | 531 | 846 |  |  |
| gtk4 | 4.14.5 | built | fails in buildPhase | 193 | 225 | vector types | `nanofil: ../gsk/gskpath.c:521: member contour of a type nanofil does not support (vector types)` |
| gtksourceview3 | 3.24.11 | tests pass | tests pass | 194 | 181 |  |  |
| gtksourceview4 | 4.8.4 | tests pass | tests pass | 188 | 183 |  |  |
| guile-avahi | 0.4.1 | tests pass | tests pass | 26 | 49 |  |  |
| guile_3_0 | 3.0.11 | tests pass | fails in buildPhase | 264 | 688 | other syntax or typing gaps | `nanofil: foreign.c:942: bad number 1.0iF` |
| gupnp_1_6 | 1.6.10 | tests pass | tests pass | 96 | 57 |  |  |
| imagemagick | 7.1.2-31 | tests pass | fails in buildPhase | 119 | 336 | other syntax or typing gaps | `nanofil: MagickCore/fourier.c:1295: bad number 1.0iF` |
| imlib2 | 1.12.6 | built | built | 32 | 133 |  |  |
| isa-l | 2.32.0 | tests pass | fails in buildPhase | 17 | 51 | other builtins | `nanofil: /nix/store/asx904awk86a38cr62zyxqq1zf10603m-filc0-resource-dir/lib/clang/20/include/crc32intrin.h:73: undeclared identifier __builtin_ia32_crc32si` |
| jq | 1.8.2 | tests pass | tests pass | 97 | 152 |  |  |
| json-glib | 1.10.8 | tests pass | tests pass | 27 | 81 |  |  |
| kbd | 2.9.0 | built | built | 38 | 202 |  |  |
| keyutils | 1.6.3 | built | fails in buildPhase | 2 | 8 | unresolved Fil-C symbol at link | `./libkeyutils.so: error: undefined reference to 'pizlonated_zargs'` |
| kittydoom | git | built | fails in buildPhase | 16 | 3 | vector types | `nanofil: src/arch/sse-base64.h:118: vector types is not supported` |
| krb5 | 1.22.2 | built | built | 258 | 1020 |  |  |
| kronosnet | 1.33 | built | fails in buildPhase | 33 | 95 | other syntax or typing gaps | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/bits/link.h:99: expected a member declaration, at __int128_t` |
| libaom | 3.12.1 | built | fails in buildPhase | 83 | 237 | unresolved Fil-C symbol at link | `CMakeFiles/lightfield_encoder.dir/examples/lightfield_encoder.c.o:function pizlonatedFI3014655940_aom_highbd_masked_sad128x128_c:(.text+0x13ebbd): error: undefined reference to 'pizlonated_aom_highbd_masked_sad128x128_c'` |
| libapparmor | 4.1.7 | built | built | 79 | 63 |  |  |
| libarchive | 3.7.4 | built | built | 90 | 425 |  |  |
| libblake3 | 1.8.5 | built | built | 4 | 5 |  |  |
| libcap | 2.70 | built | built | 8 | 16 |  |  |
| libcap_ng | 0.9.3 | tests pass | tests pass | 20 | 67 |  |  |
| libcbor | 0.13.0 | tests pass | tests pass | 18 | 134 |  |  |
| libcdio | 2.3.0 | tests pass | fails in buildPhase | 25 | 141 | alignment attributes | `nanofil: image/nrg.c:195: buf has a type nanofil does not support (alignment attributes)` |
| libdbusmenu | 16.04.0 | built | built | 44 | 55 |  |  |
| libdeflate | 1.25 | tests pass | fails in buildPhase | 9 | 32 | vector types | `nanofil: /build/source/lib/x86/adler32_template.h:219: vector types is not supported` |
| libedit | 20240808-3.1 | built | built | 42 | 115 |  |  |
| libepoxy | 1.5.10 | tests pass | tests pass | 53 | 71 |  |  |
| libev | 4.33 | built | built | 17 | 56 |  |  |
| libevdev | 1.11.0 | built | built | 13 | 60 |  |  |
| libevent | 2.1.13 | built | built | 82 | 254 |  |  |
| libffi | 3.8.0 | tests pass | fails in buildPhase | 29 | 64 | constant expressions not folded | `nanofil: ../src/types.c:126: initializer is not a constant` |
| libgbm | 26.0.3 | built | fails in buildPhase | 28 | 149 | other builtins | `nanofil: ../src/util/cache_ops_x86.c:68: undeclared identifier __builtin_ia32_mfence` |
| libgit2 | 1.9.7 | tests pass | tests pass | 272 | 698 |  |  |
| libglvnd | 1.7.0 | built | built | 182 | 85 |  |  |
| libgpg-error | 1.59 | tests pass | tests pass | 81 | 162 |  |  |
| libgsf | 1.14.58 | tests pass | tests pass | 353 | 164 |  |  |
| libgudev | 238 | built | built | 11 | 16 |  |  |
| libhandy | 1.8.3 | tests pass | tests pass | 116 | 145 |  |  |
| libhighscore | 0-unstable-2026-04-01 | tests pass | tests pass | 69 | 106 |  |  |
| libical | 3.0.20 | built | built | 85 | 228 |  |  |
| libiconv | 1.19 | built | built | 99 | 266 |  |  |
| libidn2 | 2.3.8 | built | built | 64 | 229 |  |  |
| libinput | 1.29.1 | tests pass | tests pass | 15 | 125 |  |  |
| libjpeg_turbo | 3.1.4 | tests pass | fails in buildPhase | 34 | 23 | constant expressions not folded | `nanofil: /nix/store/10xdyb6i0ahryz4a85xp747zwkh7g7xw-simde-0.8.2/include/simde/arm/neon/../../x86/mmx.h:124: static assertion is not a constant` |
| liblc3 | 1.1.3 | built | built | 4 | 15 |  |  |
| libmbim | 1.34.0 | tests pass | tests pass | 47 | 99 |  |  |
| libmhash | 0.9.9.9 | tests pass | tests pass | 155 | 140 |  |  |
| libmicrohttpd | 1.0.2 | built | built | 98 | 278 |  |  |
| libmpdclient | 2.24 | tests pass | tests pass | 8 | 98 |  |  |
| libopus | 1.6.1 | tests pass | fails in buildPhase | 7 | 39 | vector types | `nanofil: ../celt/float_cast.h:68: calls returning bad(vector types) are not supported yet` |
| libpng | 1.6.43 | built | built | 77 | 71 |  |  |
| libpq | 18.6 | built | fails in buildPhase | 122 | 304 | vector types | `nanofil: jsonapi.c:2218: vector types is not supported` |
| libraqm | 0.10.5 | tests pass | tests pass | 4 | 14 |  |  |
| libressl | 4.2.1 | tests pass | tests fail | 1921 |  | timing-dependent test | `133/134 Test  #29: bn_mod_exp .......................   Passed  948.36 sec` |
| libseccomp | 2.6.1 | tests pass | tests pass | 1300 | 161 |  |  |
| libselinux | 3.10 | built | built | 282 | 155 |  |  |
| libsepol | 3.10 | built | built | 48 | 142 |  |  |
| libshout | 2.4.6 | built | built | 53 | 92 |  |  |
| libsodium | 1.0.22-unstable-2026-04-09 | tests pass | tests pass | 345 | 377 |  |  |
| libsoup_3 | 3.6.6 | built | built | 113 | 235 |  |  |
| libssh2 | 1.11.1 | built | built | 217 | 88 |  |  |
| libtasn1 | 4.21.0 | built | built | 64 | 224 |  |  |
| libtiff | 4.7.2 | tests pass | fails in buildPhase | 17 | 63 | vector types | `nanofil: /build/source/libtiff/tif_predict.c:605: vector types is not supported` |
| libtirpc | 1.3.7 | tests pass | tests pass | 22 | 131 |  |  |
| liburcu | 0.15.6 | tests pass | tests pass | 50 | 242 |  |  |
| libuv | 1.52.1 | built | built | 20 | 94 |  |  |
| libvmaf | 3.0.0 | tests pass | tests pass | 25 | 129 |  |  |
| libvpx | 1.16.0 | built | built | 59 | 225 |  |  |
| libwebp | 1.6.0 | built | fails in buildPhase | 19 | 86 | vector types | `nanofil: /build/source/sharpyuv/sharpyuv_sse2.c:85: vector types is not supported` |
| libxcrypt | 4.5.2 | built | built | 18 | 129 |  |  |
| libxkbcommon | 1.13.1 | built | built | 88 | 393 |  |  |
| libxml2 | 2.15.4 | built | built | 90 | 82 |  |  |
| lighttpd | 1.4.85 | built | built | 176 | 295 |  |  |
| lttng-ust | 2.14.0 | tests fail | not tried |  |  |  |  |
| lzo | 2.10 | built | built | 61 | 289 |  |  |
| mailutils | 3.21 | tests pass | tests pass | 544 | 1157 |  |  |
| mariadb-connector-c_3_3 | 3.3.5 | built | built | 49 | 159 |  |  |
| mbedtls | 3.6.6 | tests pass | fails in buildPhase | 6 | 31 | other syntax or typing gaps | `nanofil: /build/source/library/bignum_core.c:480: mode TI (__int128) is not supported` |
| minizip | 1.3.2 | built | built | 26 | 35 |  |  |
| mpdecimal | 4.0.1 | built | built | 26 | 44 |  |  |
| mpfr | 4.2.2 | tests pass | tests pass | 217 | 540 |  |  |
| mpg123 | 1.33.7 | dependency fails | not tried |  |  |  |  |
| netcdf | 4.9.3 | tests pass | tests pass | 652 | 705 |  |  |
| nettle | 3.10.2 | tests pass | tests pass | 311 | 592 |  |  |
| nghttp2 | 1.69.0 | built | built | 39 | 127 |  |  |
| nspr | 4.40 | tests pass | tests fail | 73 | 98 | unresolved Fil-C symbol at link | `../../dist/lib/libnspr4.so: error: undefined reference to 'pizlonated_fegetround'` |
| nss | 3.112.5 | tests pass | fails in buildPhase | 134 | 363 | other syntax or typing gaps | `nanofil: ../../lib/freebl/gcm.c:135: __int128 is not supported` |
| oniguruma | 6.9.10 | built | built | 61 | 104 |  |  |
| openssh | 10.5p1 | tests pass | fails in buildPhase | 185 | 668 | inline or top-level asm | `nanofil: sntrup761.c:62: inline asm "sarw $15,%0" is not supported: nanofil cannot check its instructions` |
| openssl | 3.5.7 | built | fails in buildPhase | 107 | 496 | inline or top-level asm | `nanofil: crypto/cpuid.c:96: top-level asm ".filc_unsafe_export OPENSSL_ia32cap_P" is not supported; only .symver is` |
| openssl-sarcasm | 3.6.4 | tests pass | fails in buildPhase | 30 | 154 | inline or top-level asm | `nanofil: crypto/bn/bn_div.c:388: inline asm "divq   %4" is not supported: nanofil cannot check its instructions` |
| p11-kit | 0.26.2 | built | built | 132 | 289 |  |  |
| pam | 1.7.2 | built | built | 82 | 239 |  |  |
| pango | 1.56.3 | built | built | 75 | 163 |  |  |
| parted | 3.7 | tests pass | tests pass | 101 | 404 |  |  |
| pcre2 | 10.48 | built | built | 259 | 158 |  |  |
| perl5 | 5.40.0 | built | built | 2578 | 745 |  |  |
| physfs | 3.2.0 | tests pass | tests pass | 10 | 45 |  |  |
| pixman | 0.46.4 | built | built | 20 | 119 |  |  |
| polkit | 127 | tests pass | tests pass | 49 | 71 |  |  |
| potrace | 1.16 | tests pass | tests pass | 17 | 67 |  |  |
| procps | 4.0.6 | built | built | 37 | 187 |  |  |
| pth | 2.0.7 | tests pass | tests pass | 34 | 112 |  |  |
| pulseaudio | 17.0 | dependency fails | not tried |  |  |  |  |
| python312 | 3.12.5 | built | built | 611 | 858 |  |  |
| quickjs | 2026-06-04 | tests pass | fails in buildPhase | 13 | 12 | other syntax or typing gaps | `nanofil: quickjs.c:2056: __builtin_frame_address(0) is not supported: nanofil cannot express the frame address` |
| rdkafka | 2.13.0 | built | built | 174 | 240 |  |  |
| recode | 3.7.15 | tests pass | tests pass | 163 | 293 |  |  |
| redis | 8.8.2 | tests pass | fails in buildPhase | 61 | 135 | vector types | `nanofil: ./xxhash.h:5220: vector types is not supported` |
| rhash | 1.4.6 | tests pass | tests pass | 52 | 51 |  |  |
| rpcbind | 1.2.6 | built | built | 18 | 31 |  |  |
| rsync | 3.5.0 | tests pass | tests pass | 291 | 378 |  |  |
| ruby_3_3 | 3.3.10 | tests pass | fails in buildPhase | 812 | 1193 | other syntax or typing gaps | `nanofil: handle.c:460: no member named l_name` |
| runit | 2.3.1 | tests pass | tests pass | 17 | 99 |  |  |
| scrypt | 1.3.3 | built | built | 39 | 106 |  |  |
| seatd | 0.9.3 | built | built | 6 | 62 |  |  |
| spandsp | 0.0.6 | built | built | 58 | 93 |  |  |
| sqlite | 3.51.2 | built | built | 439 | 64 |  |  |
| strace | 7.2 | fails in buildPhase | not tried |  |  |  |  |
| svt-av1 | 3.1.2 | built | built | 91 | 148 |  |  |
| systemd | 256.4 | tests pass | fails in buildPhase | 57 | 253 | other syntax or typing gaps | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/bits/link.h:99: expected a member declaration, at __int128_t` |
| timidity | 2.15.0 | dependency fails | not tried |  |  |  |  |
| tinycc | 0.9.27-unstable-2025-01-06 | built | built | 11 | 14 |  |  |
| tor | 0.4.9.12 | built | fails in buildPhase | 95 | 499 | vector types | `nanofil: src/core/crypto/relay_crypto_cgo.c:55: member kb of a type nanofil does not support (vector types)` |
| torsocks | 2.5.0 | built | built | 35 | 116 |  |  |
| tpm2-abrmd | 3.0.0 | built | built | 31 | 94 |  |  |
| tpm2-tss | 4.2.0 | tests pass | tests pass | 598 | 1278 |  |  |
| trealla | unstable-2026-09-05 | built | built | 80 | 99 |  |  |
| ttyd | 1.7.7 | built | built | 8 | 9 |  |  |
| unbound | 1.26.0 | tests pass | tests pass | 516 | 734 |  |  |
| util-linux | 2.42.3 | built | built | 243 | 752 |  |  |
| uwimap | 2007f | built | built | 119 | 38 |  |  |
| vala | 0.56.19 | built | built | 405 | 488 |  |  |
| wasm3 | 0.5.0 | built | built | 9 | 19 |  |  |
| wavpack | 5.9.0 | built | built | 19 | 87 |  |  |
| wayland | 1.25.0 | built | built | 9 | 73 |  |  |
| weston | 15.0.1 | built | built | 73 | 349 |  |  |
| x264 | 0-unstable-2025-01-03 | built | fails in buildPhase | 45 | 53 | other syntax or typing gaps | `nanofil: common/macroblock.c:1521: no member named i` |
| xvidcore | 1.3.7 | built | built | 110 | 71 |  |  |
| xz | 5.8.4 | built | fails in buildPhase | 57 | 206 | vector types | `nanofil: ../../src/liblzma/lz/lz_decoder.h:243: vector types is not supported` |
| zix | 0.6.2 | tests pass | tests pass | 24 | 59 |  |  |
| zlib | 1.3.2 | tests pass | tests pass | 5 | 47 |  |  |
| zlib-ng | 2.2.4 | built | built | 64 | 69 |  |  |
| zstd | 1.5.7 | built | fails in buildPhase | 8 | 30 | vector types | `nanofil: /build/source/lib/compress/../common/zstd_internal.h:187: calls returning bad(vector types) are not supported yet` |

<!-- end survey table -->
