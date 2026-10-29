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

The survey of 2026-10-29, at `d2c5a00`: of the 300 packages ports.nix
names, 209 are C. filcc builds 202 of them. Of those 202, nanofil alone
builds 127 (63%; 119 of 201 at `7773472`, 61 of 201 at `06e5f69`),
compiling 31,623 objects. The 41 among them whose ports run tests pass
them, as filcc's builds do. Five build but fail their tests: libressl's
DTLS ssltest, on timing (plain nanofil's bn_mont.c is slow enough that
two RSA CRT halves exceed DTLS's 1 s retransmit timer; its results are
correct); gtksourceview3, gtksourceview4 and libhandy, whose test phases
compile C from stdin (`-x c -`), which the survey's wrapper refuses; and
nspr (`fegetround` at link).

New since `7773472`: coreutils, libgit2, libhighscore, libinput,
libsodium, libvpx, netcdf, rsync and sqlite. x264 regressed again
(`common/macroblock.c:1521: no member named i`). No build lost the nix
daemon in this run; bind and libressl hit a builder's 900 s silence limit
once each.

### Causes

Each failure counts once, under its first error. Removing that cause
gets a package to its next error, not necessarily to a build.

Inline and top-level asm is now the largest row (31), among them glib
itself (`G_BREAKPOINT` in gmessages.c), openssl, openssh, xz, zstd and
util-linux. filcc accepts some of this asm, and reports at run time an
instruction it cannot run safely (dconf's and mbedtls's test failures
show that message), where nanofil refuses at compile time. Alignment
attributes (15) are the next row; gtk4's `gdkresources.c` is one.

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
| built | built | 86 |
| built | fails in buildPhase | 43 |
| tests pass | tests pass | 41 |
| tests pass | fails in buildPhase | 26 |
| tests pass | tests fail | 5 |
| dependency fails | not tried | 4 |
| fails in buildPhase | not tried | 2 |
| tests pass | fails in configurePhase | 1 |
| tests fail | not tried | 1 |

| Cause | Packages | Which |
| --- | ---: | --- |
| other syntax or typing gaps | 22 | binutils-unwrapped, btrfs-progs, emacs30, finit, gnupg, gobject-introspection-unwrapped, gtk3, gtksourceview3, gtksourceview4, imagemagick, kittydoom, kronosnet, libaom, libhandy, libjpeg_turbo, libmbim, libressl, liburcu, mbedtls, nss, x264, zix |
| inline or top-level asm | 19 | ell, fftw, flac, fstrm, guile_3_0, kbd, libblake3, libdeflate, libgcrypt, openssh, openssl, openssl-sarcasm, pcre2, physfs, quickjs, rdkafka, rhash, util-linux, zlib-ng |
| vector types | 6 | gtk4, libopus, libpq, redis, tor, zstd |
| aliases beyond one prototyped function | 5 | alsa-lib, elfutils, fontconfig, gtk2, libapparmor |
| alignment attributes | 5 | bind, libcdio, libtiff, libwebp, xz |
| constant expressions not folded | 5 | ghostscript, libffi, nettle, parted, ruby_3_3 |
| other builtins | 4 | cogl, gnutls, isa-l, libgbm |
| nanofil internal failure | 3 | cryptsetup, cyrus_sasl, trealla |
| unresolved Fil-C symbol at link | 3 | bison, keyutils, nspr |
| __builtin_types_compatible_p, __builtin_choose_expr | 2 | gettext, systemd |
| calls passing arguments to a () function | 1 | gmp |

| Package | Version | filcc | nanofil | nanofil objects | Cause | First error |
| --- | --- | --- | --- | ---: | --- | --- |
| a2ps | 4.15.7 | tests pass | tests pass | 319 |  |  |
| alsa-lib | 1.2.15.3 | built | fails in buildPhase | 65 | aliases beyond one prototyped function | `nanofil: control.c:2974: alias is supported only for one prototyped, non-variadic function` |
| at-spi2-core | 2.60.5 | built | built | 224 |  |  |
| bash | 5.3p9 | built | built | 568 |  |  |
| bashNonInteractive | 5.3p9 | built | built | 573 |  |  |
| bind | 9.20.30 | tests pass | fails in buildPhase |  | alignment attributes | `nanofil: picohttpparser.c:117: alignment attributes is not supported` |
| binutils-unwrapped | 2.43.1 | built | fails in buildPhase | 660 | other syntax or typing gaps | `nanofil: /build/binutils-2.43.1/libiberty/hashtab.c:238: expected an expression, at typedef` |
| bison | 3.8.2 | built | fails in buildPhase | 449 | unresolved Fil-C symbol at link | `src/bison-getargs.o:function pizlonatedFI12770_rpl_printf:(.text+0x436fd): error: undefined reference to 'pizlonated_rpl_printf'` |
| bluez | 5.86 | fails in buildPhase | not tried |  |  |  |
| btrfs-progs | 6.19.1 | tests pass | fails in buildPhase | 133 | other syntax or typing gaps | `nanofil: kernel-shared/print-tree.c:582: unknown escape \(` |
| busybox | 1.37.0 | built | built | 14 |  |  |
| cairo | 1.18.4 | built | built | 275 |  |  |
| capstone | 5.0.7 | tests pass | tests pass | 128 |  |  |
| cmocka | 2.0.1 | built | built | 82 |  |  |
| cogl | 1.22.8 | built | fails in buildPhase | 193 | other builtins | `nanofil: deprecated/cogl-fixed.c:744: undeclared identifier __builtin_sqrt` |
| coreutils | 9.11 | built | built | 1248 |  |  |
| cryptsetup | 2.8.6 | tests pass | fails in buildPhase | 163 | nanofil internal failure | `nanofil: failed` |
| cups | 2.4.19 | built | built | 244 |  |  |
| curl | 8.22.0 | built | built | 466 |  |  |
| cyrus_sasl | 2.1.28 | built | fails in buildPhase | 225 | nanofil internal failure | `nanofil: failed` |
| dash | 0.5.12 | built | built | 96 |  |  |
| dav1d | 1.5.3 | tests pass | tests pass | 87 |  |  |
| db53 | 5.3.28 | tests pass | tests pass | 512 |  |  |
| dbus | 1.16.2 | tests pass | tests pass | 291 |  |  |
| dbus-glib | 0.114 | built | built | 68 |  |  |
| dconf | 0.49.0 | tests pass | tests pass | 84 |  |  |
| diffutils | 3.12 | built | built | 565 |  |  |
| duktape | 2.7.0 | built | built | 8 |  |  |
| e2fsprogs | 1.47.4 | built | built | 557 |  |  |
| elfutils | 0.194 | built | fails in buildPhase | 196 | aliases beyond one prototyped function | `nanofil: elf_getshdrnum.c:87: alias is supported only for one prototyped, non-variadic function` |
| ell | 0.83 | built | fails in buildPhase | 49 | inline or top-level asm | `nanofil: ell/util.c:794: the asm input constraint "0" is not supported` |
| emacs30 | 30.1 | built | fails in buildPhase | 519 | other syntax or typing gaps | `filc safety error: cannot write pointer with null object.` |
| expat | 2.7.1 | tests pass | tests pass | 89 |  |  |
| ffmpeg-headless | 8.1.2 | dependency fails | not tried |  |  |  |
| fftw | 3.3.11 | tests pass | fails in buildPhase | 183 | inline or top-level asm | `nanofil: ./cycle.h:226: inline asm "rdtsc" is not supported: nanofil cannot check its instructions` |
| file | 5.47 | built | built | 141 |  |  |
| finit | 4.17 | built | fails in buildPhase | 56 | other syntax or typing gaps | `nanofil: getty.c:407: bad number 1i` |
| flac | 1.5.0 | tests pass | fails in buildPhase | 38 | inline or top-level asm | `nanofil: /build/flac-1.5.0/src/libFLAC/cpu.c:80: inline asm "xgetbv" is not supported: nanofil cannot check its instructions` |
| fontconfig | 2.17.1 | built | fails in buildPhase | 115 | aliases beyond one prototyped function | `nanofil: ./fcaliastail.h:194: alias is supported only for one prototyped, non-variadic function` |
| freetype | 2.14.3 | tests pass | tests pass | 138 |  |  |
| fstrm | 0.6.1 | tests pass | fails in buildPhase | 60 | inline or top-level asm | `nanofil: libmy/my_queue_mb.c:132: inline asm "mfence" is not supported: nanofil cannot check its instructions` |
| gawk | 5.4.1 | built | built | 275 |  |  |
| gd | 2.3.3 | built | built | 112 |  |  |
| gdk-pixbuf | 2.44.7 | built | built | 91 |  |  |
| gettext | 1.0 | built | fails in buildPhase | 1579 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: __builtin_choose_expr needs a constant condition` |
| ghostscript | 10.07.1 | built | fails in buildPhase | 423 | constant expressions not folded | `nanofil: ./base/gp_unifs.c:274: initializer is not a constant` |
| git | 2.46.0 | built | built | 596 |  |  |
| glib | 2.80.4 | built | built | 879 |  |  |
| gmp | 6.3.0 | tests pass | fails in configurePhase | 30 | calls passing arguments to a () function | `configure: error: could not find a working compiler, see config.log for details` |
| gnu-shepherd | 1.0.9 | built | built | 240 |  |  |
| gnugrep | 3.12 | built | built | 528 |  |  |
| gnum4 | 1.4.21 | built | built | 645 |  |  |
| gnumake | 4.4.1 | tests pass | tests pass | 153 |  |  |
| gnupg | 2.4.9 | tests pass | fails in buildPhase | 362 | other syntax or typing gaps | `nanofil: keyring.c:274: cannot assign struct(176) to struct(177)` |
| gnused | 4.10 | built | built | 493 |  |  |
| gnutar | 1.35 | tests pass | tests pass | 593 |  |  |
| gnutls | 3.8.13 | built | fails in buildPhase | 664 | other builtins | `nanofil: key_share.c:256: undeclared identifier __builtin_return_address` |
| gobject-introspection-unwrapped | 1.80.1 | tests pass | fails in buildPhase | 160 | other syntax or typing gaps | `filc safety error: cannot read pointer with null object.` |
| graphene | 1.10.8 | tests pass | tests pass | 66 |  |  |
| gsl | 2.8 | tests pass | tests pass | 1060 |  |  |
| gssdp_1_6 | 1.6.6 | tests pass | tests pass | 32 |  |  |
| gtk2 | 2.24.33 | built | fails in buildPhase | 96 | aliases beyond one prototyped function | `nanofil: ../../gdk/gdkaliasdef.c:722: alias is supported only for one prototyped, non-variadic function` |
| gtk3 | 3.24.52 | built | fails in buildPhase | 182 | other syntax or typing gaps | `nanofil: error(resource_error(stack),stack_overflow{choicepoints:8,depth:763214,environments:22,globalused:1044595,localused:4,stack:[frame(763214,c_types:convert_int(115,uchar,_138),[]),frame(763211,c_lower:static_leaf((:)/2,expr/3,s/3,s/3),[]),frame(763210,system:once((:)/2),[]),frame(763208,apply` |
| gtk4 | 4.14.5 | built | fails in buildPhase | 223 | vector types | `nanofil: ../gsk/gskpath.c:521: member contour of a type nanofil does not support (vector types)` |
| gtksourceview3 | 3.24.11 | tests pass | tests fail | 180 | other syntax or typing gaps | `nanofil-survey-cc: refused, not a .c compile nanofil-cc can do: -x c - -I/nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include -I/nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0 -I/nix/store/3qibns6` |
| gtksourceview4 | 4.8.4 | tests pass | tests fail | 182 | other syntax or typing gaps | `nanofil-survey-cc: refused, not a .c compile nanofil-cc can do: -x c - -I/nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include -I/nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0 -I/nix/store/3qibns6` |
| guile-avahi | 0.4.1 | tests pass | tests pass | 49 |  |  |
| guile_3_0 | 3.0.11 | built | fails in buildPhase | 672 | inline or top-level asm | `nanofil: deprecated.c:591: an asm operand must have integer or floating type` |
| gupnp_1_6 | 1.6.10 | tests pass | tests pass | 57 |  |  |
| imagemagick | 7.1.2-31 | built | fails in buildPhase | 341 | other syntax or typing gaps | `nanofil: MagickCore/fourier.c:1295: bad number 1.0iF` |
| imlib2 | 1.12.6 | built | built | 133 |  |  |
| isa-l | 2.32.0 | tests pass | fails in buildPhase | 51 | other builtins | `nanofil: /nix/store/asx904awk86a38cr62zyxqq1zf10603m-filc0-resource-dir/lib/clang/20/include/crc32intrin.h:73: undeclared identifier __builtin_ia32_crc32si` |
| jq | 1.8.2 | built | built | 152 |  |  |
| json-glib | 1.10.8 | tests pass | tests pass | 81 |  |  |
| kbd | 2.9.0 | built | fails in buildPhase | 155 | inline or top-level asm | `nanofil: resizecons.c:400: inline asm "inb %1,%0" is not supported: nanofil cannot check its instructions` |
| keyutils | 1.6.3 | built | fails in buildPhase | 8 | unresolved Fil-C symbol at link | `./libkeyutils.so: error: undefined reference to 'pizlonated_zargs'` |
| kittydoom | git | built | fails in buildPhase | 1 | other syntax or typing gaps | `nanofil: src/PureDOOM.h:16108: invalid operands to and: int and double` |
| krb5 | 1.22.2 | built | built | 1020 |  |  |
| kronosnet | 1.33 | built | fails in buildPhase | 95 | other syntax or typing gaps | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/bits/link.h:99: expected a member declaration, at __int128_t` |
| libaom | 3.12.1 | built | fails in buildPhase | 187 | other syntax or typing gaps | `nanofil: error(resource_error(stack),stack_overflow{choicepoints:11,depth:21674,environments:22,globalused:1046703,localused:5,stack:[frame(21674,apply:exclude_([5965],(:)/2,_138),[]),frame(21252,ir:checked_inst_rest(flight/4,[83141],prepare_tf_workers,filc,[6384],[83141],[419\|_210]),[]),frame(21251` |
| libapparmor | 4.1.7 | built | fails in buildPhase | 47 | aliases beyond one prototyped function | `nanofil: kernel.c:831: alias is supported only for one prototyped, non-variadic function` |
| libarchive | 3.7.4 | built | built | 425 |  |  |
| libblake3 | 1.8.5 | built | fails in buildPhase | 4 | inline or top-level asm | `nanofil: /build/source/c/blake3_dispatch.c:70: inline asm "cpuid` |
| libcap | 2.70 | built | built | 16 |  |  |
| libcap_ng | 0.9.3 | tests pass | tests pass | 67 |  |  |
| libcbor | 0.13.0 | tests pass | tests pass | 134 |  |  |
| libcdio | 2.3.0 | tests pass | fails in buildPhase | 137 | alignment attributes | `nanofil: image/nrg.c:195: buf has a type nanofil does not support (alignment attributes)` |
| libdbusmenu | 16.04.0 | built | built | 55 |  |  |
| libdeflate | 1.25 | tests pass | fails in buildPhase | 21 | inline or top-level asm | `nanofil: /build/source/lib/x86/cpu_features.c:47: inline asm "cpuid" is not supported: nanofil cannot check its instructions` |
| libedit | 20240808-3.1 | built | built | 115 |  |  |
| libepoxy | 1.5.10 | tests pass | tests pass | 71 |  |  |
| libev | 4.33 | built | built | 56 |  |  |
| libevdev | 1.11.0 | built | built | 60 |  |  |
| libevent | 2.1.13 | built | built | 254 |  |  |
| libffi | 3.8.0 | tests pass | fails in buildPhase | 62 | constant expressions not folded | `nanofil: ../src/types.c:126: initializer is not a constant` |
| libgbm | 26.0.3 | built | fails in buildPhase | 148 | other builtins | `nanofil: ../src/util/cache_ops_x86.c:68: undeclared identifier __builtin_ia32_mfence` |
| libgcrypt | 1.12.2 | tests pass | fails in buildPhase | 129 | inline or top-level asm | `nanofil: mpiutil.c:150: an asm operand must have integer or floating type` |
| libgit2 | 1.9.7 | tests pass | tests pass | 698 |  |  |
| libglvnd | 1.7.0 | built | built | 85 |  |  |
| libgpg-error | 1.59 | tests pass | tests pass | 162 |  |  |
| libgsf | 1.14.58 | tests pass | tests pass | 164 |  |  |
| libgudev | 238 | built | built | 16 |  |  |
| libhandy | 1.8.3 | tests pass | tests fail | 144 | other syntax or typing gaps | `nanofil-survey-cc: refused, not a .c compile nanofil-cc can do: -x c - -I/nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include -I/nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0 -I/nix/store/3qibns6` |
| libhighscore | 0-unstable-2026-04-01 | tests pass | tests pass | 106 |  |  |
| libical | 3.0.20 | built | built | 228 |  |  |
| libiconv | 1.19 | built | built | 266 |  |  |
| libidn2 | 2.3.8 | built | built | 228 |  |  |
| libinput | 1.29.1 | built | built | 125 |  |  |
| libjpeg_turbo | 3.1.4 | built | fails in buildPhase | 22 | other syntax or typing gaps | `nanofil: /nix/store/10xdyb6i0ahryz4a85xp747zwkh7g7xw-simde-0.8.2/include/simde/arm/neon/movl.h:54: expected an expression, at typeof` |
| liblc3 | 1.1.3 | built | built | 15 |  |  |
| libmbim | 1.34.0 | tests pass | fails in buildPhase | 52 | other syntax or typing gaps | `nanofil: ../src/libmbim-glib/mbim-device.c:2447: pointer arithmetic on struct(627) (packed pointers)` |
| libmhash | 0.9.9.9 | tests pass | tests pass | 140 |  |  |
| libmicrohttpd | 1.0.2 | built | built | 278 |  |  |
| libmpdclient | 2.24 | tests pass | tests pass | 98 |  |  |
| libopus | 1.6.1 | tests pass | fails in buildPhase | 35 | vector types | `nanofil: ../celt/float_cast.h:68: calls returning bad(vector types) are not supported yet` |
| libpng | 1.6.43 | built | built | 71 |  |  |
| libpq | 18.6 | built | fails in buildPhase | 304 | vector types | `nanofil: jsonapi.c:2218: vector types is not supported` |
| libraqm | 0.10.5 | tests pass | tests pass | 14 |  |  |
| libressl | 4.2.1 | tests pass | tests fail |  | other syntax or typing gaps | `133/134 Test  #29: bn_mod_exp .......................   Passed  992.83 sec` |
| libseccomp | 2.6.1 | tests pass | tests pass | 161 |  |  |
| libselinux | 3.10 | built | built | 151 |  |  |
| libsepol | 3.10 | built | built | 140 |  |  |
| libshout | 2.4.6 | built | built | 92 |  |  |
| libsodium | 1.0.22-unstable-2026-04-09 | tests pass | tests pass | 376 |  |  |
| libsoup_3 | 3.6.6 | built | built | 235 |  |  |
| libssh2 | 1.11.1 | built | built | 88 |  |  |
| libtasn1 | 4.21.0 | built | built | 224 |  |  |
| libtiff | 4.7.2 | tests pass | fails in buildPhase | 61 | alignment attributes | `nanofil: /build/source/libtiff/tif_predict.c:605: alignment attributes is not supported` |
| libtirpc | 1.3.7 | tests pass | tests pass | 131 |  |  |
| liburcu | 0.15.6 | tests pass | fails in buildPhase | 124 | other syntax or typing gaps | `nanofil: cds_hlist_for_each_entry_rcu.c:67: expected a parameter declaration, at {` |
| libuv | 1.52.1 | built | built | 94 |  |  |
| libvmaf | 3.0.0 | tests pass | tests pass | 129 |  |  |
| libvpx | 1.16.0 | built | built | 225 |  |  |
| libwebp | 1.6.0 | built | fails in buildPhase | 33 | alignment attributes | `nanofil: /build/source/sharpyuv/sharpyuv_sse2.c:85: alignment attributes is not supported` |
| libxcrypt | 4.5.2 | built | built | 129 |  |  |
| libxkbcommon | 1.13.1 | built | built | 393 |  |  |
| libxml2 | 2.15.4 | built | built | 82 |  |  |
| lighttpd | 1.4.85 | built | built | 295 |  |  |
| lttng-ust | 2.14.0 | tests fail | not tried |  |  |  |
| lzo | 2.10 | built | built | 289 |  |  |
| mailutils | 3.21 | tests pass | tests pass | 1157 |  |  |
| mariadb-connector-c_3_3 | 3.3.5 | built | built | 159 |  |  |
| mbedtls | 3.6.6 | tests pass | fails in buildPhase | 30 | other syntax or typing gaps | `nanofil: /build/source/library/bignum_core.c:480: mode TI (__int128) is not supported` |
| minizip | 1.3.2 | built | built | 35 |  |  |
| mpdecimal | 4.0.1 | built | built | 44 |  |  |
| mpfr | 4.2.2 | tests pass | tests pass | 540 |  |  |
| mpg123 | 1.33.7 | dependency fails | not tried |  |  |  |
| netcdf | 4.9.3 | tests pass | tests pass | 705 |  |  |
| nettle | 3.10.2 | tests pass | fails in buildPhase | 443 | constant expressions not folded | `nanofil: ecc-secp224r1.c:212: initializer is not an address constant` |
| nghttp2 | 1.69.0 | built | built | 127 |  |  |
| nspr | 4.40 | tests pass | tests fail | 98 | unresolved Fil-C symbol at link | `../../dist/lib/libnspr4.so: error: undefined reference to 'pizlonated_fegetround'` |
| nss | 3.112.5 | tests pass | fails in buildPhase | 367 | other syntax or typing gaps | `nanofil: ../../lib/freebl/gcm.c:135: __int128 is not supported` |
| oniguruma | 6.9.10 | built | built | 104 |  |  |
| openssh | 10.5p1 | built | fails in buildPhase | 661 | inline or top-level asm | `nanofil: sntrup761.c:62: inline asm "sarw $15,%0" is not supported: nanofil cannot check its instructions` |
| openssl | 3.5.7 | built | fails in buildPhase | 150 | inline or top-level asm | `nanofil: include/internal/constant_time.h:154: the asm input constraint "0" is not supported` |
| openssl-sarcasm | 3.6.4 | tests pass | fails in buildPhase | 138 | inline or top-level asm | `nanofil: crypto/bn/bn_div.c:388: inline asm "divq   %4" is not supported: nanofil cannot check its instructions` |
| p11-kit | 0.26.2 | built | built | 289 |  |  |
| pam | 1.7.2 | built | built | 239 |  |  |
| pango | 1.56.3 | built | built | 163 |  |  |
| parted | 3.7 | tests pass | fails in buildPhase | 335 | constant expressions not folded | `nanofil: gpt.c:1944: static assertion is not a constant` |
| pcre2 | 10.48 | built | fails in buildPhase | 73 | inline or top-level asm | `nanofil: src/../deps/sljit/sljit_src/sljitNativeX86_common.c:462: inline asm "cpuid` |
| perl5 | 5.40.0 | built | built | 745 |  |  |
| physfs | 3.2.0 | built | fails in buildPhase | 42 | inline or top-level asm | `nanofil: /build/source/src/physfs_lzmasdk.h:1495: inline asm "cpuid" is not supported: nanofil cannot check its instructions` |
| pixman | 0.46.4 | built | built | 119 |  |  |
| polkit | 127 | tests pass | tests pass | 71 |  |  |
| potrace | 1.16 | tests pass | tests pass | 67 |  |  |
| procps | 4.0.6 | built | built | 187 |  |  |
| pth | 2.0.7 | tests pass | tests pass | 112 |  |  |
| pulseaudio | 17.0 | dependency fails | not tried |  |  |  |
| python312 | 3.12.5 | built | built | 858 |  |  |
| quickjs | 2026-06-04 | tests pass | fails in buildPhase | 9 | inline or top-level asm | `nanofil: quickjs.c:60630: inline asm "pause" is not supported: nanofil cannot check its instructions` |
| rdkafka | 2.13.0 | built | fails in buildPhase | 23 | inline or top-level asm | `nanofil: /build/source/src/queue.h:688: an asm operand must have integer or floating type` |
| recode | 3.7.15 | tests pass | tests pass | 293 |  |  |
| redis | 8.8.2 | tests pass | fails in buildPhase | 90 | vector types | `nanofil: ./xxhash.h:5220: vector types is not supported` |
| rhash | 1.4.6 | tests pass | fails in buildPhase | 6 | inline or top-level asm | `nanofil: calc_sums.c:555: inline asm "rdtsc" is not supported: nanofil cannot check its instructions` |
| rpcbind | 1.2.6 | built | built | 31 |  |  |
| rsync | 3.5.0 | tests pass | tests pass | 378 |  |  |
| ruby_3_3 | 3.3.10 | built | fails in buildPhase | 575 | constant expressions not folded | `nanofil: ./ast.rbinc:15: initializer is not an address constant` |
| runit | 2.3.1 | tests pass | tests pass | 98 |  |  |
| scrypt | 1.3.3 | built | built | 106 |  |  |
| seatd | 0.9.3 | built | built | 62 |  |  |
| spandsp | 0.0.6 | built | built | 93 |  |  |
| sqlite | 3.51.2 | built | built | 64 |  |  |
| strace | 7.2 | fails in buildPhase | not tried |  |  |  |
| svt-av1 | 3.1.2 | built | built | 148 |  |  |
| systemd | 256.4 | built | fails in buildPhase | 245 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: __builtin_choose_expr needs a constant condition` |
| timidity | 2.15.0 | dependency fails | not tried |  |  |  |
| tinycc | 0.9.27-unstable-2025-01-06 | built | built | 13 |  |  |
| tor | 0.4.9.12 | built | fails in buildPhase | 497 | vector types | `nanofil: src/core/crypto/relay_crypto_cgo.c:55: member kb of a type nanofil does not support (vector types)` |
| torsocks | 2.5.0 | built | built | 116 |  |  |
| tpm2-abrmd | 3.0.0 | built | built | 94 |  |  |
| tpm2-tss | 4.2.0 | built | built | 1278 |  |  |
| trealla | unstable-2026-09-05 | built | fails in buildPhase | 41 | nanofil internal failure | `nanofil: failed` |
| ttyd | 1.7.7 | built | built | 9 |  |  |
| unbound | 1.26.0 | tests pass | tests pass | 734 |  |  |
| util-linux | 2.42.3 | built | fails in buildPhase | 363 | inline or top-level asm | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/sys/io.h:47: inline asm "inb %w1,%0" is not supported: nanofil cannot check its instructions` |
| uwimap | 2007f | built | built | 38 |  |  |
| vala | 0.56.19 | built | built | 488 |  |  |
| wasm3 | 0.5.0 | built | built | 19 |  |  |
| wavpack | 5.9.0 | built | built | 87 |  |  |
| wayland | 1.25.0 | built | built | 73 |  |  |
| weston | 15.0.1 | built | built | 349 |  |  |
| x264 | 0-unstable-2025-01-03 | built | fails in buildPhase | 38 | other syntax or typing gaps | `nanofil: common/macroblock.c:1521: no member named i` |
| xvidcore | 1.3.7 | built | built | 71 |  |  |
| xz | 5.8.4 | built | fails in buildPhase | 197 | alignment attributes | `nanofil: ../../src/liblzma/lz/lz_decoder.h:243: alignment attributes is not supported` |
| zix | 0.6.2 | tests pass | fails in buildPhase | 21 | other syntax or typing gaps | `nanofil: ../include/zix/allocator.h:97: expected ;, at malloc` |
| zlib | 1.3.2 | tests pass | tests pass | 47 |  |  |
| zlib-ng | 2.2.4 | built | fails in buildPhase | 62 | inline or top-level asm | `nanofil: /build/zlib-ng-2.2.4/arch/x86/x86_features.c:64: inline asm ".byte 0x0f, 0x01, 0xd0" is not supported: nanofil cannot check its instructions` |
| zstd | 1.5.7 | built | fails in buildPhase | 27 | vector types | `nanofil: /build/source/lib/compress/../common/zstd_internal.h:187: calls returning bad(vector types) are not supported yet` |

<!-- end survey table -->
