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

The survey of 2026-10-29, at `d3d20fe`: of the 300 packages ports.nix
names, 209 are C. filcc builds 202 of them. Of those 202, nanofil alone
builds 115 (57%; 114 at `3db16ed`, 96 at `eb1ff00`, 61 of 201 at
`06e5f69`), compiling 26,057 objects. The 36 among them whose ports run
tests pass them, as filcc's builds do. Four build but fail their tests:
libgcrypt (an integer-rebuilt pointer, fixed by a port patch after this
survey; docs/ub.md), netcdf (\"undefined filter encountered\"), tpm2-tss
(`__builtin_choose_expr` with a non-constant condition in a test) and
nspr (`fegetround` at link). The other 83 fail: 81 while building and 2
in configure.

New since `3db16ed`: dconf (its leak tests pass now that `cleanup` is
honored), libseccomp, libvpx, libxkbcommon, torsocks and x264. Lost:
libinput (a `cleanup` attribute on a multi-declarator declaration),
libxcrypt (top-level asm, handled after this survey), rsync (configure),
tpm2-tss (as above), and sqlite, whose `-O` build of the amalgamation
overflows the 1 GB Prolog stack in a `maplist` (the nanofil-sqlite check
still passes). Attributes refused as a first error: noescape (redis,
zstd) and weakref (ruby).

### Causes

Each failure counts once, under its first error. Removing that cause
gets a package to its next error, not necessarily to a build.

Inline and top-level asm is now the largest row (31), among them glib
itself (`G_BREAKPOINT` in gmessages.c), openssl, openssh, xz, zstd and
util-linux. filcc accepts some of this asm, and reports at run time an
instruction it cannot run safely (dconf's and mbedtls's test failures
show that message), where nanofil refuses at compile time. Alignment
attributes (15) are the next row; gtk4's `gdkresources.c` is one.

<!-- survey table -->

| Set aside | Packages |
| --- | ---: |
| C++ | 59 |
| evaluation fails | 20 |
| no C sources found | 12 |

| filcc | nanofil | Packages |
| --- | --- | ---: |
| built | built | 79 |
| built | fails in buildPhase | 49 |
| tests pass | tests pass | 36 |
| tests pass | fails in buildPhase | 32 |
| dependency fails | not tried | 4 |
| tests pass | tests fail | 3 |
| fails in buildPhase | not tried | 2 |
| tests pass | fails in configurePhase | 2 |
| tests fail | not tried | 1 |
| built | tests fail | 1 |

| Cause | Packages | Which |
| --- | ---: | --- |
| inline or top-level asm | 30 | cogl, cryptsetup, dav1d, fftw, flac, fstrm, glib, guile_3_0, kbd, krb5, libapparmor, libblake3, libdeflate, libressl, libsodium, libxcrypt, lighttpd, mariadb-connector-c_3_3, nss, openssh, openssl, openssl-sarcasm, pcre2, physfs, quickjs, rdkafka, rhash, util-linux, xz, zlib-ng |
| other syntax or typing gaps | 24 | binutils-unwrapped, btrfs-progs, emacs30, finit, gnupg, gobject-introspection-unwrapped, imagemagick, kittydoom, kronosnet, libaom, libgcrypt, libinput, libjpeg_turbo, libmbim, liburcu, mbedtls, netcdf, redis, rsync, ruby_3_3, sqlite, systemd, zix, zstd |
| alignment attributes | 14 | bind, ell, gtk3, gtk4, gtksourceview3, gtksourceview4, libcdio, libhandy, libhighscore, libopus, libpq, libtiff, libwebp, tor |
| aliases beyond one prototyped function | 4 | alsa-lib, elfutils, fontconfig, gtk2 |
| constant expressions not folded | 4 | ghostscript, libffi, nettle, parted |
| other builtins | 3 | gnutls, isa-l, libgbm |
| unresolved Fil-C symbol at link | 3 | bison, keyutils, nspr |
| __builtin_types_compatible_p, __builtin_choose_expr | 2 | gettext, tpm2-tss |
| nanofil internal failure | 2 | cyrus_sasl, trealla |
| calls passing arguments to a () function | 1 | gmp |

| Package | Version | filcc | nanofil | nanofil objects | Cause | First error |
| --- | --- | --- | --- | ---: | --- | --- |
| a2ps | 4.15.7 | tests pass | tests pass | 319 |  |  |
| alsa-lib | 1.2.15.3 | built | fails in buildPhase | 65 | aliases beyond one prototyped function | `nanofil: control.c:2974: alias is supported only for one prototyped, non-variadic function` |
| at-spi2-core | 2.60.5 | built | built | 224 |  |  |
| bash | 5.3p9 | built | built | 568 |  |  |
| bashNonInteractive | 5.3p9 | built | built | 573 |  |  |
| bind | 9.20.30 | tests pass | fails in buildPhase |  | alignment attributes | `nanofil: picohttpparser.c:117: alignment attributes is not supported` |
| binutils-unwrapped | 2.43.1 | built | fails in buildPhase | 662 | other syntax or typing gaps | `nanofil: /build/binutils-2.43.1/libiberty/hashtab.c:238: expected an expression, at typedef` |
| bison | 3.8.2 | built | fails in buildPhase | 449 | unresolved Fil-C symbol at link | `src/bison-getargs.o:function pizlonatedFI12770_rpl_printf:(.text+0x436fd): error: undefined reference to 'pizlonated_rpl_printf'` |
| bluez | 5.86 | fails in buildPhase | not tried |  |  |  |
| btrfs-progs | 6.19.1 | tests pass | fails in buildPhase | 135 | other syntax or typing gaps | `nanofil: kernel-shared/print-tree.c:582: unknown escape \(` |
| busybox | 1.37.0 | built | built | 14 |  |  |
| cairo | 1.18.4 | built | built | 275 |  |  |
| capstone | 5.0.7 | tests pass | tests pass | 128 |  |  |
| cmocka | 2.0.1 | built | built | 82 |  |  |
| cogl | 1.22.8 | built | fails in buildPhase | 126 | inline or top-level asm | `nanofil: cogl-bitmap-conversion.c:158: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| coreutils | 9.11 | built | built | 1248 |  |  |
| cryptsetup | 2.8.6 | tests pass | fails in buildPhase | 102 | inline or top-level asm | `nanofil: lib/keyslot_context.c:807: top-level asm is not supported, at (` |
| cups | 2.4.19 | built | built | 244 |  |  |
| curl | 8.22.0 | built | built | 466 |  |  |
| cyrus_sasl | 2.1.28 | built | fails in buildPhase | 225 | nanofil internal failure | `nanofil: failed` |
| dash | 0.5.12 | built | built | 96 |  |  |
| dav1d | 1.5.3 | tests pass | fails in buildPhase | 40 | inline or top-level asm | `nanofil: ../src/recon_tmpl.c:150: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| db53 | 5.3.28 | tests pass | tests pass | 512 |  |  |
| dbus | 1.16.2 | tests pass | tests pass | 291 |  |  |
| dbus-glib | 0.114 | built | built | 68 |  |  |
| dconf | 0.49.0 | tests pass | tests pass | 84 |  |  |
| diffutils | 3.12 | built | built | 565 |  |  |
| duktape | 2.7.0 | built | built | 8 |  |  |
| e2fsprogs | 1.47.4 | built | built | 557 |  |  |
| elfutils | 0.194 | built | fails in buildPhase | 186 | aliases beyond one prototyped function | `nanofil: elf_getshdrnum.c:87: alias is supported only for one prototyped, non-variadic function` |
| ell | 0.83 | built | fails in buildPhase | 63 | alignment attributes | `nanofil: ell/log.c:103: alignment attributes is not supported` |
| emacs30 | 30.1 | built | fails in buildPhase | 519 | other syntax or typing gaps | `filc safety error: cannot write pointer with null object.` |
| expat | 2.7.1 | tests pass | tests pass | 89 |  |  |
| ffmpeg-headless | 8.1.2 | dependency fails | not tried |  |  |  |
| fftw | 3.3.11 | tests pass | fails in buildPhase | 183 | inline or top-level asm | `nanofil: ./cycle.h:226: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| file | 5.47 | built | built | 141 |  |  |
| finit | 4.17 | built | fails in buildPhase | 56 | other syntax or typing gaps | `nanofil: getty.c:407: bad number 1i` |
| flac | 1.5.0 | tests pass | fails in buildPhase | 45 | inline or top-level asm | `nanofil: /build/flac-1.5.0/src/libFLAC/cpu.c:80: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| fontconfig | 2.17.1 | built | fails in buildPhase | 115 | aliases beyond one prototyped function | `nanofil: ./fcaliastail.h:144: alias is supported only for one prototyped, non-variadic function` |
| freetype | 2.14.3 | tests pass | tests pass | 138 |  |  |
| fstrm | 0.6.1 | tests pass | fails in buildPhase | 60 | inline or top-level asm | `nanofil: libmy/my_queue_mb.c:132: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| gawk | 5.4.1 | built | built | 275 |  |  |
| gd | 2.3.3 | built | built | 112 |  |  |
| gdk-pixbuf | 2.44.7 | built | built | 91 |  |  |
| gettext | 1.0 | built | fails in buildPhase | 1579 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: __builtin_choose_expr needs a constant condition` |
| ghostscript | 10.07.1 | built | fails in buildPhase | 423 | constant expressions not folded | `nanofil: ./base/gp_unifs.c:274: initializer is not a constant` |
| git | 2.46.0 | built | built | 596 |  |  |
| glib | 2.80.4 | built | fails in buildPhase | 424 | inline or top-level asm | `nanofil: ../glib/gmessages.c:426: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| gmp | 6.3.0 | tests pass | fails in configurePhase | 30 | calls passing arguments to a () function | `configure: error: could not find a working compiler, see config.log for details` |
| gnu-shepherd | 1.0.9 | built | built | 240 |  |  |
| gnugrep | 3.12 | built | built | 528 |  |  |
| gnum4 | 1.4.21 | built | built | 645 |  |  |
| gnumake | 4.4.1 | tests pass | tests pass | 153 |  |  |
| gnupg | 2.4.9 | tests pass | fails in buildPhase | 370 | other syntax or typing gaps | `nanofil: keyring.c:274: cannot assign struct(176) to struct(177)` |
| gnused | 4.10 | built | built | 493 |  |  |
| gnutar | 1.35 | tests pass | tests pass | 593 |  |  |
| gnutls | 3.8.13 | built | fails in buildPhase | 664 | other builtins | `nanofil: key_share.c:256: undeclared identifier __builtin_return_address` |
| gobject-introspection-unwrapped | 1.80.1 | tests pass | fails in buildPhase | 160 | other syntax or typing gaps | `filc safety error: cannot read pointer with null object.` |
| graphene | 1.10.8 | tests pass | tests pass | 66 |  |  |
| gsl | 2.8 | tests pass | tests pass | 1060 |  |  |
| gssdp_1_6 | 1.6.6 | tests pass | tests pass | 32 |  |  |
| gtk2 | 2.24.33 | built | fails in buildPhase | 96 | aliases beyond one prototyped function | `nanofil: ../../gdk/gdkaliasdef.c:722: alias is supported only for one prototyped, non-variadic function` |
| gtk3 | 3.24.52 | built | fails in buildPhase | 114 | alignment attributes | `nanofil: gdk/gdkresources.c:9: alignment attributes is not supported` |
| gtk4 | 4.14.5 | built | fails in buildPhase | 153 | alignment attributes | `nanofil: gdk/gdkresources.c:9: alignment attributes is not supported` |
| gtksourceview3 | 3.24.11 | tests pass | fails in buildPhase | 147 | alignment attributes | `nanofil: gtksourceview-resources.c:9: alignment attributes is not supported` |
| gtksourceview4 | 4.8.4 | tests pass | fails in buildPhase | 68 | alignment attributes | `nanofil: gtksourceview/gtksourceview-gresources.c:9: alignment attributes is not supported` |
| guile-avahi | 0.4.1 | tests pass | tests pass | 49 |  |  |
| guile_3_0 | 3.0.11 | built | fails in buildPhase | 672 | inline or top-level asm | `nanofil: deprecated.c:591: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| gupnp_1_6 | 1.6.10 | tests pass | tests pass | 57 |  |  |
| imagemagick | 7.1.2-31 | built | fails in buildPhase | 342 | other syntax or typing gaps | `nanofil: MagickCore/fourier.c:1295: bad number 1.0iF` |
| imlib2 | 1.12.6 | built | built | 133 |  |  |
| isa-l | 2.32.0 | tests pass | fails in buildPhase | 51 | other builtins | `nanofil: /nix/store/asx904awk86a38cr62zyxqq1zf10603m-filc0-resource-dir/lib/clang/20/include/crc32intrin.h:73: undeclared identifier __builtin_ia32_crc32si` |
| jq | 1.8.2 | built | built | 152 |  |  |
| json-glib | 1.10.8 | tests pass | tests pass | 81 |  |  |
| kbd | 2.9.0 | built | fails in buildPhase | 159 | inline or top-level asm | `nanofil: resizecons.c:400: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| keyutils | 1.6.3 | built | fails in buildPhase | 8 | unresolved Fil-C symbol at link | `./libkeyutils.so: error: undefined reference to 'pizlonated_zargs'` |
| kittydoom | git | built | fails in buildPhase | 1 | other syntax or typing gaps | `nanofil: src/PureDOOM.h:16108: invalid operands to and: int and double` |
| krb5 | 1.22.2 | built | fails in buildPhase | 885 | inline or top-level asm | `nanofil: ./edwards25519_fiat.h:890: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| kronosnet | 1.33 | built | fails in buildPhase | 95 | other syntax or typing gaps | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/bits/link.h:99: expected a member declaration, at __int128_t` |
| libaom | 3.12.1 | built | fails in buildPhase | 172 | other syntax or typing gaps | `nanofil: error(resource_error(stack),stack_overflow{choicepoints:11,depth:25638,environments:21,globalused:1046071,localused:5,stack:[frame(25638,apply:exclude_([1995],(:)/2,_138),[]),frame(21248,ir:checked_inst_rest(flight/4,[83147],prepare_tf_workers,filc,[6382],[83147],[4387\|_210]),[]),frame(2124` |
| libapparmor | 4.1.7 | built | fails in buildPhase | 47 | inline or top-level asm | `nanofil: kernel.c:832: top-level asm is not supported, at (` |
| libarchive | 3.7.4 | built | built | 425 |  |  |
| libblake3 | 1.8.5 | built | fails in buildPhase | 4 | inline or top-level asm | `nanofil: /build/source/c/blake3_dispatch.c:70: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| libcap | 2.70 | built | built | 16 |  |  |
| libcap_ng | 0.9.3 | tests pass | tests pass | 67 |  |  |
| libcbor | 0.13.0 | tests pass | tests pass | 134 |  |  |
| libcdio | 2.3.0 | tests pass | fails in buildPhase | 137 | alignment attributes | `nanofil: image/nrg.c:195: buf has a type nanofil does not support (alignment attributes)` |
| libdbusmenu | 16.04.0 | built | built | 55 |  |  |
| libdeflate | 1.25 | tests pass | fails in buildPhase | 21 | inline or top-level asm | `nanofil: /build/source/lib/x86/cpu_features.c:47: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| libedit | 20240808-3.1 | built | built | 115 |  |  |
| libepoxy | 1.5.10 | tests pass | tests pass | 71 |  |  |
| libev | 4.33 | built | built | 56 |  |  |
| libevdev | 1.11.0 | built | built | 60 |  |  |
| libevent | 2.1.13 | built | built | 254 |  |  |
| libffi | 3.8.0 | tests pass | fails in buildPhase | 64 | constant expressions not folded | `nanofil: ../src/types.c:126: initializer is not a constant` |
| libgbm | 26.0.3 | built | fails in buildPhase | 148 | other builtins | `nanofil: ../src/util/cache_ops_x86.c:68: undeclared identifier __builtin_ia32_mfence` |
| libgcrypt | 1.12.2 | tests pass | tests fail |  | other syntax or typing gaps | `PASS: prime` |
| libgit2 | 1.9.7 | tests pass | tests pass | 698 |  |  |
| libglvnd | 1.7.0 | built | built | 85 |  |  |
| libgpg-error | 1.59 | tests pass | tests pass | 162 |  |  |
| libgsf | 1.14.58 | tests pass | tests pass | 164 |  |  |
| libgudev | 238 | built | built | 16 |  |  |
| libhandy | 1.8.3 | tests pass | fails in buildPhase | 49 | alignment attributes | `nanofil: src/hdy-resources.c:9: alignment attributes is not supported` |
| libhighscore | 0-unstable-2026-04-01 | tests pass | fails in buildPhase | 105 | alignment attributes | `nanofil: tests/hs-test-resources.c:9: alignment attributes is not supported` |
| libical | 3.0.20 | built | built | 228 |  |  |
| libiconv | 1.19 | built | built | 266 |  |  |
| libidn2 | 2.3.8 | built | built | 228 |  |  |
| libinput | 1.29.1 | built | fails in buildPhase | 120 | other syntax or typing gaps | `nanofil: ../tools/libinput-record.c:1354: a cleanup attribute on a declaration of several declarators is not supported` |
| libjpeg_turbo | 3.1.4 | built | fails in buildPhase | 23 | other syntax or typing gaps | `nanofil: /nix/store/10xdyb6i0ahryz4a85xp747zwkh7g7xw-simde-0.8.2/include/simde/arm/neon/movl.h:54: expected an expression, at typeof` |
| liblc3 | 1.1.3 | built | built | 15 |  |  |
| libmbim | 1.34.0 | tests pass | fails in buildPhase | 64 | other syntax or typing gaps | `nanofil: ../src/libmbim-glib/mbim-message.c:2407: sizeof: packed pointers` |
| libmhash | 0.9.9.9 | tests pass | tests pass | 140 |  |  |
| libmicrohttpd | 1.0.2 | built | built | 278 |  |  |
| libmpdclient | 2.24 | tests pass | tests pass | 98 |  |  |
| libopus | 1.6.1 | tests pass | fails in buildPhase | 18 | alignment attributes | `nanofil: ../celt/float_cast.h:68: calls returning bad(alignment attributes) are not supported yet` |
| libpng | 1.6.43 | built | built | 71 |  |  |
| libpq | 18.6 | built | fails in buildPhase | 304 | alignment attributes | `nanofil: jsonapi.c:2218: alignment attributes is not supported` |
| libraqm | 0.10.5 | tests pass | tests pass | 14 |  |  |
| libressl | 4.2.1 | tests pass | fails in buildPhase | 61 | inline or top-level asm | `nanofil: /build/libressl-4.2.1/ssl/bio_ssl.c:106: top-level asm is not supported, at (` |
| libseccomp | 2.6.1 | tests pass | tests pass | 161 |  |  |
| libselinux | 3.10 | built | built | 151 |  |  |
| libsepol | 3.10 | built | built | 140 |  |  |
| libshout | 2.4.6 | built | built | 92 |  |  |
| libsodium | 1.0.22-unstable-2026-04-09 | tests pass | fails in buildPhase | 193 | inline or top-level asm | `nanofil: crypto_ipcrypt/ipcrypt_soft.c:287: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| libsoup_3 | 3.6.6 | built | built | 235 |  |  |
| libssh2 | 1.11.1 | built | built | 88 |  |  |
| libtasn1 | 4.21.0 | built | built | 224 |  |  |
| libtiff | 4.7.2 | tests pass | fails in buildPhase | 60 | alignment attributes | `nanofil: /build/source/libtiff/tif_predict.c:605: alignment attributes is not supported` |
| libtirpc | 1.3.7 | tests pass | tests pass | 131 |  |  |
| liburcu | 0.15.6 | tests pass | fails in buildPhase | 124 | other syntax or typing gaps | `nanofil: cds_hlist_for_each_entry_rcu.c:67: expected a parameter declaration, at {` |
| libuv | 1.52.1 | built | built | 94 |  |  |
| libvmaf | 3.0.0 | tests pass | tests pass | 129 |  |  |
| libvpx | 1.16.0 | built | built | 225 |  |  |
| libwebp | 1.6.0 | built | fails in buildPhase | 34 | alignment attributes | `nanofil: /build/source/sharpyuv/sharpyuv_sse2.c:85: alignment attributes is not supported` |
| libxcrypt | 4.5.2 | built | fails in buildPhase | 110 | inline or top-level asm | `nanofil: lib/crypt-gensalt-static.c:33: top-level asm is not supported, at (` |
| libxkbcommon | 1.13.1 | built | built | 393 |  |  |
| libxml2 | 2.15.4 | built | built | 82 |  |  |
| lighttpd | 1.4.85 | built | fails in buildPhase | 270 | inline or top-level asm | `nanofil: ./algo_xxhash.h:2987: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| lttng-ust | 2.14.0 | tests fail | not tried |  |  |  |
| lzo | 2.10 | built | built | 289 |  |  |
| mailutils | 3.21 | tests pass | tests pass | 1157 |  |  |
| mariadb-connector-c_3_3 | 3.3.5 | built | fails in buildPhase | 135 | inline or top-level asm | `nanofil: /build/source/libmariadb/ma_context.c:201: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| mbedtls | 3.6.6 | tests pass | fails in buildPhase | 19 | other syntax or typing gaps | `nanofil: /build/source/library/bignum_core.c:480: mode TI (__int128) is not supported` |
| minizip | 1.3.2 | built | built | 35 |  |  |
| mpdecimal | 4.0.1 | built | built | 44 |  |  |
| mpfr | 4.2.2 | tests pass | tests pass | 540 |  |  |
| mpg123 | 1.33.7 | dependency fails | not tried |  |  |  |
| netcdf | 4.9.3 | tests pass | tests fail | 691 | other syntax or typing gaps | `fail (129): NetCDF: Filter error: undefined filter encountered` |
| nettle | 3.10.2 | tests pass | fails in buildPhase | 440 | constant expressions not folded | `nanofil: ecc-secp224r1.c:212: initializer is not an address constant` |
| nghttp2 | 1.69.0 | built | built | 127 |  |  |
| nspr | 4.40 | tests pass | tests fail | 98 | unresolved Fil-C symbol at link | `../../dist/lib/libnspr4.so: error: undefined reference to 'pizlonated_fegetround'` |
| nss | 3.112.5 | tests pass | fails in buildPhase | 24 | inline or top-level asm | `nanofil: ../../lib/util/secport.c:870: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| oniguruma | 6.9.10 | built | built | 104 |  |  |
| openssh | 10.5p1 | built | fails in buildPhase | 661 | inline or top-level asm | `nanofil: sntrup761.c:62: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| openssl | 3.5.7 | built | fails in buildPhase | 141 | inline or top-level asm | `nanofil: crypto/bn/bn_asm.c:29: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| openssl-sarcasm | 3.6.4 | tests pass | fails in buildPhase | 132 | inline or top-level asm | `nanofil: crypto/bn/asm/../bn_asm.c:28: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| p11-kit | 0.26.2 | built | built | 289 |  |  |
| pam | 1.7.2 | built | built | 239 |  |  |
| pango | 1.56.3 | built | built | 163 |  |  |
| parted | 3.7 | tests pass | fails in buildPhase | 330 | constant expressions not folded | `nanofil: gpt.c:1944: static assertion is not a constant` |
| pcre2 | 10.48 | built | fails in buildPhase | 73 | inline or top-level asm | `nanofil: src/../deps/sljit/sljit_src/sljitNativeX86_common.c:462: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| perl5 | 5.40.0 | built | built | 745 |  |  |
| physfs | 3.2.0 | built | fails in buildPhase | 36 | inline or top-level asm | `nanofil: /build/source/src/physfs_lzmasdk.h:1495: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| pixman | 0.46.4 | built | built | 119 |  |  |
| polkit | 127 | tests pass | tests pass | 71 |  |  |
| potrace | 1.16 | tests pass | tests pass | 67 |  |  |
| procps | 4.0.6 | built | built | 187 |  |  |
| pth | 2.0.7 | tests pass | tests pass | 112 |  |  |
| pulseaudio | 17.0 | dependency fails | not tried |  |  |  |
| python312 | 3.12.5 | built | built | 858 |  |  |
| quickjs | 2026-06-04 | tests pass | fails in buildPhase | 12 | inline or top-level asm | `nanofil: quickjs.c:60630: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| rdkafka | 2.13.0 | built | fails in buildPhase | 40 | inline or top-level asm | `nanofil: /build/source/src/queue.h:688: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| recode | 3.7.15 | tests pass | tests pass | 293 |  |  |
| redis | 8.8.2 | tests pass | fails in buildPhase | 69 | other syntax or typing gaps | `nanofil: ./xxhash.h:908: attribute noescape is not supported` |
| rhash | 1.4.6 | tests pass | fails in buildPhase | 6 | inline or top-level asm | `nanofil: calc_sums.c:555: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| rpcbind | 1.2.6 | built | built | 31 |  |  |
| rsync | 3.5.0 | tests pass | fails in configurePhase | 69 | other syntax or typing gaps | `configure.sh: error: Aborting configure run` |
| ruby_3_3 | 3.3.10 | built | fails in buildPhase | 572 | other syntax or typing gaps | `nanofil: ./include/ruby/internal/anyargs.h:274: attribute weakref is not supported` |
| runit | 2.3.1 | tests pass | tests pass | 98 |  |  |
| scrypt | 1.3.3 | built | built | 106 |  |  |
| seatd | 0.9.3 | built | built | 62 |  |  |
| spandsp | 0.0.6 | built | built | 93 |  |  |
| sqlite | 3.51.2 | built | fails in buildPhase | 59 | other syntax or typing gaps | `nanofil: error(resource_error(stack),stack_overflow{choicepoints:337,depth:676,environments:341,globalused:798209,localused:127,non_terminating:[frame(671,apply:maplist_([423],(:)/2),[]),frame(669,apply:maplist_([425],(:)/2),[])],stack_limit:1048576,trailused:45054})` |
| strace | 7.2 | fails in buildPhase | not tried |  |  |  |
| svt-av1 | 3.1.2 | built | built | 148 |  |  |
| systemd | 256.4 | built | fails in buildPhase | 248 | other syntax or typing gaps | `nanofil: ../src/core/apparmor-setup.c:27: a cleanup attribute on a declaration of several declarators is not supported` |
| timidity | 2.15.0 | dependency fails | not tried |  |  |  |
| tinycc | 0.9.27-unstable-2025-01-06 | built | built | 13 |  |  |
| tor | 0.4.9.12 | built | fails in buildPhase | 510 | alignment attributes | `nanofil: src/core/crypto/relay_crypto_cgo.c:55: member kb of a type nanofil does not support (alignment attributes)` |
| torsocks | 2.5.0 | built | built | 116 |  |  |
| tpm2-abrmd | 3.0.0 | built | built | 94 |  |  |
| tpm2-tss | 4.2.0 | built | tests fail | 494 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: __builtin_choose_expr needs a constant condition` |
| trealla | unstable-2026-09-05 | built | fails in buildPhase | 43 | nanofil internal failure | `nanofil: failed` |
| ttyd | 1.7.7 | built | built | 9 |  |  |
| unbound | 1.26.0 | tests pass | tests pass | 734 |  |  |
| util-linux | 2.42.3 | built | fails in buildPhase | 361 | inline or top-level asm | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/sys/io.h:47: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| uwimap | 2007f | built | built | 38 |  |  |
| vala | 0.56.19 | built | built | 488 |  |  |
| wasm3 | 0.5.0 | built | built | 19 |  |  |
| wavpack | 5.9.0 | built | built | 87 |  |  |
| wayland | 1.25.0 | built | built | 73 |  |  |
| weston | 15.0.1 | built | built | 349 |  |  |
| x264 | 0-unstable-2025-01-03 | built | built | 35 |  |  |
| xvidcore | 1.3.7 | built | built | 71 |  |  |
| xz | 5.8.4 | built | fails in buildPhase | 137 | inline or top-level asm | `nanofil: common/common.c:395: top-level asm is not supported, at (` |
| zix | 0.6.2 | tests pass | fails in buildPhase | 15 | other syntax or typing gaps | `nanofil: ../include/zix/allocator.h:97: expected ;, at malloc` |
| zlib | 1.3.2 | tests pass | tests pass | 47 |  |  |
| zlib-ng | 2.2.4 | built | fails in buildPhase | 60 | inline or top-level asm | `nanofil: /build/zlib-ng-2.2.4/arch/x86/x86_features.c:64: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| zstd | 1.5.7 | built | fails in buildPhase | 22 | other syntax or typing gaps | `nanofil: /build/source/lib/common/xxhash.h:904: attribute noescape is not supported` |

<!-- end survey table -->
