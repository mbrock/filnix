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

The survey of 2026-10-28, at `eb1ff00`: of the 300 packages ports.nix
names, 209 are C. filcc builds 202 of them. Of those 202, nanofil alone
builds 96 (48%; 61 of 201 at `06e5f69`). The 29 among them whose ports run
tests pass them, as filcc's builds do. Two build but fail their tests:
mbedtls traps on inline asm with a pointer argument where filcc's build
passes, and nspr's tests fail to link (`fegetround`). The other 104 fail:
102 while building and 2 in configure. The 96 built ones compiled 19,789
objects with nanofil.

The packages built are a2ps, bash, busybox, cairo, capstone, cmocka,
coreutils, cups, dash, db53, dbus, dbus-glib, diffutils, duktape,
e2fsprogs, expat, file, freetype, gawk, gd, gnu-shepherd, gnugrep, gnum4,
gnumake, gnused, gnutar, graphene, gsl, gssdp_1_6, imlib2, jq, libarchive,
libcap, libcap_ng, libcbor, libdbusmenu, libedit, libepoxy, libev,
libevdev, libgit2, libglvnd, libgsf, libgudev, libical, libiconv, libidn2,
liblc3, libmhash, libmpdclient, libpng, libraqm, libselinux, libsepol,
libshout, libssh2, libtasn1, libtirpc, libuv, libvmaf, libxcrypt, libxml2,
lzo, minizip, mpdecimal, mpfr, nghttp2, oniguruma, p11-kit, pam, perl5,
pixman, polkit, potrace, pth, recode, rpcbind, rsync, runit, scrypt,
seatd, spandsp, sqlite, svt-av1, tinycc, torsocks, tpm2-abrmd, ttyd,
uwimap, vala, wasm3, wavpack, wayland, xvidcore and zlib (and
bashNonInteractive). x264 built at `06e5f69` and now fails
(`common/base.c:933: expected a statement, at {`).

Between `06e5f69` and `eb1ff00` nanofil gained refusal of incompatible
redeclarations, alignments up to 4096, the generic `__atomic` builtins,
`__builtin_types_compatible_p` and `__builtin_choose_expr`, GNU89 extern
inline, K&R definitions, folded integer casts of constant addresses, and
local call thunks for static callees (a miscompile potrace's tests
caught).

### Causes

Each failure counts once, under its first error. Removing that cause
gets a package to its next error, not necessarily to a build.

The largest row, "other syntax or typing gaps" (39), splits by hand:

- **`__transparent_union__` parameters** (12): GLib 2.80's
  `G_DEFINE_BOXED_TYPE` registers its copy and free functions through a
  prototype whose parameters are transparent unions, so every GLib
  consumer that defines a boxed type stops there (at-spi2-core,
  gdk-pixbuf, gobject-introspection, gtk4, gtksourceview3, gupnp,
  json-glib, libhighscore, libsoup, pango), as do bind and mailutils.
- **Statement expressions that don't type** (3): glib's own `gatomic.c`,
  gtk3 and dconf (`!` applied to one).
- **`sizeof` of an incomplete type** (3): git, mariadb-connector-c,
  tpm2-tss.
- **Attributes in expression or statement position** (3): libevent,
  unbound, util-linux.
- **Imaginary literals** (2): finit (`1i`), imagemagick (`1.0iF`).
- The rest are one package each.

Inline and top-level asm (22) is the next row.

<!-- survey table -->

| Set aside | Packages |
| --- | ---: |
| C++ | 59 |
| evaluation fails | 20 |
| no C sources found | 12 |

| filcc | nanofil | Packages |
| --- | --- | ---: |
| built | built | 67 |
| built | fails in buildPhase | 62 |
| tests pass | fails in buildPhase | 40 |
| tests pass | tests pass | 29 |
| dependency fails | not tried | 4 |
| fails in buildPhase | not tried | 2 |
| tests pass | fails in configurePhase | 2 |
| tests pass | tests fail | 2 |
| tests fail | not tried | 1 |

| Cause | Packages | Which |
| --- | ---: | --- |
| other syntax or typing gaps | 39 | at-spi2-core, bind, binutils-unwrapped, dconf, emacs30, finit, gdk-pixbuf, git, glib, gobject-introspection-unwrapped, gtk3, gtk4, gtksourceview3, gupnp_1_6, imagemagick, json-glib, kittydoom, krb5, kronosnet, libaom, libevent, libhighscore, libjpeg_turbo, libmbim, libseccomp, libsoup_3, libvpx, libxkbcommon, mailutils, mariadb-connector-c_3_3, pango, parted, python312, ruby_3_3, tpm2-tss, unbound, util-linux, x264, zix |
| inline or top-level asm | 22 | dav1d, ell, fftw, flac, fstrm, kbd, libapparmor, libblake3, libressl, libsodium, mbedtls, nss, openssh, openssl, openssl-sarcasm, pcre2, physfs, quickjs, rdkafka, rhash, xz, zlib-ng |
| alignment attributes | 9 | ghostscript, gtksourceview4, libcdio, libdeflate, libhandy, libopus, libtiff, libwebp, tor |
| other builtins | 9 | cogl, gnutls, isa-l, libgbm, libmicrohttpd, libpq, netcdf, redis, zstd |
| constant expressions not folded | 8 | curl, guile-avahi, guile_3_0, libffi, liburcu, lighttpd, nettle, weston |
| aliases beyond one prototyped function | 4 | alsa-lib, elfutils, fontconfig, gtk2 |
| constructor on a declaration | 4 | cryptsetup, gnupg, libgcrypt, libgpg-error |
| __builtin_types_compatible_p, __builtin_choose_expr | 3 | btrfs-progs, gettext, systemd |
| unresolved Fil-C symbol at link | 3 | bison, keyutils, nspr |
| GNU case ranges | 2 | libinput, procps |
| nanofil internal failure | 2 | cyrus_sasl, trealla |
| calls passing arguments to a () function | 1 | gmp |

| Package | Version | filcc | nanofil | nanofil objects | Cause | First error |
| --- | --- | --- | --- | ---: | --- | --- |
| a2ps | 4.15.7 | tests pass | tests pass | 319 |  |  |
| alsa-lib | 1.2.15.3 | built | fails in buildPhase | 66 | aliases beyond one prototyped function | `nanofil: control.c:2974: alias is supported only for one prototyped, non-variadic function` |
| at-spi2-core | 2.60.5 | built | fails in buildPhase | 110 | other syntax or typing gaps | `nanofil: ../atk/atkrange.c:84: cannot assign ptr(func(ptr(struct(181)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(181)),[ptr(char),union(270),union(271)],fixed))` |
| bash | 5.3p9 | built | built | 568 |  |  |
| bashNonInteractive | 5.3p9 | built | built | 573 |  |  |
| bind | 9.20.30 | tests pass | fails in buildPhase | 204 | other syntax or typing gaps | `nanofil: async.c:60: cannot assign ptr(struct(98)) to union(100)` |
| binutils-unwrapped | 2.43.1 | built | fails in buildPhase | 636 | other syntax or typing gaps | `nanofil: /build/binutils-2.43.1/libiberty/md5.c:115: no member named buffer` |
| bison | 3.8.2 | built | fails in buildPhase | 449 | unresolved Fil-C symbol at link | `src/bison-getargs.o:function pizlonatedFI12770_rpl_printf:(.text+0x436fd): error: undefined reference to 'pizlonated_rpl_printf'` |
| bluez | 5.86 | fails in buildPhase | not tried |  |  |  |
| btrfs-progs | 6.19.1 | tests pass | fails in buildPhase | 116 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: __builtin_choose_expr needs a constant condition` |
| busybox | 1.37.0 | built | built | 14 |  |  |
| cairo | 1.18.4 | built | built | 275 |  |  |
| capstone | 5.0.7 | tests pass | tests pass | 128 |  |  |
| cmocka | 2.0.1 | built | built | 82 |  |  |
| cogl | 1.22.8 | built | fails in buildPhase | 96 | other builtins | `nanofil: driver/gl/cogl-framebuffer-gl.c:418: undeclared identifier __builtin_ffsl` |
| coreutils | 9.11 | built | built | 1248 |  |  |
| cryptsetup | 2.8.6 | tests pass | fails in configurePhase | 51 | constructor on a declaration | `configure: error: You need the device-mapper library.` |
| cups | 2.4.19 | built | built | 244 |  |  |
| curl | 8.22.0 | built | fails in buildPhase | 240 | constant expressions not folded | `nanofil: curl_gssapi.c:66: initializer is not a constant` |
| cyrus_sasl | 2.1.28 | built | fails in buildPhase | 225 | nanofil internal failure | `nanofil: failed` |
| dash | 0.5.12 | built | built | 96 |  |  |
| dav1d | 1.5.3 | tests pass | fails in buildPhase | 41 | inline or top-level asm | `nanofil: ../src/recon_tmpl.c:150: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| db53 | 5.3.28 | tests pass | tests pass | 512 |  |  |
| dbus | 1.16.2 | tests pass | tests pass | 291 |  |  |
| dbus-glib | 0.114 | built | built | 68 |  |  |
| dconf | 0.49.0 | tests pass | fails in buildPhase | 25 | other syntax or typing gaps | `nanofil: ../engine/dconf-engine.c:403: cannot type un(not,stmtexpr(at(../engine/dconf-engine.c:403,block([decl(../engine/dconf-engine.c:403,[tname(gint)],[init(dcl(some(gaicae_oldval),base,none),id(ref_count))]),static_assert(../engine/dconf-engine.c:403,bin(eq,sizeof_expr(un(deref,un(addr,arrow(id(` |
| diffutils | 3.12 | built | built | 565 |  |  |
| duktape | 2.7.0 | built | built | 8 |  |  |
| e2fsprogs | 1.47.4 | built | built | 557 |  |  |
| elfutils | 0.194 | built | fails in buildPhase | 187 | aliases beyond one prototyped function | `nanofil: elf_getshdrnum.c:87: alias is supported only for one prototyped, non-variadic function` |
| ell | 0.83 | built | fails in buildPhase | 48 | inline or top-level asm | `nanofil: ell/util.c:794: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| emacs30 | 30.1 | built | fails in buildPhase | 440 | other syntax or typing gaps | `nanofil: ./dynlib.h:33: expected a declaration, at typedef` |
| expat | 2.7.1 | tests pass | tests pass | 89 |  |  |
| ffmpeg-headless | 8.1.2 | dependency fails | not tried |  |  |  |
| fftw | 3.3.11 | tests pass | fails in buildPhase | 183 | inline or top-level asm | `nanofil: ./cycle.h:226: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| file | 5.47 | built | built | 141 |  |  |
| finit | 4.17 | built | fails in buildPhase | 56 | other syntax or typing gaps | `nanofil: getty.c:407: bad number 1i` |
| flac | 1.5.0 | tests pass | fails in buildPhase | 36 | inline or top-level asm | `nanofil: /build/flac-1.5.0/src/libFLAC/cpu.c:80: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| fontconfig | 2.17.1 | built | fails in buildPhase | 112 | aliases beyond one prototyped function | `nanofil: ./fcaliastail.h:268: alias is supported only for one prototyped, non-variadic function` |
| freetype | 2.14.3 | tests pass | tests pass | 138 |  |  |
| fstrm | 0.6.1 | tests pass | fails in buildPhase | 60 | inline or top-level asm | `nanofil: libmy/my_queue_mb.c:132: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| gawk | 5.4.1 | built | built | 275 |  |  |
| gd | 2.3.3 | built | built | 112 |  |  |
| gdk-pixbuf | 2.44.7 | built | fails in buildPhase | 68 | other syntax or typing gaps | `nanofil: ../gdk-pixbuf/gdk-pixbuf-io.c:3626: cannot assign ptr(func(ptr(struct(185)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(185)),[ptr(char),union(951),union(952)],fixed))` |
| gettext | 1.0 | built | fails in buildPhase | 1600 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: __builtin_choose_expr needs a constant condition` |
| ghostscript | 10.07.1 | built | fails in buildPhase | 350 | alignment attributes | `nanofil: ./brotli/c/enc/matching_tag_mask.h:24: alignment attributes is not supported` |
| git | 2.46.0 | built | fails in buildPhase | 343 | other syntax or typing gaps | `nanofil: imap-send.c:1434: sizeof: incomplete` |
| glib | 2.80.4 | built | fails in buildPhase | 402 | other syntax or typing gaps | `nanofil: ../glib/gatomic.c:175: cannot type stmtexpr(at(../glib/gatomic.c:175,block([decl(../glib/gatomic.c:175,[tname(gint)],[init(dcl(some(gaicae_oldval),base,none),id(oldval))]),static_assert(../glib/gatomic.c:175,bin(eq,sizeof_expr(un(deref,id(atomic))),sizeof_type(type([tname(gint)],base))),[69` |
| gmp | 6.3.0 | tests pass | fails in configurePhase | 30 | calls passing arguments to a () function | `configure: error: could not find a working compiler, see config.log for details` |
| gnu-shepherd | 1.0.9 | built | built | 240 |  |  |
| gnugrep | 3.12 | built | built | 528 |  |  |
| gnum4 | 1.4.21 | built | built | 645 |  |  |
| gnumake | 4.4.1 | tests pass | tests pass | 153 |  |  |
| gnupg | 2.4.9 | tests pass | fails in buildPhase | 171 | constructor on a declaration | `nanofil: the ctor gpg_err_init is not defined in this translation unit` |
| gnused | 4.10 | built | built | 493 |  |  |
| gnutar | 1.35 | tests pass | tests pass | 593 |  |  |
| gnutls | 3.8.13 | built | fails in buildPhase | 673 | other builtins | `nanofil: key_share.c:256: undeclared identifier __builtin_return_address` |
| gobject-introspection-unwrapped | 1.80.1 | tests pass | fails in buildPhase | 142 | other syntax or typing gaps | `nanofil: ../tests/scanner/regress.c:2029: cannot assign ptr(func(ptr(struct(176)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(176)),[ptr(char),union(1142),union(1143)],fixed))` |
| graphene | 1.10.8 | tests pass | tests pass | 66 |  |  |
| gsl | 2.8 | tests pass | tests pass | 1060 |  |  |
| gssdp_1_6 | 1.6.6 | tests pass | tests pass | 32 |  |  |
| gtk2 | 2.24.33 | built | fails in buildPhase | 98 | aliases beyond one prototyped function | `nanofil: ../../gdk/gdkaliasdef.c:1910: alias is supported only for one prototyped, non-variadic function` |
| gtk3 | 3.24.52 | built | fails in buildPhase | 104 | other syntax or typing gaps | `nanofil: ../gdk/wayland/gdkcursor-wayland.c:251: cannot type stmtexpr(at(../gdk/wayland/gdkcursor-wayland.c:251,block([decl(../gdk/wayland/gdkcursor-wayland.c:251,[tname(gint)],[init(dcl(some(gaicae_oldval),base,none),num(0,none-other))]),static_assert(../gdk/wayland/gdkcursor-wayland.c:251,bin(eq,s` |
| gtk4 | 4.14.5 | built | fails in buildPhase | 104 | other syntax or typing gaps | `nanofil: ../gtk/css/gtkcsssection.c:33: cannot assign ptr(func(ptr(struct(181)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(181)),[ptr(char),union(647),union(648)],fixed))` |
| gtksourceview3 | 3.24.11 | tests pass | fails in buildPhase | 110 | other syntax or typing gaps | `nanofil: gtksourceencoding.c:49: cannot assign ptr(func(ptr(struct(177)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(177)),[ptr(char),union(338),union(339)],fixed))` |
| gtksourceview4 | 4.8.4 | tests pass | fails in buildPhase | 69 | alignment attributes | `nanofil: gtksourceview/gtksourceview-gresources.c:9: alignment attributes is not supported` |
| guile-avahi | 0.4.1 | tests pass | fails in buildPhase | 43 | constant expressions not folded | `nanofil: src/errors.c:25: initializer is not a constant` |
| guile_3_0 | 3.0.11 | built | fails in buildPhase | 658 | constant expressions not folded | `nanofil: array-map.c:386: initializer is not a constant` |
| gupnp_1_6 | 1.6.10 | tests pass | fails in buildPhase | 40 | other syntax or typing gaps | `nanofil: ../libgupnp/gupnp-service-introspection.c:175: cannot assign ptr(func(ptr(struct(177)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(177)),[ptr(char),union(763),union(764)],fixed))` |
| imagemagick | 7.1.2-31 | built | fails in buildPhase | 336 | other syntax or typing gaps | `nanofil: MagickCore/fourier.c:1295: bad number 1.0iF` |
| imlib2 | 1.12.6 | built | built | 133 |  |  |
| isa-l | 2.32.0 | tests pass | fails in buildPhase | 51 | other builtins | `nanofil: /nix/store/asx904awk86a38cr62zyxqq1zf10603m-filc0-resource-dir/lib/clang/20/include/crc32intrin.h:73: undeclared identifier __builtin_ia32_crc32si` |
| jq | 1.8.2 | built | built | 152 |  |  |
| json-glib | 1.10.8 | tests pass | fails in buildPhase | 50 | other syntax or typing gaps | `nanofil: ../json-glib/json-array.c:51: cannot assign ptr(func(ptr(struct(176)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(176)),[ptr(char),union(407),union(408)],fixed))` |
| kbd | 2.9.0 | built | fails in buildPhase | 154 | inline or top-level asm | `nanofil: resizecons.c:400: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| keyutils | 1.6.3 | built | fails in buildPhase | 8 | unresolved Fil-C symbol at link | `./libkeyutils.so: error: undefined reference to 'pizlonated_zargs'` |
| kittydoom | git | built | fails in buildPhase | 1 | other syntax or typing gaps | `nanofil: src/PureDOOM.h:16108: invalid operands to and: int and double` |
| krb5 | 1.22.2 | built | fails in buildPhase | 263 | other syntax or typing gaps | `nanofil: ../../include/k5-platform.h:698: no member named i` |
| kronosnet | 1.33 | built | fails in buildPhase | 95 | other syntax or typing gaps | `nanofil: /nix/store/l9vcwpxmi9a255r27cgn9gwf8j0d356g-filc-glibc-2.44/include/bits/link.h:99: expected a member declaration, at __int128_t` |
| libaom | 3.12.1 | built | fails in buildPhase | 172 | other syntax or typing gaps | `nanofil: error(resource_error(stack),stack_overflow{choicepoints:12,depth:26885,environments:22,globalused:1045671,localused:5,stack:[frame(26885,ir:evidence_names(chk10658,live/6),[]),frame(26884,apply:exclude_([745],(:)/2,_164),[]),frame(21246,ir:checked_inst_rest(let/4,[83151],prepare_tf_workers,` |
| libapparmor | 4.1.7 | built | fails in buildPhase | 47 | inline or top-level asm | `nanofil: kernel.c:832: top-level asm is not supported, at (` |
| libarchive | 3.7.4 | built | built | 425 |  |  |
| libblake3 | 1.8.5 | built | fails in buildPhase | 4 | inline or top-level asm | `nanofil: /build/source/c/blake3_dispatch.c:70: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| libcap | 2.70 | built | built | 16 |  |  |
| libcap_ng | 0.9.3 | tests pass | tests pass | 67 |  |  |
| libcbor | 0.13.0 | tests pass | tests pass | 134 |  |  |
| libcdio | 2.3.0 | tests pass | fails in buildPhase | 142 | alignment attributes | `nanofil: image/nrg.c:195: buf has a type nanofil does not support (alignment attributes)` |
| libdbusmenu | 16.04.0 | built | built | 55 |  |  |
| libdeflate | 1.25 | tests pass | fails in buildPhase | 30 | alignment attributes | `nanofil: /build/source/lib/x86/crc32_pclmul_template.h:194: alignment attributes is not supported` |
| libedit | 20240808-3.1 | built | built | 115 |  |  |
| libepoxy | 1.5.10 | tests pass | tests pass | 71 |  |  |
| libev | 4.33 | built | built | 56 |  |  |
| libevdev | 1.11.0 | built | built | 60 |  |  |
| libevent | 2.1.13 | built | fails in buildPhase | 192 | other syntax or typing gaps | `nanofil: bufferevent_filter.c:619: expected an expression, at attribute` |
| libffi | 3.8.0 | tests pass | fails in buildPhase | 62 | constant expressions not folded | `nanofil: ../src/types.c:126: initializer is not a constant` |
| libgbm | 26.0.3 | built | fails in buildPhase | 150 | other builtins | `nanofil: ../src/util/cache_ops_x86_clflushopt.c:44: undeclared identifier __builtin_ia32_clflushopt` |
| libgcrypt | 1.12.2 | tests pass | fails in buildPhase | 105 | constructor on a declaration | `nanofil: the ctor gpg_err_init is not defined in this translation unit` |
| libgit2 | 1.9.7 | tests pass | tests pass | 698 |  |  |
| libglvnd | 1.7.0 | built | built | 85 |  |  |
| libgpg-error | 1.59 | tests pass | fails in buildPhase | 120 | constructor on a declaration | `nanofil: the ctor gpg_err_init is not defined in this translation unit` |
| libgsf | 1.14.58 | tests pass | tests pass | 164 |  |  |
| libgudev | 238 | built | built | 16 |  |  |
| libhandy | 1.8.3 | tests pass | fails in buildPhase | 65 | alignment attributes | `nanofil: src/hdy-resources.c:9: alignment attributes is not supported` |
| libhighscore | 0-unstable-2026-04-01 | tests pass | fails in buildPhase | 99 | other syntax or typing gaps | `nanofil: ../src/hs-border.c:22: cannot assign ptr(func(ptr(struct(177)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(177)),[ptr(char),union(271),union(272)],fixed))` |
| libical | 3.0.20 | built | built | 228 |  |  |
| libiconv | 1.19 | built | built | 266 |  |  |
| libidn2 | 2.3.8 | built | built | 228 |  |  |
| libinput | 1.29.1 | built | fails in buildPhase | 40 | GNU case ranges | `nanofil: ../src/evdev-frame.h:336: GNU case ranges are not supported, at EVDEV_BTN_DIGI` |
| libjpeg_turbo | 3.1.4 | built | fails in buildPhase | 22 | other syntax or typing gaps | `nanofil: /nix/store/10xdyb6i0ahryz4a85xp747zwkh7g7xw-simde-0.8.2/include/simde/arm/neon/movl.h:54: expected an expression, at typeof` |
| liblc3 | 1.1.3 | built | built | 15 |  |  |
| libmbim | 1.34.0 | tests pass | fails in buildPhase | 51 | other syntax or typing gaps | `nanofil: ../src/libmbim-glib/mbim-device.c:2447: pointer arithmetic on struct(627) (packed pointers)` |
| libmhash | 0.9.9.9 | tests pass | tests pass | 140 |  |  |
| libmicrohttpd | 1.0.2 | built | fails in buildPhase | 232 | other builtins | `nanofil: md5.c:155: undeclared identifier __builtin_rotateleft32` |
| libmpdclient | 2.24 | tests pass | tests pass | 98 |  |  |
| libopus | 1.6.1 | tests pass | fails in buildPhase | 17 | alignment attributes | `nanofil: ../celt/float_cast.h:68: calls returning bad(alignment attributes) are not supported yet` |
| libpng | 1.6.43 | built | built | 71 |  |  |
| libpq | 18.6 | built | fails in buildPhase | 233 | other builtins | `nanofil: snprintf.c:1365: undeclared identifier __builtin_isinf` |
| libraqm | 0.10.5 | tests pass | tests pass | 14 |  |  |
| libressl | 4.2.1 | tests pass | fails in buildPhase | 46 | inline or top-level asm | `nanofil: /build/libressl-4.2.1/crypto/crypto_err.c:102: top-level asm is not supported, at (` |
| libseccomp | 2.6.1 | tests pass | fails in buildPhase | 40 | other syntax or typing gaps | `nanofil: arch.c:267: bad offsetof` |
| libselinux | 3.10 | built | built | 151 |  |  |
| libsepol | 3.10 | built | built | 140 |  |  |
| libshout | 2.4.6 | built | built | 92 |  |  |
| libsodium | 1.0.22-unstable-2026-04-09 | tests pass | fails in buildPhase | 194 | inline or top-level asm | `nanofil: crypto_ipcrypt/ipcrypt_soft.c:287: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| libsoup_3 | 3.6.6 | built | fails in buildPhase | 53 | other syntax or typing gaps | `nanofil: ../libsoup/cookies/soup-cookie.c:62: cannot assign ptr(func(ptr(struct(176)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(176)),[ptr(char),union(734),union(735)],fixed))` |
| libssh2 | 1.11.1 | built | built | 88 |  |  |
| libtasn1 | 4.21.0 | built | built | 224 |  |  |
| libtiff | 4.7.2 | tests pass | fails in buildPhase | 60 | alignment attributes | `nanofil: /build/source/libtiff/tif_predict.c:605: alignment attributes is not supported` |
| libtirpc | 1.3.7 | tests pass | tests pass | 131 |  |  |
| liburcu | 0.15.6 | tests pass | fails in buildPhase | 91 | constant expressions not folded | `nanofil: ../include/urcu/static/wfqueue.h:119: static assertion is not a constant` |
| libuv | 1.52.1 | built | built | 94 |  |  |
| libvmaf | 3.0.0 | tests pass | tests pass | 129 |  |  |
| libvpx | 1.16.0 | built | fails in buildPhase |  | other syntax or typing gaps | `[CXX] vp8/vp8_ratectrl_rtc.cc.o` |
| libwebp | 1.6.0 | built | fails in buildPhase | 34 | alignment attributes | `nanofil: /build/source/sharpyuv/sharpyuv_sse2.c:85: alignment attributes is not supported` |
| libxcrypt | 4.5.2 | built | built | 130 |  |  |
| libxkbcommon | 1.13.1 | built | fails in buildPhase | 68 | other syntax or typing gaps | `nanofil: ../src/xkbcomp/keycodes.c:306: no member found` |
| libxml2 | 2.15.4 | built | built | 81 |  |  |
| lighttpd | 1.4.85 | built | fails in buildPhase | 209 | constant expressions not folded | `nanofil: server.c:2261: initializer is not a constant` |
| lttng-ust | 2.14.0 | tests fail | not tried |  |  |  |
| lzo | 2.10 | built | built | 289 |  |  |
| mailutils | 3.21 | tests pass | fails in buildPhase | 900 | other syntax or typing gaps | `nanofil: prog.c:32: cannot convert ptr(func(void,[ptr(struct(220))],fixed)) to union(230)` |
| mariadb-connector-c_3_3 | 3.3.5 | built | fails in buildPhase | 131 | other syntax or typing gaps | `nanofil: /build/source/plugins/io/remote_io.c:296: sizeof: incomplete` |
| mbedtls | 3.6.6 | tests pass | tests fail | 483 | inline or top-level asm | `AES-128-CBC Encrypt NIST KAT #1 ................................... filc safety error: cannot handle inline asm (inline assembly with pointer argument is not supported):` |
| minizip | 1.3.2 | built | built | 35 |  |  |
| mpdecimal | 4.0.1 | built | built | 44 |  |  |
| mpfr | 4.2.2 | tests pass | tests pass | 540 |  |  |
| mpg123 | 1.33.7 | dependency fails | not tried |  |  |  |
| netcdf | 4.9.3 | tests pass | fails in buildPhase | 332 | other builtins | `nanofil: dcetab.c:1049: undeclared identifier __builtin_memcpy` |
| nettle | 3.10.2 | tests pass | fails in buildPhase | 444 | constant expressions not folded | `nanofil: ecc-secp224r1.c:212: initializer is not an address constant` |
| nghttp2 | 1.69.0 | built | built | 127 |  |  |
| nspr | 4.40 | tests pass | tests fail | 98 | unresolved Fil-C symbol at link | `../../dist/lib/libnspr4.so: error: undefined reference to 'pizlonated_fegetround'` |
| nss | 3.112.5 | tests pass | fails in buildPhase | 36 | inline or top-level asm | `nanofil: ../../lib/util/secport.c:870: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| oniguruma | 6.9.10 | built | built | 104 |  |  |
| openssh | 10.5p1 | built | fails in buildPhase | 661 | inline or top-level asm | `nanofil: sntrup761.c:62: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| openssl | 3.5.7 | built | fails in buildPhase | 144 | inline or top-level asm | `nanofil: crypto/bn/bn_asm.c:29: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| openssl-sarcasm | 3.6.4 | tests pass | fails in buildPhase | 132 | inline or top-level asm | `nanofil: crypto/bn/asm/../bn_asm.c:28: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| p11-kit | 0.26.2 | built | built | 289 |  |  |
| pam | 1.7.2 | built | built | 239 |  |  |
| pango | 1.56.3 | built | fails in buildPhase | 59 | other syntax or typing gaps | `nanofil: ../pango/fonts.c:57: cannot assign ptr(func(ptr(struct(183)),[ptr(char),ptr(func(ptr(void),[ptr(void)],fixed)),ptr(func(void,[ptr(void)],fixed))],fixed)) to ptr(func(ptr(struct(183)),[ptr(char),union(994),union(995)],fixed))` |
| parted | 3.7 | tests pass | fails in buildPhase | 325 | other syntax or typing gaps | `nanofil: pc98.c:784: expected }, at :` |
| pcre2 | 10.48 | built | fails in buildPhase | 73 | inline or top-level asm | `nanofil: src/../deps/sljit/sljit_src/sljitNativeX86_common.c:462: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| perl5 | 5.40.0 | built | built | 745 |  |  |
| physfs | 3.2.0 | built | fails in buildPhase | 37 | inline or top-level asm | `nanofil: /build/source/src/physfs_lzmasdk.h:1495: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| pixman | 0.46.4 | built | built | 119 |  |  |
| polkit | 127 | tests pass | tests pass | 71 |  |  |
| potrace | 1.16 | tests pass | tests pass | 67 |  |  |
| procps | 4.0.6 | built | fails in buildPhase | 144 | GNU case ranges | `nanofil: src/ps/parser.c:550: GNU case ranges are not supported, at chr(57)` |
| pth | 2.0.7 | tests pass | tests pass | 112 |  |  |
| pulseaudio | 17.0 | dependency fails | not tried |  |  |  |
| python312 | 3.12.5 | built | fails in buildPhase | 753 | other syntax or typing gaps | `nanofil: ./Modules/readline.c:448: expected an expression, at )` |
| quickjs | 2026-06-04 | tests pass | fails in buildPhase | 12 | inline or top-level asm | `nanofil: quickjs.c:60630: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| rdkafka | 2.13.0 | built | fails in buildPhase | 23 | inline or top-level asm | `nanofil: /build/source/src/queue.h:688: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| recode | 3.7.15 | tests pass | tests pass | 293 |  |  |
| redis | 8.8.2 | tests pass | fails in buildPhase | 97 | other builtins | `nanofil: ./xxhash.h:3100: undeclared identifier __builtin_rotateleft32` |
| rhash | 1.4.6 | tests pass | fails in buildPhase | 6 | inline or top-level asm | `nanofil: calc_sums.c:555: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| rpcbind | 1.2.6 | built | built | 31 |  |  |
| rsync | 3.5.0 | tests pass | tests pass | 378 |  |  |
| ruby_3_3 | 3.3.10 | built | fails in buildPhase | 572 | other syntax or typing gaps | `nanofil: ./include/ruby/assert.h:132: expected a declaration, at __declspec` |
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
| tor | 0.4.9.12 | built | fails in buildPhase | 498 | alignment attributes | `nanofil: src/core/crypto/relay_crypto_cgo.c:55: member kb of a type nanofil does not support (alignment attributes)` |
| torsocks | 2.5.0 | built | built | 116 |  |  |
| tpm2-abrmd | 3.0.0 | built | built | 94 |  |  |
| tpm2-tss | 4.2.0 | built | fails in buildPhase | 92 | other syntax or typing gaps | `nanofil: src/tss2-fapi/ifapi_curl.c:433: sizeof: incomplete` |
| trealla | unstable-2026-09-05 | built | fails in buildPhase | 41 | nanofil internal failure | `nanofil: failed` |
| ttyd | 1.7.7 | built | built | 9 |  |  |
| unbound | 1.26.0 | tests pass | fails in buildPhase | 335 | other syntax or typing gaps | `nanofil: services/rpz.c:247: expected an expression, at attribute` |
| util-linux | 2.42.3 | built | fails in buildPhase | 338 | other syntax or typing gaps | `nanofil: lib/pty-session.c:589: expected an expression, at attribute` |
| uwimap | 2007f | built | built | 38 |  |  |
| vala | 0.56.19 | built | built | 488 |  |  |
| wasm3 | 0.5.0 | built | built | 19 |  |  |
| wavpack | 5.9.0 | built | built | 87 |  |  |
| wayland | 1.25.0 | built | built | 73 |  |  |
| weston | 15.0.1 | built | fails in buildPhase | 140 | constant expressions not folded | `nanofil: ../libweston/renderer-gl/gl-renderer.c:1947: initializer is not a constant` |
| x264 | 0-unstable-2025-01-03 | built | fails in buildPhase | 44 | other syntax or typing gaps | `nanofil: common/base.c:933: expected a statement, at {` |
| xvidcore | 1.3.7 | built | built | 71 |  |  |
| xz | 5.8.4 | built | fails in buildPhase | 133 | inline or top-level asm | `nanofil: common/common.c:395: top-level asm is not supported, at (` |
| zix | 0.6.2 | tests pass | fails in buildPhase | 14 | other syntax or typing gaps | `nanofil: ../include/zix/allocator.h:36: expected a parameter declaration, at *` |
| zlib | 1.3.2 | tests pass | tests pass | 47 |  |  |
| zlib-ng | 2.2.4 | built | fails in buildPhase | 60 | inline or top-level asm | `nanofil: /build/zlib-ng-2.2.4/arch/x86/x86_features.c:64: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| zstd | 1.5.7 | built | fails in buildPhase | 20 | other builtins | `nanofil: /build/source/lib/common/xxhash.h:3187: undeclared identifier __builtin_rotateleft32` |

<!-- end survey table -->
