# PHP extensions on Fil-C

`pkgsFilc.php` (PHP 8.4) builds with Nixpkgs' default extensions. The
extensions below are the commonly enabled ones beyond that set: PECL
extensions from `phpPackages.extensions` and bundled extensions Nixpkgs leaves
out. Their overrides are in the `php84` block of `ports/overlay.nix`;
library fixes are in `ports.nix`.

## How they are tested

`withTests` runs each extension's own test suite during the build, with the
default extensions and the extension's dependencies loaded, twice:

- on Zend's allocator, as PHP normally runs, and
- with `USE_ZEND_ALLOC=0`. Zend's allocator hands out request memory from
  2 MiB chunks, so Fil-C bounds a PHP value only by its chunk. On the system
  allocator every allocation has its own bounds, and overflows or use after
  free between values trap. Most of the real bugs below only showed up here.

Test failures were compared with the same harness on x86-64 PHP without
Fil-C; tests that fail there too are removed with `withoutTests`.

run-tests matches `--EXPECTF--` output with PCRE, and PCRE has no JIT under
Fil-C. Lines with many `%s` then exhaust the default
`pcre.backtrack_limit`, so tests that produced the right output failed.
The harness raises the limit, both for run-tests and for its parallel
workers, which run with no options and read it from `PHP_INI_SCAN_DIR`.
The tests themselves run with `-n` and do not see it.

Tests that only work on Zend's allocator are left out of the second run:
those the extension marks for ASan (`SKIP_ASAN`), memory_limit tests such
as luasandbox's `oom-init` (`zendAllocOnlyTests`), and Xdebug's debugger
tests. Some of those give the debugged PHP one second to connect; on a busy
builder it connected after the client had given up, and both then waited
forever. Other tests that wait fixed times missed them on busy builders
and are skipped: seven of phpredis' session locking tests, which race a
second PHP, and luasandbox's CPU timer test, which expects a wall-clock
busy loop to be all CPU time.

## Status

Passing their test suites on both allocators; counts are tests run on
Zend's allocator, the rest skip (most for want of a server or service):

| Extension | Tests | Notes |
| --- | --- | --- |
| mongodb | 1690 | No MongoDB server, so most tests skip. |
| xdebug | 777 | Xdebug's `run-xdebug-tests.php`, including DBGp debugger sessions; the debugger tests run on Zend's allocator only (see below). |
| snuffleupagus | 343 | |
| imagick | 320 | ImageMagick without librsvg, libheif and libjxl; DejaVu fonts for the text tests. |
| ds | 231 | |
| zend_test | 130 | |
| igbinary | 124 | |
| msgpack | 123 | |
| memcached | 114 | Against local memcached. |
| ffi | 93 | |
| ast | 90 | |
| xsl | 78 | |
| yaml | 76 | |
| memcache | 75 | Against local memcached. |
| opentelemetry | 75 | |
| apcu | 61 | |
| zstd | 57 | |
| tidy | 49 | |
| uv | 49 | |
| decimal | 48 | |
| spx | 45 | |
| gnupg | 37 | |
| dba | 36 | |
| imap | 31 | |
| amqp | 30 | No broker, so most tests skip. |
| wikidiff2 | 30 | |
| event | 29 | |
| mailparse | 28 | |
| rdkafka | 21 | No broker, so most tests skip. |
| luasandbox | 20 | |
| bz2 | 19 | |
| uuid | 14 | |
| excimer | 13 | |
| meminfo | 12 | |
| sysvshm | 10 | |
| pcov | 7 | |
| sysvmsg | 7 | |
| snmp | 4 | |
| grpc | 3 | |
| maxminddb | 3 | |
| shmop | 3 | |
| inotify, pinba, vld | 1 each | |
| redis | | phpredis' own `TestRedis.php` against local servers, Redis and RedisArray. |

Built and loading, but without tests that run here: phalcon, protobuf
and systemd ship no `.phpt` tests in their releases; pspell and ssh2 skip
all of theirs (no aspell dictionary, no SSH server).

## Bugs found and fixed

These are bugs natively too. There they read or wrote memory they did not
own, or reached undefined behaviour, without crashing; Fil-C stopped them.

- **msgpack**: unserializing an enum stored the case object without a
  reference, so it was freed while the class still owned it
  (`php-msgpack-enum-refcount.patch`). Invalid input such as
  `"\x82\xc0\x91\x01\xc0"` freed a map value twice
  (`php-msgpack-map-item-double-free.patch`).
- **opentelemetry**: WithSpan and SpanAttribute values were added to hook
  parameter tables without a reference and freed twice at shutdown
  (`php-opentelemetry-hook-args-refcount.patch`). Upstream has since
  rewritten this code with references.
- **xdebug** (`php-xdebug-out-of-bounds.patch`):
  - Internal function frames were read as user op arrays, past the end of
    the smaller struct, in the coverage filter check and the line
    breakpoint check. Upstream master has the same guards.
  - `/proc/self/mountinfo` filled an 8 KiB buffer with no room for its
    terminator.
  - DBGp `feature_set max_depth` allocated one runtime page too few.
- **snuffleupagus**: the configuration scanner indexed its tables with a
  signed `char`, so bytes from 0x80 up read before them
  (`php-snuffleupagus-scanner-unsigned.patch`).
- **meminfo**: dumping a frame with an unset compiled variable reached
  `ZEND_UNREACHABLE()` (`php-meminfo-undef.patch`).
- **libgd**: rotating a palette image read the palette original's null
  `tpixels`, and the 180-degree case freed the caller's image (upstream
  6cc1e39e and a656f5cc).

## Fil-C porting fixes

These are changes Fil-C needs, not bugs:

- Pointers round-tripped through integers, or offset from another object,
  lose their capability.
  - APCu: shared memory offsets (`php-apcu-filc.patch`).
  - PHP core: `zend_str_tolower_dup_ex()` and `zend_str_toupper_dup_ex()`
    addressed the new copy as `source + (copy - source)`. On the system
    allocator `strip_tags()` with allowed tags trapped
    (`php-8.4-filc.patch`).
  - OpenEXR: the chunk table kept in an `atomic_uintptr_t`
    (`openexr-chunk-table-pointer.patch`), and frame buffer bases offset
    through `intptr_t` (`openexr-frame-buffer-pointers.patch`).
- Pointers must be stored 8-byte aligned: libraqm's text info array after
  odd-length text (`libraqm-align-text-info.patch`).
- Fil-C's `shmdt` rejects addresses that are not mappings, where glibc
  returns EINVAL: shmop detached failed attachments
  (`php-8.4-shmop-filc.patch`).
- Inline assembly with memory operands, raw opcode bytes and some
  intrinsics are refused. Turned off or avoided:
  - OpenEXR's DWA AVX assembly, FPU control-register access, and the
    vendored OpenJPH SIMD (its AVX2 gathers are not lowered).
  - librdkafka's hardware CRC32C detection.
- Configure probes that run programs fail when cross-compiling: amqp's
  version, inotify, and pkg-config lookups for memcached, zstd and grpc.
- Fibers run on a stack Fil-C's runtime allocates, so `zend_test`'s custom
  fibers measured their stack from the wrong base.
- libraw's pkg-config files named libstdc++; Fil-C's C++ runtime is libc++.
- uw-imap's c-client used `vfork`, which Fil-C's libc does not provide.

Unrelated to Fil-C: libgd rejected the bicubic interpolation methods
(upstream 39abd723), and libmemcached's `memflush` did not compile with
Clang.

## Not ported

| Extension | Why |
| --- | --- |
| memprof | Uses Judy arrays. Judy keeps every node address in a `Word_t` (`JudyMalloc` returns one), so its pointers have no capability and the first recorded allocation traps in `JudyLIns`. It needs Judy retyped throughout; marked broken. |
| enchant | 17 of libenchant's own 352 unit tests fail under Fil-C, all about which providers the broker loads and in what order (describe and ordering tests with mock providers). Not root-caused, so the library does not build and the extension is untested. |
| swoole, openswoole | Need valgrind, which has no Fil-C build. |
| couchbase, parallel | Marked broken in Nixpkgs. parallel also needs ZTS PHP. |
| smbclient | Needs libbsd, which does not build. |
| rrd | rrdtool's configure needs GLib's GRegex or libpcre; not attempted. |
| pdlib | Needs dlib with LAPACK and gfortran. |
| ioncube-loader, relay, blackfire, datadog-trace, oci8, sqlsrv, tideways | Prebuilt binaries or proprietary client libraries. |

ImageMagick for imagick is built without three delegates:

- librsvg: Rust, which has no Fil-C target.
- libheif: its x265 encoder builds parts with GCC.
- libjxl: Highway detects SIMD targets with `xgetbv` spelled as raw opcode
  bytes and then dispatches to AVX2 and AVX-512 intrinsics.

## Remaining test differences

- **gd** (tests disabled in Nixpkgs): with the libgd patches, 8 of 272
  ext/gd tests still fail on either allocator, and none trap. Six are
  TrueType bounding boxes, which fail the same way natively. Two
  (bug65148, bug73272) are rotated image sizes one or two pixels off; on
  unpatched libgd they crash or fail on bicubic natively. The tests are
  written for the libgd bundled with PHP, which rounds differently from
  system libgd 2.3.3. Before the patches there were 11 failures and a trap.
- **Core PHP on the system allocator**: Zend, standard, SPL, date, PCRE,
  JSON, random, hash and reflection pass with the `strip_tags` fix, apart
  from two memory_limit tests. memory_limit is only enforced by Zend's
  allocator.
