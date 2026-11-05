# PHP on Fil-C

PHP 8.5, its native extensions and their C/C++ libraries, compiled with
[Fil-C](https://github.com/pizlonator/fil-c). Your PHP application does not
need a rewrite. A memory error in the interpreter, an extension or a
library stops the worker instead of corrupting memory. This is the existing
PHP implementation with targeted porting changes, not a new PHP runtime.

**The default is PHP 8.5.12.** `pkgsFilc.php`, `php-dist` and `php-docker`
use it; explicit 8.4 and 7.4 packages remain available. For an experimental
JIT evaluation, start with the **LLVM backend on staging**, not the older
C-emitting backend.

## Try it

```sh
nix build .#pkgsFilc.php     # PHP 8.5, Nixpkgs' default extensions
nix build .#php-dist        # php-8.5.12-filc-x86_64-linux.tar.xz
nix build .#php-docker      # OCI image, tagged filnix-php:8.5.12
```

Configure a [binary cache](binary-caches.md) first. The tarball runs on
x86-64 Linux without Nix: unpack it anywhere and use its `bin/php` or
`bin/php-fpm`. It carries its own runtime and libraries. See the
[bundled README](../packages/php-dist/README.md) for configuration.
Images and tarballs from a previous release do not change when the Nix
default changes; check the [release assets](https://github.com/mbrock/filnix/releases)
for the published version, or build the outputs above.

```sh
nix build .#php-docker && docker load < result
docker run --rm -p 9000:9000 -v "$PWD:/var/www/html" \
  filnix-php:8.5.12 php-fpm
```

Port 9000 is **FastCGI, not HTTP**: put nginx or Caddy in front, as with
`php:fpm`. For a development server, use `php -S` with `docker run --init`.
The [NixOS module](nixos.md) can switch existing FPM pools and supported web
applications to Fil-C with `filc.phpfpm.enable = true`.

`withExtensions` and `buildEnv` work as in Nixpkgs. The distribution adds
APCu, Redis, Memcached, MongoDB, Imagick and other commonly used extensions
to the defaults. Extensions and their libraries must also be Fil-C builds;
binary PECL downloads cannot be loaded. See the
[extension list](php-extensions.md). PHP 8.5 does not include the pinned
igbinary, memcache or Phalcon versions: they do not build against PHP 8.5
natively either.

## The JIT on real applications

**A small internal wiki or blog is a plausible evaluation target, not a
proven production capacity claim.** WordPress, MediaWiki and DokuWiki work
with the interpreter and the checked LLVM JIT. What matters is warmed
response latency, available CPU and memory, and whether you can keep cold
workers out of traffic—not the speedup on a numeric loop.

The [HTTP service benchmark](../bench/php/README.md#http-service-latency-and-throughput)
measures nginx → PHP-FPM → SQLite and reads each complete response over
loopback. It separates an ordinary article view from a mixed request load,
and separates cold warm-up from warmed measurements. No nginx full-page
cache bypasses PHP. These are server response times, not browser page loads:
network latency, TLS and fetching images/stylesheets are additional work.

### Measured HTTP responses

Three-round medians on Chapel, November 5, 2026: Core i7-10700K, two FPM
workers, 120 requests per load per round. Article latency uses one client;
mixed throughput and p95 use four concurrent clients.

| Site / runtime | Article p50 / p95 | Mixed req/s | Mixed p95 |
| --- | ---: | ---: | ---: |
| MediaWiki — native | 57 / 80 ms | 47.4 | 116 ms |
| MediaWiki — Fil-C interpreter | 184 / 197 ms | 11.1 | 472 ms |
| MediaWiki — Fil-C LLVM JIT | 209 / 229 ms | 8.4 | 643 ms |
| WordPress — native | 46 / 48 ms | 47.1 | 111 ms |
| WordPress — Fil-C interpreter | 277 / 286 ms | 7.2 | 762 ms |
| WordPress — Fil-C LLVM JIT | 265 / 274 ms | 7.1 | 790 ms |

These are PHP 8.5.12 builds from [the measured snapshot](https://github.com/mbrock/filnix/commit/37e529c96b9d0bc305170e667bd048cd95a078e9),
with both Fil-C variants on staging and the tracked system allocator.
They are **not measurements of the released-toolchain default**. Initial
warm-up is excluded; occasional later trace compilation remains included
in measured loads. The shared LLVM object cache is off. See the
[measurement notes](php-port-notes.md#http-service-measurements) for settings
and round-to-round spread.

For these small fixtures, a warmed article is a few hundred milliseconds,
not one or two seconds. But the two-worker pool has modest throughput,
and concurrent requests queue. This makes an internal site worth trying;
it does not establish capacity for a medium-traffic WordPress or small VM.
The LLVM JIT did not consistently improve CMS performance. Keep the
interpreter as a baseline rather than assuming the JIT is necessary.

The earlier “1.3 seconds for MediaWiki” was the **sum of medians for twelve
different requests**, not one page. Those comparisons and the 4.7× LLVM
speedup on CPU-bound `Zend/bench.php` belong in the
[detailed measurement record](php-port-notes.md#the-jit-on-real-applications),
not a server capacity estimate.

### Budget for warm-up and memory

In the Chapel run, interpreter workers held roughly **0.5–0.6 GiB RSS**,
versus about **1 GiB or more with LLVM tracing**. These are worker RSS
figures, not a whole container's memory limit; shared pages mean they
cannot simply be summed to obtain unique pool memory.

The two-worker pools took roughly **8–10 minutes** to complete their first
mixed pass with LLVM, versus about **4 seconds** interpreted. This is a
pool warm-up measurement, not the time for one page. The requests that
trigger compilation wait, and restarting or recycling workers brings the
cost back. Warm every worker before admitting traffic, keep spare capacity,
and test worker replacement as well as steady state. Compilation stops
PHP's execution timer, but not a reverse proxy's timeout.

There is an opt-in shared LLVM object cache, but it is **off by default**
and has a [documented security caveat](upstream-updates.md#llvm-jit).
Do not enable `PHP_JIT_LLVM_CACHE_SIZE` merely to reproduce a faster start.
It reduces duplicate compilation, not the measured steady-state cost.

For deployment sizing, replay your own traffic and check p95 latency at
your expected concurrency. The supplied fixtures are small, SQLite-backed
sites, not a large MediaWiki installation or a plugin-heavy WordPress with
remote MySQL. Full-page caches can greatly reduce PHP traffic but change
what is being measured. A benchmark at saturation is a capacity sample,
not a safe operating target or a promise about a VM.

## LLVM JIT: the experimental path forward

```sh
nix build .#php85-jit
result/bin/php -d opcache.enable_cli=1 -d opcache.jit=tracing \
  -d opcache.jit_buffer_size=64M script.php
```

`php85-jit` uses `pkgsFilcStaging.php85-jit`, built against **unreleased
upstream Fil-C work plus our additions**, pinned in `lib/filc-staging.json`.
It is separate from the released-toolchain PHP 8.5 default. LLVM JIT
support must stay on staging until a Fil-C release includes the needed API;
changing PHP's default version does not promote that toolchain.
The `php85-staging-dist` tarball and `php85-staging-docker` image are also
interpreter builds; they do not include this opt-in JIT package.

OPcache still finds hot code and builds its intermediate representation.
The new backend turns it into LLVM IR and calls Fil-C's in-process compiler.
KillUB and FilPizlonator check the generated code just as they check compiled
C; no external compiler process runs. Side traces can link to each other.
This preserves the memory-safety boundary, not PHP semantic correctness:
a JIT bug can still give a wrong result or crash a worker. Application body
comparisons caught bugs that HTTP status checks and the JIT test suite missed.

Use `opcache.jit=tracing` for services. `function` compiles every function
of a loaded file; `1235` compiles hot whole functions and took 13 minutes
on MediaWiki in the earlier experiments. A one-shot script often loses to
compilation overhead. Keep the interpreter as a baseline: LLVM is the JIT
to evaluate, but it is not automatically faster for every service.

### Early experiment: the C-emitting backend

The first backend printed C, ran Fil-C clang and loaded the result. That
established that OPcache could generate checked code without rewriting PHP,
but external compilation is expensive and its side traces do not link.
It is superseded as the starting point for new evaluations by the LLVM
backend, not removed. `PHP_JIT_BACKEND=c` selects it on the 8.5 JIT build;
the historical `php-jit` output still names the 8.4 experiment. Its persistent
disk cache and implementation details are in the
[port notes](php-port-notes.md#opcache-jit-through-c).

## Security and operational differences

- **One allocation per PHP value.** The default tracked system allocator
  lets Fil-C detect overflows between values and use after free within a
  request. Zend's chunk allocator hides those boundaries. Keep the default:
  `USE_ZEND_ALLOC=1` weakens this protection; `USE_TRACKED_ALLOC=0` gives up
  `memory_limit`. Memory accounting works with the tracked allocator.
- **OPcache is per-worker.** Workers inherit what the master populated
  before forking but otherwise cache privately. `opcache_reset()` only
  resets the worker receiving it. Plan deployment and cache invalidation
  accordingly. Native OPcache/PCRE machine-code JITs are disabled.
- **A trap is still a crash.** FPM can replace a killed worker, but an
  attacker may cause denial of service. Fil-C does not fix SQL injection,
  authentication bugs, PHP object-injection gadgets or malicious PHP code.
  This is not a sandbox and does not replace upgrading PHP.

There is direct exploit evidence, not just synthetic bounds tests: the
adapted StealMyBitcoin chain succeeds against native vulnerable PHP 8.4.25
and stops at a Fil-C capability trap before the first heap leak against the
same vulnerable PHP on Fil-C. That does not establish protection against
every exploit route. See the [reproduction and limits](php-port-notes.md#the-stealmybitcoin-exploit-against-8425).

## Which PHP?

| Build | Nix output | Purpose |
| --- | --- | --- |
| **8.5.12, released toolchain** | `pkgsFilc.php` / `pkgsFilc.php85`, `php-dist`, `php-docker` | Default; interpreter and OPcache, no PHP JIT |
| **8.5.12, staging LLVM JIT** | `php85-jit` | Experimental checked tracing JIT; evaluate separately |
| 8.4.27 | `pkgsFilc.php84` | Explicit compatibility option |
| 7.4.33 | `pkgsFilc.php74`, `php74-dist` | End-of-life migration aid, not a supported PHP |
| 8.4.25 | `php84_25`, `php84_25-dist`, `php84_25-docker` | Deliberately vulnerable exploit reproduction only |

## Further evidence

- [Port notes](php-port-notes.md): allocator and VM changes, LLVM and C JIT
  internals, detailed benchmarks, exploit evidence and version-specific tests.
- [Extensions](php-extensions.md): supported modules and how they are tested.
- [Benchmark harness](../bench/php/README.md): fixtures and reproducible commands.
- [Staging toolchain](upstream-updates.md#llvm-jit): upstream basis, our additions
  and the shared-cache security caveat.
