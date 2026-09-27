# QuickJS in place of Node.js

Node.js (V8) is out of scope for Fil-C. This note records which Nixpkgs
packages actually need Node on the Fil-C host, where QuickJS can stand in, and
what was prototyped on the `orb/quickjs` branch.

## Summary

- The first thing to fix was QuickJS itself: every greedy regexp (`/a+/`,
  `/.*/`) trapped under Fil-C. Fixed in
  `patches/quickjs-regexp-greedy-cptr.patch`; `tests/quickjs-regexp.js` now
  runs as the port's check.
- Most packages that use Node only as a build tool already get the native
  Node (`buildPackages`), which is fine. Some are dragged to the Fil-C Node
  anyway by broken splicing: `fetchPnpmDeps` was the clearest case. Running
  the fetcher natively removes the Fil-C Node from 17 excluded packages.
- **yt-dlp** supports QuickJS upstream as its JavaScript runtime. The overlay
  now selects `quickjs` instead of Deno (V8). It works, except for an
  unrelated blocker (see the yt-dlp section).
- **qnode** (`packages/qnode/qnode.js`, about 500 lines) is a small Node
  compatibility layer on `qjs`. It runs **bibtex-tidy**, **aasvg** and
  **uglify-js** with output identical to Node. bibtex-tidy and aasvg are
  packaged on it (`tests/qnode.nix` compares them with Node).
- Recommendation: use QuickJS where upstream supports it (yt-dlp). Use qnode
  for small bundled CLIs, one reviewed package at a time. Don't aim for general
  Node compatibility: the long tail is `Buffer`, streams, `child_process`,
  `http`, bare-specifier ESM, and newer syntax that QuickJS 2024-02-14 lacks.

## How packages reach Node

The Nixpkgs 26.05 campaign inventory (`packages.csv`) lists 702 packages whose
own expression mentions Node tooling (`nodejs`, `buildNpmPackage`,
`fetchNpmDeps`, pnpm, yarn). Evaluating them for `pkgsFilc` with
nix-eval-jobs gave 574 derivations; 111 others fail to evaluate. With the
changes on this branch:

| Closure contains the Fil-C `nodejs-slim` | Packages |
|---|---:|
| no                                        |  77 |
| yes, directly referenced by the package   | 441 |
| yes, through another dependency           |  56 |

These are the reasons, roughly in order of how often each occurs:

1. **Build-time tool, native Node already.** Examples: neovim, cockpit,
   guile-hoot, and tiddlywiki's build step. `nativeBuildInputs = [ nodejs ]`
   splices to the native Node from cache.nixos.org, so these are not blocked
   by Node. The campaign blocks them for other reasons: neovim is waiting on
   greenlet, cockpit on polkit, guile-hoot on boehm-gc.
2. **Build-time tool, wrong platform.** Helpers that should run natively pick
   up the host (Fil-C) Node:
   - `fetchPnpmDeps` overrides `pnpm-fixup-state-db` with `pnpm.nodejs-slim`.
     Accessing an attribute of a spliced package, or calling `.override` on
     it, yields the host version. Fixed in `ports/overlay.nix` by calling
     `buildPackages.fetchPnpmDeps` with the build-platform pnpm. The fetcher is
     a fixed-output derivation, so its store path is unchanged. After the fix,
     these excluded packages no longer have the Fil-C Node in their closure:
     autoprefixer, bumpp, changelogen, element-call, element-web-unwrapped,
     equicord, it-tools, mcporter, meshtastic-web, metacubexd, mgrep,
     moonlight, ni, synchrony, vencord, zigbee2mqtt, and yt-dlp's
     yt-dlp-ejs.
   - binaryen puts the Fil-C `nodejs-slim` in `nativeCheckInputs`; only its
     wasm2js tests use it.
3. **Runtime Node.** `buildNpmPackage` adds the host Node to `buildInputs`
   and generates `exec node …` wrappers with it (441 packages). This includes
   static web front ends (fluidd, mainsail, …) whose output never runs Node.
   The wrapper hook still references it.

Caveat for group 2: packages that run Node at runtime then build, but their
wrappers exec the *native* Node. Verified with `pkgsFilc.ni`:
`bin/na` runs `/nix/store/…-nodejs-24.21.0/bin/node` (x86_64-linux, not
Fil-C). That is fine for static web assets (it-tools, element-web-unwrapped,
meshtastic-web, metacubexd). For CLIs and servers (ni, bumpp, changelogen,
mcporter, mgrep, zigbee2mqtt, synchrony) it means "builds, but the runtime is
not memory-safe". The campaign may want to treat those as excluded or rehost
them on qnode.

## Candidates

| Package | Kind | Node APIs used | QuickJS status |
|---|---|---|---|
| yt-dlp | Python; runs JS challenge solvers (yt-dlp-ejs) | none: upstream calls `qjs` directly | **supported upstream** (QuickJS ≥ 2023-12-09) |
| bibtex-tidy | single esbuild bundle, 140 KB | `require` of fs, assert, process; `fs.promises`, stdin events, argv/env/exit | **works on qnode**, output identical |
| aasvg | two ESM files | argv, exit, stdin `readable`/`read()`, console.warn | **works on qnode**, output identical |
| uglify-js | CommonJS, no dependencies | fs, `require.resolve`, `new Function`, `atob`, `process.stdout._handle` | **works on qnode**, output identical (not packaged) |
| clean-css-cli | CommonJS plus glob | `Buffer`, `process.openStdin` | fails: needs `Buffer` |
| csso-cli | CommonJS with an ESM dependency (clap) | `fs.createReadStream`, streams | fails: streams |
| sql-formatter | CommonJS bundle | `node:stream/consumers`, tty | fails: streams |
| terser | `"exports"` points at ESM `main.js` | ESM with bare specifiers | fails: needs a module loader or a bundle |
| js-beautify | CommonJS plus minimatch | class field named `set;` | fails: QuickJS 2024-02-14 parser bug |
| html-minifier | CommonJS | deeper util/stream use | fails |
| tiddlywiki, cjdns-tools | servers / network tools | http, net, dgram | not a target |
| Electron apps, language servers | large | the whole of Node | not a target |

Language servers (`*-language-server`, coc-*), npm/pnpm/yarn themselves, and
anything built on Electron need real Node and stay out of scope.

## Prototypes

### QuickJS regexp fix

`lre_exec_backtrack` returns the end of a `no_recurse` match as an
`intptr_t`, and `REOP_simple_greedy_quant` casts it back to a pointer. Under
Fil-C that integer has no capability, so the next character read traps:

```
$ qjs -e '/a+/.exec("xaa")'
filc safety error: cannot access pointer with null object.
    (qjs) libregexp.c:2140:13: lre_exec_backtrack
```

The patch rebuilds the pointer from the subject buffer:
`cptr = s->cbuf + ((uintptr_t)res - (uintptr_t)s->cbuf)`. This affected
*every* JS program that uses `+` or `*` in a regexp, so it is a prerequisite
for everything else here. The port previously skipped all checks; it now runs
`tests/quickjs-regexp.js`.

### yt-dlp on QuickJS

`ports/overlay.nix` overrides `yt-dlp` with `jsRuntime = final.quickjs`
(Nixpkgs' documented knob). It also drops curl-cffi (curl-impersonate needs Go)
and secretstorage (cryptography needs Rust); both are optional. With the
`fetchPnpmDeps` fix, the closure contains no Fil-C Node, Deno, Rust or Go.

Remaining blocker, unrelated to JS: `requests` → `charset-normalizer`, whose
pytest run traps under Fil-C in mypyc-compiled code. This is already a top
campaign blocker. Building without `requests` (yt-dlp falls back to urllib)
works; see the verification notes in the branch summary.

### qnode

`qjs --std --unhandled-rejection --stack-size 4000000 qnode.js SCRIPT ARGS`
provides:

- CommonJS `require` with `node_modules` lookup, `"exports"` (require/default
  conditions), JSON, `require.resolve` and `require.cache`
- ESM entry points via `import()`. Imports must be relative; there is no bare
  specifier resolution.
- `process`: argv, env, exit, cwd, stdin (read whole, then events),
  stdout/stderr, versions (reports Node 18)
- fs as utf-8 strings, in sync, callback and promise forms: read/write/copy,
  stat, readdir, mkdir, exists
- path (posix), assert, events, util (format, inherits, promisify), os, tty,
  url, `atob`/`btoa`
- stubs for child_process, crypto, http, https, net, readline, stream, vm,
  worker_threads and zlib. They load, and throw only when called.

The larger stack is needed: QuickJS's default 256 KiB JS stack overflows in
clean-css and sql-formatter under Fil-C.

`packages/qnode/npm-cli.nix` rehosts a natively built pure-JS npm package
(`buildPackages.<pkg>`): it copies `lib/node_modules`, strips native Node
shebangs, and wraps each binary with qnode. The npm install and bundling run
natively; only the runtime changes. `pkgsFilc.bibtex-tidy` and
`pkgsFilc.aasvg` use it, and their runtime closures contain no Node.

## Recommendation

1. Keep the QuickJS regexp fix. It is a real memory-safety trap in a ported
   package, independent of Node.
2. Take the yt-dlp change; it becomes useful once charset-normalizer is fixed.
3. Take the `fetchPnpmDeps` splicing fix. Decide how the campaign should count
   runtime-Node CLIs that now build against the native Node (see the caveat
   above).
4. Use qnode only for small, dependency-light CLIs, each with a byte-for-byte
   comparison against Node like `tests/qnode.nix`. Good next candidates:
   uglify-js, marked-man (needs a bundle), katex CLI. Adding `Buffer` (as
   `Uint8Array` plus utf-8 helpers) is the single change that would unlock the
   most packages (clean-css-cli and similar).
5. For ESM CLIs with bare imports (ni, terser, marked-man), bundle to one
   CommonJS file natively with esbuild at build time, then run the bundle on
   qnode.
6. A newer QuickJS (2025 releases, or quickjs-ng) would fix parser gaps such
   as the `set;` class field. It is a separate port, and the regexp code there
   was rewritten, so the Fil-C patch would need re-checking.
