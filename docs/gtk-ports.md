# GTK, GObject introspection and GnuTLS

The September 2026 follow-up builds GTK3, GTK4 and their shared GNOME/TLS
dependencies using Fil-C. Both GTK versions pass the Broadway consumer check
below. It keeps the compiler, GLib 2.80.4 and Python 3.12.5 derivations unchanged.
The campaign can retry selected failed candidates from a committed revision;
its original source, inventory and attempt history remain intact.

## Source alignment

| Package | Filnix version | Upstream patch source |
| --- | --- | --- |
| GTK3 | 3.24.52 | `projects/gtk-3.24.52` |
| GTK4 | 4.14.5 | `projects/gtk-4.14.5` |
| GnuTLS | 3.8.9, retaining Nixpkgs security patches | `projects/gnutls-3.8.7.1` |
| gobject-introspection | 1.80.1 | `projects/gobject-introspection-1.80.1` |
| AT-SPI | 2.60.5 | `projects/at-spi2-core-2.60.5` |
| PyGObject | 3.48.2 | `projects/pygobject-3.48.2` |

These project directories exist at the existing ports pin,
`4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c`. The GTK/GI/GnuTLS project trees were
also unchanged at the upstream revision inspected on 2026-09-14,
`9a04915f14538072e0662f1dd16f1e3b22dd33e2`. No compiler rebuild or source-pin
change was needed. Existing upstream patches for GdkPixbuf, Graphene, Pango
and HarfBuzz are applied as well.

The patches primarily adapt pointer-valued GTypes. Generated Autotools changes
remain excluded: the existing compiler libtool hook handles those probes.
GnuTLS keeps Nixpkgs 3.8.9 and all six security patches; its upstream port changes
the atfork DSO argument and disables hardware acceleration.

## Matching generators to the target ABI

The introspection scanner loads a Python C extension, compiles C dumpers and
executes them against the inspected library. Native scanner tools cannot provide
Fil-C's GType and pointer semantics. The port builds its own scanner with Fil-C
Python, disables the prebuilt scanner path, and preserves the interpreter in
the installed shebang. GLib remains without introspection during bootstrap.

The scanner's test fixtures generate matching GLib/GObject/GModule/Gio GIRs and
typelibs. They are explicitly installed for consumers, since this GI version
normally expects GLib to install them. The port fixes static inline linkage,
new setuptools' MSVC module location, and the installed scanner's absolute ldd
path. All 60 introspection tests pass.

Consumers run build-platform generators, as in any Nixpkgs cross build, but
those generators are made for their Fil-C target. `ports/build-tools.nix`
overrides GLib, gobject-introspection and Meson only in the package set whose
target is Fil-C (`pkgsFilc.buildPackages`). Splicing selects that set for
`nativeBuildInputs`, so ordinary `callPackage` consumers receive these tools,
and the native package set stays unchanged.

GLib and gobject-introspection there are native twins of the ports, at the
same versions (2.80.4 and 1.80.1). Newer generators emit APIs the target GLib
lacks (gdbus-codegen 2.84+ calls `g_variant_builder_init_static`), and Meson
chooses scanner options by the build GI's version. The twins apply only the
target-neutral parts of the port patches, selected by file with `filterdiff`:

- gdbus-codegen and glib-genmarshal cast GTypes through `uintptr_t`;
- the scanner's `gdump.c` does the same, builds dumpers with debug
  information, and links them in the build environment;
- Meson's built-in enum template emits pointer-valued once initialization
  (`patches/meson-gtype.patch`).

The scanner compiles each dumper with the Fil-C compiler and runs it directly,
resolving its libraries with an absolute `ldd`. The Fil-C GI port above still
supplies the target GIRs and typelibs: the build GI propagates it to consumers
as a target dependency, and its setup hook puts Fil-C dependencies' GIRs on
`GI_GIR_PATH`. The scanner searches that before `XDG_DATA_DIRS`, where
build-platform GIRs would otherwise win. `tests/gi-link-environment.nix`
checks both.

`gio-querymodules` is different: it loads the GIO modules it indexes, so it
must be the Fil-C binary. The Fil-C GLib's setup hook gives Meson consumers a
cross file naming its own `gio-querymodules`, which Meson prefers over the
build GLib's. DConf, GLib networking and both GTKs use it at install time.

PyGObject uses the upstream GType patch and leaves the bootstrap Python type's
NULL metaclass initializer for `PyType_Ready` until its real metaclass exists.
The runtime check imports GI and exercises properties, a Python signal callback,
and a Gio memory stream.

## Other shared dependency fixes

- AT-SPI links `systemdLibs`, avoiding the full systemd tool closure. Its upstream
  patch and introspection remain enabled.
- DConf uses native Vala for VAPI generation, target GLib's DBus generator, and
  capability-preserving pointer operations for GTypes and once initialization.
  Its exported-symbol check expects Fil-C's real `pizlonated_` names. All 14
  DConf tests pass.
- Duktape's value-stack resize now rebases pointers from the new allocation,
  preserving offsets after realloc-triggered finalizers. A repeated large-call
  and GC check passes; downstream libproxy passes all six tests.
- libepoxy enables EGL independently of X11 for GTK's Wayland backend.

GTK enables Wayland and Broadway and disables X11. GTK4 also disables Vulkan,
Tracker and the optional GStreamer video backend. GTK3, DConf and Graphene API
documentation is disabled where its generators are not ported; GIR generation
is retained. GTK3's disabled documentation output is removed as well. Graphene
currently reports no tests defined for the cross build.
GTK's upstream suites remain disabled as in the Nixpkgs recipes. GTK4 4.14.5
cannot satisfy applications requiring newer APIs; successful toolkit builds do
not establish compatibility for every GNOME application.

## Reproducing the checks

Observed results on 2026-09-14:

| Check | Result |
| --- | --- |
| GObject introspection suite | 60 passed |
| DConf suite | 14 passed |
| libproxy suite | 6 passed |
| GLib networking suite | 6 groups passed, no skips |
| GnuTLS TLS, certificate and slow suites | 526 passed, 60 skipped, no failures |
| GTK3 and GTK4 Broadway consumers | Both passed |
| PyGObject properties, callbacks and Gio | Passed |
| Duktape stack resize and GC | Passed |

Libmicrohttpd 1.0.1 also builds unchanged against the repaired dependency stack.

Evaluation checks scanner selection, retained GnuTLS security patches and the
shared dependency choices without building during evaluation:

```sh
nix eval --impure --json --offline \
  --option allow-import-from-derivation false --file tests/gtk-ports.nix
```

Focused downstream checks are exposed as flake checks:

```sh
nix build .#checks.x86_64-linux.pygobject \
  .#checks.x86_64-linux.gtk3-runtime \
  .#checks.x86_64-linux.gtk4-runtime \
  .#checks.x86_64-linux.glib-networking \
  .#checks.x86_64-linux.gnutls-tls \
  --no-link --keep-going --max-jobs 2 --cores 4 -L
```

The GTK checks compile Fil-C applications and run against Broadway, exercising
builder-created widgets, properties, signals, Pango text shaping and a PNG
round trip. They are focused consumer checks, not the GTK upstream suites or
a visual validation.

GLib networking's six test groups pass, including TLS connection and session
expiry tests. Its check uses a reproducible CA bundle and resolves libc directly
for its clock interposer because Fil-C does not implement `RTLD_NEXT`.

The GnuTLS check runs the TLS, certificate and slow suites separately from
gnulib's allocator, stack-inspection and inline-assembly portability probes.
It fixes the test PKCS#11 module's atfork DSO argument just like the library's
upstream port, and recognizes Fil-C's abort signal in the deliberate invalid-API
subtests. The main cross-built packages retain their original check settings;
separate checks do not invent test evidence in the campaign catalog.

Investigation logs and graph comparisons are retained locally in
`results/gtk-unlock/`. Nix build logs are available with `nix log` on the recorded
derivations, and campaign retries retain both original and replacement recipes.
