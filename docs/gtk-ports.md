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
patches Meson in the package set whose target is Fil-C
(`pkgsFilc.buildPackages`) and builds GLib and gobject-introspection twins
from it. The twins are named only in the Fil-C set's view of that set
(`pkgsFilc.pkgsBuildHost`, which `buildPackages` and splicing read), so
ordinary `callPackage` consumers receive these tools in
`nativeBuildInputs`, while native packages inside the set still link the
ordinary GLib and match the native package set.

The twins used to replace `glib` for the whole set. Every native library
there that links GLib was then rebuilt against GLib 2.80.4, off
cache.nixos.org: Pango 1.57 wants GLib 2.82, so `pangocairo` and
`gtk+-3.0` had no usable pkg-config (libdecor, i3), glibmm-based libxml++
tests exited 127, and gjs's debugger tests failed. Fil-C packages reached
them through tools such as `sdl2-config` (SDL → PipeWire → FFADO →
libxml++) and fontforge (DejaVu → fontconfig). Qt is still aliased to the
native set's: its qmake hook comes from `buildPackages`, whose qtbase is
not this set's even without the twins, so native Qt modules such as qtsvg
(reached through `wrapQtAppsHook` → qtwayland → qtdeclarative) saw two
qtbases and qtbase's setup hook stopped with "detected mismatched Qt
dependencies". Qt's generators emit no GType code; the gobject-introspection
wrapper and PyGObject get the same treatment. Native tools there still
propagate the ordinary GLib and GI into Fil-C builds (gdk-pixbuf, PyGObject),
so the twins' setup hooks put their generators first on PATH after all
other hooks have run.

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
- dbus-glib switches on `(uintptr_t)` GType values. Its `dbus-binding-tool`
  needs no build-platform twin: its glue names GTypes by macro, and server
  marshallers come from the Fil-C-targeted `glib-genmarshal`. The
  `dbus-glib` check calls a Fil-C service with containers, variants and a
  signal through that glue.
- json-glib switches on `(uintptr_t)` GType values and orders its boxed
  transform list by comparing them, rather than subtracting GTypes into a
  `gint`. Its tests compare type names; all 18 suites pass. libdbusmenu's
  installed JSON loader needs the same switch cast.
- glibmm clears `G_SIGNAL_TYPE_STATIC_SCOPE` in its defs generator with
  `zandptr`, and gains an identity `TypeTraits<GType>`: otherwise a pointer
  GType selects the container traits meant for GObject wrapper pointers.
  glibmm 2.88 and gtkmm 4.22 need GLib 2.87 and GTK 4.22, so `glibmm_2_68`
  and `gtkmm4` are pinned to 2.80.1 and 4.14.0. Both cairomm versions
  pass their Boost.Test suites (see the Boost port). The `glibmm`, `glibmm_2_68`, `gtkmm3-runtime` and
  `gtkmm4-runtime` checks cover derived types, properties, signals, GValue,
  variants, `wrap()` and list models, the latter two on Broadway.
- libepoxy enables EGL independently of X11 for GTK's Wayland backend.

GTK enables Wayland and Broadway and disables X11. GTK4 also disables Vulkan,
Tracker and the optional GStreamer video backend. GTK3, DConf and Graphene API
documentation is disabled where its generators are not ported; GIR generation
is retained. GTK3's disabled documentation output is removed as well. Graphene
currently reports no tests defined for the cross build.
GTK's upstream suites remain disabled as in the Nixpkgs recipes. GTK4 4.14.5
cannot satisfy applications requiring newer APIs; successful toolkit builds do
not establish compatibility for every GNOME application.

## GTK 2

GTK 2.24.33 has no upstream Fil-C port. `patches/gtk2-filc-gtype.patch` makes
the GTK 3 port's changes to the older sources and is applied after
the Nixpkgs patches. Unlike GTK 3/4 here, GTK 2 keeps its X11 backend, since
it has no other backend on Linux, and GAIL is still built as its
accessibility module.

With GType a pointer, the unpatched sources do not compile. The changes are:

- **Fundamental-type switches.** GtkArg conversion (`gtkobject.c`,
  `gtksignal.c`), key-binding argument copying and marshalling
  (`gtkbindings.c`), GtkBuilder value parsing, GtkSettings, and tree-model
  row storage (`gtktreedatalist.c`) switch on `(uintptr_t)` of the type, with
  `(uintptr_t)` case labels. Fundamental types are small constants, so
  this only compares addresses.
- **Signal scope flags.** `TYPE | G_SIGNAL_TYPE_STATIC_SCOPE` becomes
  `zorptr(TYPE, ...)`, and GtkArg's `type & ~G_SIGNAL_TYPE_STATIC_SCOPE`
  becomes `zandptr`, so registered GTypes keep their capability. This covers
  about 50 signals in GtkWidget, GtkTextBuffer, GtkTreeModel, GtkEntry and
  others.
- **Type registration.** GAIL's accessible factories (the
  `GAIL_IMPLEMENT_FACTORY` macro) and `GailCellParent` use a pointer
  `g_once_init_enter_pointer`/`_leave_pointer`, as the GTK 3 templates do.
  GTK 2's own enum types come from pre-generated `gtktypebuiltins.c`, whose
  `static GType etype` is already fine.
- **GTypes in integers.** GtkComboBoxText held a model's column type in a
  `gint`. No code stores a GType through `G*_TO_POINTER` or similar casts.
- **Clang errors outside GType.** GtkScale passed its three-argument mark
  comparator through a `GCompareFunc` cast. `tests/testmenubars.c` used a
  K&R parameter and an extra argument, and `tests/testtreeview.c` walks
  types numerically (fixed as in the GTK 3 port).

`checks.gtk2-runtime` compiles `tests/gtk2-runtime.c` with Fil-C and runs it
against a native Xvfb server with `GTK_MODULES=gail`. It exercises:

- GtkBuilder type lookup and properties;
- signal emission, including the flagged `insert-text` and `row-inserted`
  signals;
- a GtkBindingSet entry and an RC-file binding, activated by key;
- list-store storage and sorting of string, int, double and boolean columns;
- GtkComboBoxText, GtkSettings and GtkScale marks;
- GAIL's accessible types;
- Pango text measurement and a PNG round trip through GdkPixbuf;
- showing and mapping a window, then running `gtk_main` until a timeout
  quits it.

The run produces no GLib warnings or criticals.

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
  .#checks.x86_64-linux.gtk2-runtime \
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
