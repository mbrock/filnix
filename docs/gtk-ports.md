# GTK and GObject introspection ports

These ports are enabled for build attempts. Patch application and dependency
evaluation have been checked; this checkpoint has not compiled or run them.
The existing experiment uses a frozen source snapshot and is unaffected.

## Source alignment

| Package | Filnix version | Upstream patch source |
| --- | --- | --- |
| GTK3 | 3.24.52 | `projects/gtk-3.24.52` |
| GTK4 | 4.14.5 | `projects/gtk-4.14.5` |
| GnuTLS | 3.8.9, retaining Nixpkgs security patches | `projects/gnutls-3.8.7.1` |
| gobject-introspection | 1.80.1, matching GLib 2.80.4 | `projects/gobject-introspection-1.80.1` |

All four project directories are already present at the ports pin,
`4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c`. Their trees are unchanged at the
upstream revision inspected on 2026-09-14,
`9a04915f14538072e0662f1dd16f1e3b22dd33e2`. Neither source pin needs to move.

GTK3 and GnuTLS patches were extracted with `ports/extract-patch.sh`. Repeating
extraction for GTK4 and introspection reproduced their existing patches byte
for byte. The GTK patches adapt GType handling to Fil-C's pointer semantics;
they are more than configure-script workarounds. Generated Autotools changes
remain excluded; the compiler's existing libtool setup hook handles its probes.

The GnuTLS patch changes the `__register_atfork` call's DSO argument. It also
applies to Nixpkgs' 3.8.9, so the port keeps that release, the certificate-path
patch, and all six existing security patches. Hardware acceleration is disabled
as in upstream's build recipe.

The backend choices follow upstream's
[GTK3 recipe](https://github.com/pizlonator/fil-c/blob/4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c/pizlix/build_postlc4_chroot_project_gtk3.sh)
and
[GTK4 recipe](https://github.com/pizlonator/fil-c/blob/4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c/pizlix/build_postlc4_chroot_project_gtk4.sh):
Wayland and Broadway enabled, X11 disabled, and Vulkan disabled for GTK4.
Tracker support is disabled. Both ports explicitly request introspection.
Nixpkgs' disabled GTK test suites remain disabled; the upstream recipes do not
run those suites either.

GTK4 is intentionally aligned with the upstream port's 4.14.5 source. A
downstream package that requires a newer GTK can still fail at configure time.
Removing the old blanket exclusions does not establish compatibility for every
dependent package.

## Bootstrapping introspection

Introspection builds a C extension for its Python scanner, and the scanner
compiles and runs small programs linked against the library being inspected.
Fil-C Python must load the Fil-C extension; the generated programs also need
the upstream-patched GType dumper.

Nixpkgs normally supplies prebuilt scanner tools to a cross build. Here the
Fil-C host binaries can run directly on the build machine. The port therefore:

1. Removes its prebuilt introspection input and builds its own scanner with
   `gi_cross_use_prebuilt_gi=false`.
2. Selects Fil-C Python with mako, markdown and setuptools. A small local Meson
   patch preserves that interpreter in the generated scanner's shebang.
3. Uses GLib without introspection while bootstrapping. The existing GLib port
   and compiler derivations stay unchanged.
4. Enables the test subdirectory when `meson.can_run_host_binaries()` is true.
   This builds the patched fixtures and installs their matching source files
   for downstream users such as PyGObject. The Nix check phase stays enabled.
5. Removes the cross-build step that copies documentation and test sources
   from native introspection 1.84. API documentation is disabled for the
   introspection package, so its unused `devdoc` output is also removed.

GTK3 and GTK4 explicitly receive the Fil-C introspection wrapper as their
scanner input. Ordinary Nix splicing would otherwise supply native tools.
This override is limited to these two ports; other packages that generate
introspection data may need the same adjustment when they are tested.

## Validation and next build

Run the evaluation regression check without permitting builds during evaluation:

```sh
nix eval --impure --json --offline \
  --option allow-import-from-derivation false --file tests/gtk-ports.nix
```

It resolves all four derivations, checks the scanner/Python ABI selection and
the lack of a direct prebuilt/self scanner input, and verifies that GnuTLS
retains Nixpkgs' release and patches.

At this checkpoint, the complete patch lists were applied in Nix order to
downloaded release archives. All upstream patches and the local introspection
patch apply with zero fuzz. Nixpkgs' existing GTK3 immodules-cache patch uses
one line of fuzz with the normal patch invocation. The GTK post-patch script
paths also exist in the selected versions. The compiler, Fil-C GLib, native
GLib and native introspection derivation paths match the pre-change baseline.

The next useful build is introspection alone: it exercises scanner bootstrap,
GLib/GObject/Gio GIR generation and the test fixtures before GTK is attempted.
After it succeeds, try GnuTLS, GTK3 and GTK4 separately, followed by a small
downstream introspection consumer. Neither those builds nor changes to the
running campaign are part of this checkpoint.
