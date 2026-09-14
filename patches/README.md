# Local Filnix patches

This directory contains changes maintained by Filnix. Upstream extraction writes
to `ports/patch/`; both importers reject this directory (including symlinks and
subdirectories) as an output destination. `make -C ports clean` only removes
the generated `ports/patch/` directory.

Keep a local addition separate from an extracted patch even when both modify
the same file. List the upstream patch first and the local patch second in
`ports.nix` or the package's Nix expression. Nix applies that list in order.
An inventory entry in `ports/patches.nix` does not enable a port by itself.

Use a descriptive package-and-purpose filename. New local patches should begin
with a short provenance header, followed by an ordinary unified diff:

```
Subject: What this change fixes
Origin: Filnix
Upstream-Status: Not submitted
Applies-After: ports/patch/package-version.patch

Explain the failing behavior, why this differs from the upstream port, and
where its regression check lives. Omit Applies-After when no upstream port
patch is used. Replace Upstream-Status with an issue/commit link when available.
```

On an upstream refresh, regenerate only `ports/patch/`, then apply the complete
ordered patch list to the selected release. A conflict in a local patch is a
review point: check whether upstream has absorbed or superseded the fix. Remove
the local patch only after verifying the replacement behavior. Never copy local
hunks back into the generated patch to make a refresh appear clean.

Older patches may not yet have these headers. Their location and explicit Nix
patch list still define ownership and application order; add provenance when
touching them rather than rewriting every historical patch at once.
