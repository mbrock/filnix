"""Scope exclusions are policy decisions, separate from build failures."""

REASON = "Linux kernel; outside the Fil-C userspace runtime"


def kernel_metadata(metadata, source_file=None):
    if metadata.get("isLinuxKernel"):
        return True
    source = source_file or (metadata.get("position") or "").rsplit(":", 1)[0]
    if "/pkgs/" in source:
        source = "pkgs/" + source.split("/pkgs/", 1)[1]
    if source.startswith("pkgs/os-specific/linux/kernel/"):
        return True
    # Hardened kernels override meta.position to this aggregate expression.
    # Do not match arbitrary packages just because their names mention Linux.
    pname = metadata.get("pname") or ""
    return (
        source == "pkgs/top-level/linux-kernels.nix"
        and (pname == "linux" or pname.startswith("linux-"))
        and pname not in ("linux-headers", "linux-api-headers", "linux-firmware")
    )


def kernel_derivation(info):
    env = info.get("env", {})
    flags = env.get("buildFlags", "")
    if isinstance(flags, str):
        flags = flags.split()
    # Pinned Nixpkgs' generic/manual-config kernel builder. Unlike a name
    # prefix, these distinguish kernel images from headers and userspace tools,
    # including kernels renamed by overlays and native build dependencies.
    return "vmlinux" in flags and any(
        flag.startswith("KBUILD_BUILD_VERSION=") for flag in flags
    )
