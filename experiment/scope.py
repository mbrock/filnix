"""Scope exclusions are policy decisions, separate from build failures."""

import json
import re

REASON = "Linux kernel; outside the Fil-C userspace runtime"
TOOLCHAIN_REASON = (
    "Compiler toolchain (rustc, GCC, LLVM) built for or targeting Fil-C; "
    "outside the experiment, since filcc is the Fil-C compiler"
)
INHERITED = "Depends on a derivation outside the experiment's scope"

# GCC cross compilers name themselves after their target, and packages built
# for Fil-C carry its triple as a suffix. rustc targeting Fil-C keeps its plain
# name, so it is recognized by its configure flags (see toolchain_derivation).
FILC = "x86_64-unknown-linux-gnufilc0"
TOOLCHAIN_NAME = re.compile(
    rf"^(?:{FILC}-(?:gcc|gfortran|gnat|gccgo|gdc)"
    rf"|(?:llvm|clang|compiler-rt|compiler-rt-libc|lld|mlir|libclang|clang-tools|libllvm|polly|openmp)-{FILC}"
    r")-\d"
)
# V8 (Node.js) and Chromium (Electron, QtWebEngine) rely on JIT compilation,
# pointer compression and tagged pointers; porting them is out of scope.
V8_REASON = (
    "V8 or Chromium (Node.js, Electron, QtWebEngine); a JIT JavaScript engine "
    "outside the experiment's scope"
)
V8_NAME = re.compile(
    rf"^(?!.*-source)(?:nodejs|nodejs-slim|electron-unwrapped|qtwebengine)-{FILC}-\d"
)
# Multi-process servers that share pointer-containing memory between processes
# (PostgreSQL's shared buffers and catalogs, Apache and nginx scoreboards and
# shared zones); Fil-C capabilities do not survive in memory another process
# maps.
SHARED_MEMORY_REASON = (
    "Multi-process server sharing pointer-containing memory between processes "
    "(PostgreSQL server, Apache httpd, nginx); outside the experiment's scope"
)
SHARED_MEMORY_NAME = re.compile(
    rf"^(?!.*-source)(?:postgresql|apache-httpd|nginx|nginxQuic|freenginx|angie|angieQuic"
    rf"|openresty|tengine)-{FILC}-\d"
)
RUSTC_NAME = re.compile(r"^rustc(?:-unwrapped)?-\d")


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


def toolchain_derivation(name, info=None):
    """Whether a derivation is a compiler that Fil-C cannot (and need not) build.

    With ``info`` (a ``nix derivation show`` record), rustc counts only when it
    targets Fil-C; without it, the name alone decides.
    """
    if TOOLCHAIN_NAME.match(name or ""):
        return True
    if RUSTC_NAME.match(name or ""):
        return info is not None and f"--target={FILC}" in json.dumps(info)
    return False


def exclusion(name, info):
    if kernel_derivation(info):
        return REASON
    if toolchain_derivation(name, info):
        return TOOLCHAIN_REASON
    for pattern, reason in OUT_OF_SCOPE:
        if pattern.match(name or ""):
            return reason
    return None


OUT_OF_SCOPE = [(V8_NAME, V8_REASON), (SHARED_MEMORY_NAME, SHARED_MEMORY_REASON)]
