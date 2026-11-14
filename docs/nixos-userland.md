# A Fil-C userland for NixOS: the record

`nixosModules.default` ([lib/filc-system.nix](../lib/filc-system.nix), with
[nixos/default.nix](../nixos/default.nix)) makes a NixOS system's `pkgs` the
Fil-C package set, the same way it does for finix. systemd, D-Bus,
util-linux, Linux-PAM, coreutils, OpenSSH and every service a module starts
become Fil-C builds without per-service overrides. The kernel, the
bootloader and the packages in
[lib/native-exceptions.nix](../lib/native-exceptions.nix) stay native;
[docs/nixos.md](nixos.md) says how to use it and has the table of
exceptions.

This page is the running record of the work: what had to change to get a
NixOS to boot this way, and what is still open.

Status (2026-11-05): the VM test [tests/nixos/userland.nix](../tests/nixos/userland.nix)
(`nix build .#nixosTests.userland`) passes. The machine boots through a
Fil-C initrd and stage 2, `alice` logs in on tty1 through the Fil-C PAM,
PID 1, journald, udevd, logind, dbus-daemon, sshd and the login shell all
map libpizlo, no unit fails, and `filc-ps` finds no native process outside
the exceptions.

## Why the exceptions are what they are

The Rust entries are there because the package set refuses to evaluate Rust
and Go packages ([lib/block-rust-go.nix](../lib/block-rust-go.nix)), and
NixOS 26.05 has rewritten several of its own boot and activation tools in
Rust: `nixos-init`, `makeInitrdNGTool`, `switch-to-configuration-ng`, and
fish 4, which `users-groups.nix` compares every user's shell with.

The native packages come from a separate, plain import of filnix's Nixpkgs
(`filc.nativePackages` to choose another). Not
`pkgsFilc.pkgsBuildBuild`: the variants it derives, such as `pkgsStatic`,
inherit the Fil-C crossSystem's `replaceCrossStdenv`, so the "static native"
setuid wrappers were built by filcc and failed to link
(`ld: --no-dynamic-linker: unknown option`). Not `buildPackages` either: its
target platform is Fil-C, which matters for any package that is itself a
compiler (Emacs' native compilation pulled in a Fil-C-targeted libgccjit
that way).

## Obstacles and decisions

### systemd: 260, not upstream Fil-C's 256.4

The Fil-C systemd port was 256.4, upstream Fil-C's version
(`ports/patch/systemd-256.4.patch`), while Nixpkgs and its NixOS modules are
at 260.4. That skew stopped the build in three places: the systemd and
initrd modules link every upstream unit they know of and failed on
260-only ones (`missing …/example/systemd/system/breakpoint-pre-udev.service`,
97 units in all); the initrd module copies 260-only programs
(`systemd-factory-reset`); and `systemd.package`'s `apply` appends
`postpone-d-bus-queue-dispatch.patch`, a 260 fix that does not apply to 256.
Stubbing the units and dropping the patch got 256 to build and the native
initrd to hand over, but the Fil-C 256 PID 1 then died at once after
switch-root, silently: systemd points its stdio at /dev/null before the
runtime prints its panic.

So the port now builds Nixpkgs' own systemd, with
[patches/systemd-262-filc.patch](../patches/systemd-262-filc.patch): upstream
Fil-C's changes rebased (version script, signal reset, bus error maps
without ELF sections), plus what 260 and 262 need. Its header lists each
change. Systemd 262 (Nixpkgs 26.11) keeps its command-line verbs and
options in ELF sections, which Fil-C cannot link; the patch does not
handle that yet.
The ones that matter at run time:

- `pidfd_spawn()` in the Fil-C glibc stops the program
  (`spawni.c:342: … assertion !use_pidfd failed`); PID 1 starts every
  service with it. systemd uses plain `posix_spawn()` instead. 256 has the
  same call, which is the likely cause of the 256 PID 1 dying.
- Fil-C's `syscall()` stops the program on numbers it does not support
  instead of returning ENOSYS. systemd's raw wrappers (kcmp, bpf, ioprio,
  pivot_root, quotactl_fd, setxattrat, rt_tgsigqueueinfo, …) return ENOSYS
  under Fil-C, where systemd has fallbacks. kcmp mattered: Fil-C's `fcntl()`
  rejects `F_DUPFD_QUERY`, so `same_fd()` fell through to it.
- PID 1 died at once in the initrd on `syscall(SYS_capget)`
  (`filc user error: unsupported syscall: 125` in `have_effective_cap`).
  capget and capset now go through glibc's wrappers, `raw_reboot()` through
  glibc's `reboot()`, and `raw_clone()` forks and `unshare()`s the child
  (refusing `CLONE_NEWPID`, which cannot be had that way).
- Fil-C reserves SIGBUS, so journald and journalctl no longer install a
  SIGBUS handler for truncated journal files.
- systemd 257+ `dlopen()`s most optional libraries by soname, and Fil-C's
  `dlopen()` ignores RUNPATH, so the port rewrites those sonames to
  absolute paths.
- `getauxval()` returns addresses as plain integers under Fil-C, so the
  `memcpy` from `getauxval(AT_RANDOM)` in `random-util.c` and
  `osc-context.c` panicked, as did `get_runpath()`'s walk of
  `getauxval(AT_PHDR)`. Under Fil-C they skip the auxv data (it only mixes
  entropy into a fallback seed and an ID that the pid and pidfd ID still
  make unique) and report no runpath.
- `clone_with_nested_stack()` (used by `asynchronous_close()`) called
  glibc's `clone()`, which stops a Fil-C program. It returns ENOSYS under
  Fil-C, and callers close synchronously.
- The compiler drops `section()` on globals, so the `.note.dlopen` notes
  are lost, and make-initrd-ng reads those notes to copy a binary's
  dlopen()ed libraries into the initrd. Without libkmod there,
  `systemd-modules-load` failed ("Failed to initialize libkmod context:
  Operation not supported"), the initrd loaded no modules, and
  `initrd-find-nixos-closure` could not find the system under /sysroot.
  The notes' JSON survives as data, so the port's postFixup puts them back
  with objcopy ([ports/restore-dlopen-notes.py](../ports/restore-dlopen-notes.py)).

systemdMinimal and systemdLibs derive from the port, so they are 260 too.

### Runtime and glibc fixes

These are outside package ports, so each has an Oracle review and a failing
regression, and they land together in one reviewed batch (one rebuild of
the Fil-C world), carried by the finix thread:

- Fil-C's `prctl()` returned ENOSYS for `PR_CAPBSET_READ`,
  `PR_CAPBSET_DROP` and `PR_CAP_AMBIENT`, so PID 1 started no service
  ("Failed to apply the starting ambient set: Function not implemented").
  [patches/filc-runtime-prctl-caps.patch](../patches/filc-runtime-prctl-caps.patch)
  passes them to the kernel; `checks.x86_64-linux.runtime-prctl-caps`.
- glibc's `__openat64_nocancel` made a raw syscall (nftw, scandirat, fts);
  brk, sched_setattr and pidfd_spawn stopped the program. Fixed by the
  finix thread's `patches/filc-glibc-openat-nocancel.patch` and
  `patches/filc-glibc-unsupported-syscalls.patch`. systemd 260 does not fall
  back from `pidfd_spawn()` on ENOSYS (`process-util.c`), so the port keeps
  `HAVE_PIDFD_SPAWN=0`.
- `settimeofday(NULL, tz)` (glibc's `__settimezone`) made a raw syscall.
  The stage-2 PID 1 calls it from `clock_reset_timewarp()` right after
  switch-root (the initrd skips it), so the machine got through the whole
  initrd and then died. [patches/filc-glibc-settimezone.patch](../patches/filc-glibc-settimezone.patch)
  routes it through `zsys_settimeofday`; `checks.x86_64-linux.glibc-settimezone`.

While these were being found, a debug VM put the patched libpizlo and glibc
on `LD_LIBRARY_PATH` (PID 1's `ManagerEnvironment` in the initrd and stage 2,
plus `DefaultEnvironment` for services), so each fix could be tried without
rebuilding the world. With the batch built in (finix-demo ef34345c28b9), the
VM test passes without it.

### Seeing why PID 1 died

systemd points its stdio at /dev/null early, so a Fil-C panic in PID 1
prints nowhere and the kernel only reports `trap int3 … in libpizlo.so`
and "Attempted to kill init". In the test VM `/dev/console` is tty0 (the
last `console=`), not the serial port the driver logs, so reopening the
console does not help either; the panic has to go to `/dev/ttyS0`.

- In the initrd: make `/init` a script that runs
  `strace -D -f -o /dev/ttyS0 …/systemd` (`-D` keeps systemd PID 1),
  adding strace, bash and util-linux to `boot.initrd.systemd.storePaths`.
  The panic text shows up in the traced `write(2, …)`.
- After switch-root, systemd kills the initrd's strace and re-executes
  itself. What worked was a debug patch that re-executes through a wrapper
  named in an environment variable (set with
  `boot.initrd.systemd.managerEnvironment`), the wrapper running
  `exec 2>/dev/ttyS0; exec "$@"`. strace across the re-exec was not
  usable: it lost the main thread's syscalls.
- Not `FILC_LOG_TO_FILE`: the runtime then reserves an fd for its log,
  and systemd's fcntl() on every fd stops it in `check_fd`
  (`!is_reserved_fd(fd)`), a crash of the debugging setup itself.

### NSS

NixOS loads NSS modules (nss-systemd, nss-myhostname) only into nscd and
asserts that nscd is on whenever `system.nssModules` is not empty. Neither
nscd works here: the Fil-C glibc is built without nscd, and NixOS's default
nsncd is Rust, which as a native process could not load the Fil-C NSS
modules anyway. The module turns nscd off and empties `system.nssModules`,
so names resolve from `/etc` files only: DynamicUser= names and
`myhostname` do not resolve through NSS. systemd itself does not need NSS
for DynamicUser=.

Activation's `update-users-groups.pl` still runs `nscd --invalidate` and
prints "Can't exec "nscd": Function not implemented". The error is
harmless, but the errno is wrong: every failed `exec` in the Fil-C perl
reports ENOSYS, with or without a PATH search, while the kernel returns
ENOENT (strace) and a Fil-C C program's `execv`/`execvp` gets ENOENT. The
runtime's execve wrapper keeps the kernel's errno, so something on perl's
exec path after the failed execve overwrites it. Not yet found.

Two further facts for whoever fixes this: the Fil-C glibc looks NSS modules
up as `libnss_<name>.so.6662` (its `shlib-versions`), while systemd installs
`libnss_systemd.so.2`; and `dlopen` of a bare soname ignores the caller's
RUNPATH ([filc-findings.md](filc-findings.md)). The likely fix is a Fil-C
nscd, which means building glibc's nscd in the Fil-C glibc (a glibc change,
so it needs the Oracle review in AGENTS.md).

### D-Bus: dbus-daemon, not dbus-broker

NixOS 26.05 defaults to dbus-broker. Its Fil-C build fails its test suite on
real memory-safety findings, for example `c_rbtree_store` writing a pointer
with no capability (c-rbtree keeps flag bits in its parent pointers) and a
`memcpy` from a null object in `config_parser_init`, and the launcher's
`util_fork_broker` fails with `Function not implemented`. The module sets
`services.dbus.implementation = "dbus"`, the reference dbus-daemon, which is
ported. Porting dbus-broker (and c-rbtree) is open.

### QEMU guest agent

The test framework turns on `services.qemuGuest`, whose agent comes from the
full QEMU build. Its Fil-C dependencies dtc (a test data file in assembly)
and libiscsi (`-Werror=cast-align`) do not build yet. The tests turn the
agent off; the driver does not use it.

### PrivateUsers=

Nixpkgs' service tests (`nixosTests`) found that every unit with
`PrivateUsers=` (mosquitto, redis, tor) failed at step USER: "Failed to set
up user namespacing: Invalid argument". systemd sets it up with
`unshare(CLONE_NEWUSER)` in the forked child, and the kernel refuses that to
a multithreaded process; a Fil-C process always runs the runtime's own
threads (PHP's `pcntl_unshare_01` fails for the same reason,
docs/php-port-notes.md). The module turns `PrivateUsers=` off for every
service with a top-level drop-in, `service.d/zz-filc-no-private-users.conf`.
Making it work would need a single-threaded window in the runtime around
`unshare`, which is open.

### Servers that share pointers between processes

Fil-C keeps each pointer's capability in per-process shadow memory. A
pointer that one process stores in memory it shares with another process
arrives there as a bare address, with no capability, and using it stops the
program. Servers built around shared memory that holds pointers cannot be
Fil-C, and are refused at evaluation:

- PostgreSQL: its backends share buffers and state that hold pointers.
  Filip Pizlo tried to port it for a long time and concluded that this is
  a fundamental problem. (The builds here also showed Nixpkgs turning on
  JIT, which needs an LLVM that isn't ported, and `-flto`, which Fil-C
  can't link; those were fixable, the sharing is not.)
- nginx: its workers share pointers through shared memory zones.
Keep them native with `filc.native`; for a Fil-C web server or reverse
proxy, use lighttpd, which is one process, or Apache.

Apache is ported: its scoreboard, the shmcb TLS session and socache
caches and its mutexes hold integers, strings and offsets, which cross
processes fine (`nixosTests.apache` runs prefork and event under load).
Two modules kept pointers there: the port moves mod_auth_digest's client
table to apr_rmm offsets, and makes mod_ldap ignore its shared cache
(`LDAPSharedCacheSize`), so each process keeps its own. Client libraries such as libpq
stay Fil-C.

### First boot on EC2

The first launch of filc.less.rest found two bugs that the VM boot check
could not, since it boots without user data:

- `filnix-first-switch` was a oneshot wanted by multi-user.target, and a
  target is ordered after the units it wants. switch-to-configuration
  started multi-user.target and waited for that job, which waited for the
  unit running the switch. It is a simple service now, and
  `nixosTests.first-switch` boots with `#filnix` user data naming another
  system and checks that it switches and boot finishes.
- `nixos-rebuild --option max-jobs 0` planned to build 78 derivations,
  although their outputs were cached, and failed. NixOS marks the system
  and its small generated files `allowSubstitutes = false`, which Nix
  honours unless `always-allow-substitutes` is set; `nix build` of the
  store path worked because substituting a path by name ignores it. The
  base image sets `always-allow-substitutes = true`. It was not the cache
  or the native Nix: the same command against an empty store, with that
  option, fetches all 806 paths and builds nothing.

The release AMI's check found one more: a unit that fails after the switch
(ACME, while the name points elsewhere) makes switch-to-configuration exit
with 4, and the service then left its done marker unwritten and would switch
again on every boot. Status 4 means the new system is active, so the service
now logs the failed units and writes the marker; the test's target has a
unit that fails.

### Service tests

Fixes and exceptions the `nixosTests` matrix needed:

- PHP 8.3 is not ported, and MediaWiki's module defaults to it; the tests
  and demo-wiki set `services.mediawiki.phpPackage` to PHP 8.4.
- nginx and the PostgreSQL server (above) are native in the tests that
  use them; MediaWiki and WordPress run behind Fil-C Apache.
- MariaDB is not ported yet: its client library's linker version script
  names the C symbols, which Fil-C prefixes with `pizlonated_` ("undefined
  symbol 'mysql_affected_rows' referenced in expression"). The MySQL tests
  keep the server native; PHP's MySQL drivers use mysqlnd, not libmariadb.
- knot-dns (the unbound test's client, kdig) needs xdp-tools, whose BPF
  programs need a cross compiler that doesn't build; without XDP it builds
  but fails 161 of its 211 tests with Fil-C safety stops ("cannot read pointer with
  null object"); the test keeps it native. Porting it is open.
- lighttpd's HTTP/2 module: ls-hpack kept decoder table entries as
  `uintptr_t`, so closing an HTTP/2 connection freed pointers without
  capabilities and Fil-C stopped lighttpd (found by the demo-wiki test);
  [patches/lighttpd-ls-hpack-pointers.patch](../patches/lighttpd-ls-hpack-pointers.patch).
  The same test found that serving a static file over HTTP/2 stopped it in
  the Fil-C glibc's `preadv2` (docs/filc-findings.md); lighttpd is built
  without `preadv2`.
- davfs2 (Nextcloud's test client): cross autoconf assumed a broken
  `malloc(0)` and substituted an `rpl_malloc` nobody defines. It builds
  with that fixed, but its `mount.davfs` daemon stops with a Fil-C trap
  after it forks and closes stderr, so the trace is lost; the Nextcloud
  tests keep davfs2 native. Open.
- `mount(8)` with a helper stopped in libmount's `fsopen(NULL)` probe
  (docs/filc-findings.md); fixed in util-linux, and mount units use the
  classic `mount(2)`.
- `opensshPackages.openssh` is ported too, so Nixpkgs' variants made with
  `.override` (no PAM, null PAM) keep the patch. Its variant without
  OpenSSL cannot use the Fil-C PAM: pam_unix's `crypt_r` from libxcrypt does
  not resolve in that sshd. That test node runs the regular Fil-C OpenSSH;
  why is open.

### Package fixes

These came up once PID 1 reached multi-user.target:

- acl 2.4: libmisc's `getxattrat`/`setxattrat`/… and `openat2` used raw
  `syscall()`, so `setfacl -R`, `getfacl -R` and NixOS's resolvconf
  service (which runs setfacl) stopped on syscall 464.
  [patches/acl-2.4-filc.patch](../patches/acl-2.4-filc.patch) uses the
  path-based xattr calls under Fil-C.
- dhcpcd 10.3: its rbtree kept the parent pointer in a `uintptr_t`, which
  drops the capability (`rb_tree_remove_node`: "cannot write pointer with
  null object"); fixed by the finix thread's
  `patches/dhcpcd-10.3-rbtree-pointer.patch`.
- kbd: autoPatchelfHook, there only for `.note.dlopen`, replaced the
  RUNPATH and dropped the Fil-C runtime, so `loadkeys` (and
  systemd-vconsole-setup) could not start. Turned off; kbd uses
  `dlopenByPath` like systemd.

- texinfo-interactive: its tests run texi2any with the build platform's
  Perl, which cannot load the Fil-C XS modules; checks skipped in ports.nix.
