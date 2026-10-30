# What campaigns mean

A campaign is a frozen, bounded observation of Nix realising named roots at
one Filnix revision. It is not the port inventory, a fresh rebuild guarantee,
or a release. Success includes existing and substituted outputs and the
package's enabled checks, not every flake check or comprehensive runtime tests.

## Two questions, two selections

- **Expected** (`ports/expected.nix`): an explicit compatibility expectation
  checked per revision. Start conservatively with the curated baseline and
  established world landmarks, whose successful recordings give a useful
  starting expectation. Review additions using build/check and consumer
  evidence for the exact configured variant. A failure is a regression to
  investigate, not permission to automatically shrink the list.
- **Exploration** (`scope = "ports"`): the world plus declared port recipes.
  A declaration is an adaptation to try, not a support promise. Failures are
  research findings. `world` remains a shell/VM composition, not the definition
  of expected compatibility.

Both selections put `scripts/ci-outputs.txt` first, unchanged: distribution
artifacts need early publication. `scripts/ship-outputs.txt` remains the smaller
compiler/baseline push gate. Do not make every exploratory port a push gate.

Record known incompatibilities with the port's `broken` declaration and a
reason. The manifest must distinguish deliberate exclusions (including a
known broken dependency) from unresolved evaluation errors. Expected selection
evaluation errors must fail freezing rather than silently remove obligations.
The known PipeWire blocker and its observed consumers remain visible outside
the expected list as exclusions, not as successes or expected regressions.

### PipeWire evidence (2026-10-24)

`nix log /nix/store/y2h436ydl72l3maya6a4rhf1128idvph-pipewire-x86_64-unknown-linux-gnufilc0-1.6.6.drv`
from `ports-a324a843` reports 51 passing tests and one failure:
`test-loop` / `cancel_thread_while_dispatching` traps with SIGTRAP after
`libgcc_s.so.6661 must be installed for pthread_cancel to work`.
The trace goes through `__pthread_cancel` and `pw_data_loop_stop`. This is a
current cancellation-runtime limitation, not a missing native libgcc package.
It is not evidence establishing exactly when patch removal introduced it.
Marking PipeWire broken also rejects `wireplumber`, `sdl3`, `sdl2-compat`,
`cava`, `sfml_2`, `SDL_compat` and `smpeg` at evaluation through that dependency.
The latter three were confirmed by their evaluation diagnostics, not inferred
as independent package failures. This small explicit blocker list is not a
general dependency-failure classifier.

## Reading and operating a campaign

Read the frozen revision and selection first, then successful / failed /
incomplete / timed-out / unattempted admitted roots. Read exclusions separately;
they are outside the admitted denominator. An expected campaign is verified
only when every admitted root succeeds and no unexpected evaluation exclusion
is hidden. A running or budget-exhausted campaign is not verified. Cache
publication is a separate delivery state, not another kind of test success.

Start an expected campaign after a meaningful package/toolchain revision;
start exploration deliberately when looking for new coverage. Freeze committed
source and review the manifest before launch: `campaignctl submit world
--scope expected --rev REV` freezes it, and the service keeps it GC-rooted
and queues it beside the earlier campaigns ([the campaign
service](campaign-service.md)). Transient failures can get a fresh attempt
(`campaignctl retry`); recipe/toolchain changes need a new frozen revision.
Attempts never overwrite earlier evidence.

Keep publishers independent, on the same outputs feed and durable receipts.
Drain old publication before switching recordings or explicitly enqueue its
needed outputs; successful dependencies of failed roots are not discovered
independently. Check both publishers and the outputs feed after rollover.
CI requires cached outputs; rerun it after publication. Releases require
explicit authorization and the full default distribution cache gate, not just
foundation CI or a green expected campaign. See
[operational commands](port-campaign-operations.md) and
[cache semantics](binary-caches.md).

## Review and scope

Oracle's history review found three intentions conflated: the legacy broad
compatibility experiment, the bounded 82-landmark native observer, and later
distribution/cache delivery priority. The original native thread
T-01a0fd6b-16ab-7029-9ae2-f63ae4171e6b confirms bounded coverage and preservation
of observations; T-01a15ce7-1e2f-76ab-8c1e-fb4f3eacb8ac confirms distribution
leaders were delivery priority, not a broader support promise. The later
foundation-only ship decision must remain intact.

We adopt Oracle's explicit expected list, strict unexpected evaluation handling,
reasoned exclusions and unchanged runner/publisher lifecycle. We defer its
dashboard disclosure proposal: the existing scope/name and API exclusions can
carry this first small policy change without a runner deployment. The desired
next viewer improvement is a visible selection explanation and exclusion
disclosure, preserving old manifests. Also deferred: automatic promotion or
demotion, retry/resume queues, dependency-success publication, and historical
dashboard federation. None requires changing toolchain pins or cancellation
semantics here.
