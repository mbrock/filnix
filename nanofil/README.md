# nanofil

A C compiler written in Prolog, with a QBE-style IR, that emits x86-64
assembly in the Fil-C ABI. Its output links with clang-built Fil-C code
and has the same memory-safety checks, frames and garbage-collector
rooting. The goal is a small reference implementation of what Fil-C's
LLVM pass does, written so the rules can be read, tested and run backwards.

Status: milestone 0 (ground truth on the pinned toolchain). There is no
compiler code yet.

- [PLAN.md](PLAN.md): decisions, milestones and acceptance criteria.
- [docs/handoff.md](docs/handoff.md): the original research handoff,
  kept verbatim.
- [docs/abi-findings.md](docs/abi-findings.md): the ABI checked against
  filnix's Fil-C 0.686, with answers to the handoff's open questions.
- [probes/](probes/): C probes and a hand-written Fil-C ABI assembly link
  test. Run `nanofil/probes/run.sh [outdir]`.
