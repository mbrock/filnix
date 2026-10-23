# nanofil

A C compiler written in Prolog, with a QBE-style IR, that emits x86-64
assembly in the Fil-C ABI. Its output links with clang-built Fil-C code
and has the same memory-safety checks, frames and garbage-collector
rooting. The goal is a small reference implementation of what Fil-C's
LLVM pass does, written so the rules can be read, tested and run backwards.

Status: milestone 1. There is a QBE-subset parser, printer and
validator, and a CLP(Z) interpreter differentially tested against real
qbe ([docs/m1.md](docs/m1.md)). No backend yet.

- [PLAN.md](PLAN.md): decisions, milestones and acceptance criteria.
- [docs/handoff.md](docs/handoff.md): the original research handoff,
  kept verbatim.
- [docs/abi-findings.md](docs/abi-findings.md): the ABI checked against
  filnix's Fil-C 0.686, with answers to the handoff's open questions.
- [docs/m1.md](docs/m1.md): the IR, its semantics, how it is tested, and
  the qbe and Trealla bugs that testing found.
- [probes/](probes/): C probes and a hand-written Fil-C ABI assembly link
  test. Run `nanofil/probes/run.sh [outdir]`.
