# How GNU Hello was proved never to panic: a chronicle

This page tells how the proof that GNU Hello never panics was built. It covers November 6 to November 18, 2026: the phases, the decisions, the problems, the models that did the work, and what surprised us. It is a short history, not a full record. The technical surprises in glibc itself are collected in [Proving GNU Hello over userland glibc](hello-glibc.md), and the plan behind it all is in [the formal campaign](formal.md).

The campaign ended with a theorem about the real program. Hello is linked with the userland glibc it actually uses, and the proof starts where the C library starts a process. From any allowed start state, no Fil-C check ever fails. The proof keeps five assumptions on purpose. File descriptors 1 and 2 are open, the environment selects the C locale, the CPU reports an end to its cache list, and the runtime is ready. Nothing else is assumed. A second theorem shows that the real image has such a start state when the runtime is the model's own interpreter. In Rocq the two theorems are `hello_never_panics` in [HelloStartNeverPanics.v](../rocq/glibc/hello/HelloStartNeverPanics.v) and `hello_interp_never_panics`, which landed at [c3d33bc2](https://github.com/mbrock/filnix/commit/c3d33bc2).

All times are UTC. Thread links go to the Amp threads that did the work.

## The idea (November 6 and 7)

The formal campaign did not begin with Hello. On November 6 mbrock wrote down a plan to make Fil-C programs faster by removing a check only where a machine-checked proof says it cannot fire. That plan, now [formal.md](formal.md), said explicitly that "the whole program never needs proving". The proof work started the same day in [the Campaign 1 thread](https://ampcode.com/threads/T-01a1b0b0-1f68-7215-86c9-677838e76829). That thread copied nanofil's IR and its interpreter into Rocq, and it checked the copy against the Prolog original on every test.

On November 7 mbrock corrected the framing. When Filip Pizlo says that a program panics, he means that a Fil-C check failed. A claim that a program never panics is therefore a theorem about one pinned program, and Fil-C as a whole cannot have it. Twelve minutes later mbrock wrote that it would be cool to do this "for even something like GNU Hello or some trivial program, maybe that uses libc", and he asked which lemmas we could already establish. The coordinator wrote that idea into formal.md as Campaign 7 ([8bc9749a](https://github.com/mbrock/filnix/commit/8bc9749a)). Hello was the natural first target, because the repository already built every one of its objects with nanofil and compared the result with filcc's build. A program with one call to `puts`, `hi.c`, would come first.

mbrock then answered five design questions, and he took the proposed default each time ([bfabc92](https://github.com/mbrock/filnix/commit/bfabc92)). The proof does not count running out of memory or overflowing the stack as a panic. It rules out undefined behaviour. It allows any well-formed input, and it trusts libc through contracts that native tests probe.

## Phase 1: the model, soundness and Iris (November 6 to 10)

The Campaign 1 thread built the foundation in four days. The core model agreed with the Prolog interpreter on every run it compared. The validator transcription agreed on about twenty thousand verdicts per mode. Its most valuable finds were bugs in the Prolog rather than in the Rocq: a module the validator accepted could end `unchecked` once a variadic snapshot was freed, which was a hole in the planned soundness theorem itself. The runtime became a `Module Type Runtime` of axioms, each with a native test, and soundness of checking, `valid_no_unchecked`, was proved on November 8 ([66f5e14](https://github.com/mbrock/filnix/commit/66f5e14)).

On November 9 a hand-rolled program logic and an Iris spike both proved a small list sum. The thread recommended Iris, reversing its earlier advice, and mbrock chose it. `hi.c` was proved through Iris that afternoon, and Hello became the target that evening. By November 10 every path through Hello's `main` was proved ([e427306](https://github.com/mbrock/filnix/commit/e427306)), but against contracts for libc and about 190 premises about an abstract world. An Oracle review pointed out that nobody had shown those premises could all hold at once.

## Phase 2: glibc inside the proof (November 11)

The next decision moved the trust boundary down. Instead of writing contracts for libc, the campaign would compile Fil-C's userland glibc to nanofil IR, link it with Hello, and prove glibc's own code. Contracts would remain only at the runtime's `zsys_*` system-call wrappers. mbrock approved the plan with "let's roll" at 02:34 on November 11, and [the campaign thread](https://ampcode.com/threads/T-01a1c874-b786-745e-a94b-3e56e5fa6937) ran it with Gemini 4 Carbon as lead. The plan had milestones M0 to M7, three to five worker lanes on disjoint files, and a limit of about 700 lines and 25 s of compile time per file.

The first day went fast. glibc uses atomic compare-and-swap, so one worker taught the model that instruction. Another wrote contracts for the runtime's system-call wrappers, each checked by a native probe. The rest proved the string, allocation, exit-handler and stream functions that Hello reaches. A bake-off pitted Opus 5.5, GPT-6.1 Sol and Gemini 4 Argon against the same `strcmp` proof; Opus was furthest ahead when it was checked, and the M3 lanes ran on Opus. Fable 5.2 did cold audits: of the `zsys` contracts, and of the locale-archive loader, where it found five unchecked bounds bugs that became glibc patches.

At about 16:30 the lead stopped, because its Gemini prepayment credits had run out. A GPT-6.1 Sol thread, [the recovery thread](https://ampcode.com/threads/T-01a1cb7e-097a-70a7-a4e2-3a1badd8447d), took over the same checkout and finished the walking skeleton at 22:06 ([45fdf11c](https://github.com/mbrock/filnix/commit/45fdf11c)). A small test program that prints through `puts` and an exit handler was now proved never to panic, with nothing left for its caller to supply. Hello's theorem still depended on 13 named debts. Both proofs covered a whole program over real glibc, but both began from a start state that the proof's authors had written by hand, called `hi_host_prepare`.

## Phase 3: M4 and the stall (November 12 to 16)

The fourth milestone, M4, covered narrow `printf`, the `error` function and `getopt_long`. Both Opus lanes stopped late on November 11 when the Anthropic credits ran out. On the morning of November 12 mbrock moved the proof workers to GPT-6 Astra, and he kept them there after the credits returned. From then on heavy work ran on OpenAI models, and Opus and Fable did short reviews or rescued stuck lanes.

Less than an hour later the first cyber-safety stop happened. The Astra getopt lane had written a small C test showing that glibc's `getopt` reads past the end of `argv` when a caller changes only `optind` between calls. OpenAI's safety check then stopped the thread as possible unauthorized security work. The Space approved an Opus replacement whose brief described the native runs plainly as differential tests, and that lane finished the proof.

The rest of the sprint spent most of its effort on timing. The 25 s rule was enforced by a solo watchdog, and the stacked module functors cost 11–17 s per instance before any proof work began, so files had to be split again and again. Flattening the functors helped a great deal (one getopt file went from 23 s to 3.3 s), but measurement noise was up to 2×, and the `Print Assumptions` audit of `hi_atexit_never_panics` at about 51 s was still counted as a failure. On November 16 mbrock asked for a clean stop and a reflection. The leads wrote that "most of the lead and worker time went to re-timing, split negotiations and clearance messages rather than proofs", and that "the Hello end goal" had made no progress that sprint.

## Phase 4: a fresh look (November 16)

mbrock asked [a fresh thread](https://ampcode.com/threads/T-01a1e5b1-285e-75f7-a0bf-08c5e483375a) for an outside review. He said he "had the spidey sense that … something about our assumptions and the way we were going about this was preventing us from getting further". The review found that the tree held eleven `hello_never_panics` variants with different premises and no single measure of progress. It also found that Hello's start-state premise required glibc's single-thread flag to be 1 while the loaded image held 0, so the headline theorem might say nothing about the real program.

Asked why the flag was 0, the thread traced the cause to one gap in the model. The model had no rule for `setjmp`, and glibc's startup calls it just before it calls `main`. The model therefore could not run the startup code, so the earlier work had started at `main` and assumed by hand everything that startup sets up. In real glibc the flag becomes 1 during that startup code. The thread proposed four changes. The model would get a rule for the first return of `setjmp`, and the proof would start where the real process starts, from the image's initial memory. The tree would keep one theorem, and CI would print how many premises it still had.

## Phase 5: from the real startup (November 16 to 18)

The last phase set out to prove Hello from the state that the real loader builds, rather than from a state written by hand. Its lead started at 19:11 on November 16, in [its own thread](https://ampcode.com/threads/T-01a1e5c5-ae53-7628-ba7a-3c9794e64301), with a team of Opus workers and Fable for reviews. Within an hour the model could run glibc's startup code up to the call of `main`, and Fable had judged the plan sound. Nobody could tell whether a change helped while several versions of the theorem coexisted, so the lead deleted the eight extra versions and kept one. A new script counted what that theorem still assumed, and CI printed the number on every push. It started at 178, and about 160 of those assumptions described the hand-made start state. That night mbrock also removed every timing rule.

On November 17 the proofs of glibc's startup came in. The largest piece of startup asks the CPU what it supports, and it runs about 4,850 checked instructions. One worker wrote a small checker that runs over those instructions for every possible CPU answer, and then it proved the checker correct. The checker found a real trap: if a CPU never ends its list of caches, a loop counter wraps around and an array read goes out of bounds. The proof of the startup code also showed that it marks the process single-threaded, which settled the question about the flag.

By 17:03 the small test program was proved from the real image, and the hand-made start state was deleted. Hello followed at 18:41 in commit [a69ebb04](https://github.com/mbrock/filnix/commit/a69ebb04).

That evening a worker checked whether the 18 remaining premises could all be true, and Fable reviewed the answer. Seven of them could not hold, or probably could not. For example, glibc's `setlocale` leaves its lock word at 1, while one premise demanded 0. The fixes landed the same evening.

Each library call that the theorem still assumed was a place where the proof trusted glibc instead of checking it. On November 18 the workers proved those calls. They print the greeting and its diagnostics, set the locale, and write wide characters, which every greeting does. By 16:22 the theorem assumed only the start state and the five kept assumptions. A theorem whose assumptions can never hold together proves nothing. An Astra worker therefore checked that these assumptions can hold at once, and it found that they do for the interpreter's runtime on the real image. mbrock chose to name that runtime in one place. The concrete theorem then landed at 18:03 in commit [c3d33bc2](https://github.com/mbrock/filnix/commit/c3d33bc2).

## Themes

### Opus and Astra

The campaign used every model family it had, and money decided as much as quality did. Gemini 4 Carbon led until its credits ran out; GPT-6.1 Sol led the recovery; Opus 5.5 won the bake-off and did M3; Astra did M4 after the Anthropic credits ran out; Fable 5.2 did cold audits throughout. In the last phase mbrock asked for Opus as the default, and then compared it with Astra on the same campaign. By the morning of November 18 Astra had made 19 landings without a fix-forward and had caught three soundness problems before proving anything. On a larger task, the wide `printf` contract, it finished in about 15 landings and found four more problems, while the Opus half of the wide stream had landed only predicates. The lead still recommended Opus as the default. At 14:14 mbrock answered "I think Astra", and the remaining work went to Astra workers with larger scopes.

### Cyber-safety stops

OpenAI's safety check stopped two Astra threads, and both times nothing in the work was an attack. The first, on November 12, came right after the getopt lane reproduced an out-of-bounds read with a native test. The second, at 10:08 on November 18, came while a worker was reading glibc's transliteration tables and raw image code. A stopped thread cannot be resumed, so its uncommitted work is at risk. After the second stop, workers pushed work in progress to a branch at each milestone, and restarts waited for mbrock's approval.

### The 25 s rule

The per-file limit came from the M0 plan, where it was meant to keep the edit loop fast. In practice it became the work. Leads negotiated splits, re-timed files under noise larger than the margins, and counted a 51 s query as a failed proof. The fresh-eyes review called the limit "the wrong target, not just badly measured". mbrock removed it on November 16 ([a2252e1](https://github.com/mbrock/filnix/commit/a2252e1)): the checks print the slowest files, and nobody splits a file to meet a number. The lead reintroduced the rule twice afterwards in its own worker briefs, and the parent thread corrected it both times. A rule that has been repeated in many briefs keeps coming back after it is removed.

### CI memory and the watchdog

Two kinds of CI failure came from the proofs' size rather than from their content. In the first, the glibc job was killed with exit 143 on four pushes in a row on November 18, because heavy files building in parallel ran the 16 GB runner out of memory. The fix that held was two parallel jobs, a 12 GB swap file and two cheaper proofs ([dc28959a](https://github.com/mbrock/filnix/commit/dc28959a)). In the second, from the setlocale landing onward, CI's 900 s per-file watchdog killed `HelloSetlocaleAll.v`, where one sentence took 211 s. Profiling showed that the cost was a `rewrite !big_sepL_cons`, not the `iFrame` everyone suspected, and proving the three setlocale loops once per symbolic category brought the file to 303 s ([dcae0141](https://github.com/mbrock/filnix/commit/dcae0141)). Earlier, in the recovery sprint, a missing `set -o pipefail` had let a failed build under `tee` report success.

### Contract bugs found before proving

A contract is an assumption until something proves it, and a wrong one can make a theorem vacuous. Several were caught only when someone tried to prove the code behind them: the `ioctl` request number off by 1024, a `FILE` field at byte 72 instead of 80, and a `vfprintf` precondition that allowed `%s` with an integer argument. In the last phase Astra caught them before writing proofs. Its finds included a premise X that could be chosen as `True`, a `_shortbuf` state one byte out of bounds, a runtime signature too weak to use, two holes in `file_wide`, a signed 32-bit padding test, missing allocation bounds on `hd_wprintf`, a rule that accepted a null `tm`, and a postcondition that let bit 30 of the stream flags be cleared.

### The premise counter

The counter, `nanofil/tests/hello_premises.py`, runs in the glibc CI job and prints one line per premise of `hello_never_panics`, tagged with the work that discharges it. It made progress visible for the first time. The count went from 178 on November 16 to 18 once the theorem started from the real image, and then down by about one per landing through November 18. It also needed honesty of its own. At one point it showed 17 while the true number was 18, and on the last afternoon it showed 5 because the script missed a private-state premise; the fix made it count every premise of the theorem. After the first audit it also marked premises not known to be satisfiable, so a low count could not hide a vacuous theorem.

### The five assumptions that stay

When only the deliberate assumptions were left, someone asked mbrock whether to prove the locale premise away too. He answered "nah not right now, keep the locale premise etc". Each of the five assumptions describes how the program is started or what machine it runs on. The program must start with file descriptors 1 and 2 open. Its environment must select the C locale, so the locale variables must be unset, empty, `C` or `POSIX`. The CPU must end its list of caches; a CPU that does not would need a change to glibc. The runtime must be ready for the image.

The audit raised one caveat. A runtime that is never ready would make the general theorem empty, and the concrete theorem for the interpreter's runtime answers that caveat.

### The malloc caveat

The malloc contract that the proof uses never returns null. When the runtime cannot allocate, the run ends as `out_of_memory`, and that ending is not a panic. The theorem therefore says nothing about a malloc that returns null, and this matters for real code. When `wprintf` first writes to a wide stream, glibc ignores a failed allocation, sizes the wide buffer at zero, and would panic on its first store. [hello-glibc.md](hello-glibc.md#the-theorem-assumes-malloc-never-returns-null) states this where it lists what the proof trusts ([22c4b70e](https://github.com/mbrock/filnix/commit/22c4b70e)).

## What we learned

- When the campaign proved real code, it found real bugs. Early on, its most valuable result was a list of defects rather than a theorem. The proofs found unchecked offsets in the locale-archive loader and a read past the end of the argument vector in getopt. They also found a memcmp that panics without optimization and a cache counter that wraps.
- A hand-made start state hides the work. The single-thread flag looked like a detail and turned out to be the sign that a whole layer, glibc's startup, was assumed rather than proved.
- One endpoint and one number change behaviour. With eleven theorem variants nobody could say whether a slice helped; with one counted theorem every landing either reduced the count or did not.
- Process can eat a campaign. Timing rules, clearance messages and long checkpoint logs cost more than the proofs did in the stalled sprint, and removing them was the fastest speed-up of the campaign.
- Statements need checking before proofs. The satisfiability audits and the contract reviews found more vacuity than any build did, because Rocq accepts a proof from false premises without complaint.
- The edit loop matters more than raw build speed. Workers moved from recompiling a file per try to a persistent Rocq session, described in the next section.

## Interactive proving with rq

For most of the campaign an agent saw its next proof goal by recompiling the whole file. That took a minute or more in the large startup and stream files. On November 17 mbrock asked the startup-world worker what was slowing it down, and the worker answered by writing rq. A minute later another commit made rq the default edit loop in nanofil/AGENTS.md. This section comes from [a separate review](https://ampcode.com/threads/T-01a1efda-4c3b-70e2-b0b1-dbf1fcf2c52f) of how the workers in the last phase used it.

### What it is

rq is about 160 lines in `nanofil/rocq/scripts/glibc-tools/rq/`. `server.py` keeps one `rocq repl` running behind a Unix socket. `start.sh FILE LINE` starts a server and loads the file up to that line, and `rq.py` sends it a chunk of tactics or replays a line range of a file. The server knows that a chunk has finished when a sentinel command writes a file. If the output contains the word "Error", the server rolls Rocq back to the state before the chunk.

### How agents used it

Every proof worker in the last phase used rq, some of them for a thousand chunks or more. A small try came back in 0.15 to 1 s, and a load took 7 to 17 s. It replaced recompiles of 30 to 95 s in the transliteration files, up to 600 s in the wide write loop, and up to 700 s in `HelloSetlocaleAll.v`. The tools divided the work cleanly. Agents used rq for tries and goals, `one.sh` with `-time` as the judge of `Qed` and as the profiler, and `affected.sh` before each push. No worker ran the full gate inside the loop.

Several habits worked well. Agents sent small chunks followed by `Show.`, and they returned to a known good state when a try failed. They read the IR in a live session with `Eval vm_compute`, drafted helper lemmas and Ltac as a `Goal … Qed.` before copying them into the file, and timed single tactics on a synthetic goal. One worker stopped a runaway tactic with SIGINT, and rq rolled back and kept the session.

### Where it hurt

The problems were the same across threads, and rq itself never changed after November 17 to fix them.

- A load that ends inside a sentence or a comment hangs forever. The sentinel joins the unfinished sentence and never runs, and the server waits for its file with no timeout. A C excerpt such as `(unsigned char *)` in a header comment caused one hang by closing the comment early.
- A load error does not roll back, because there is no earlier state to return to. One bad import produces dozens of follow-on errors, and `start.sh` prints only their tail, so the real error stays hidden in `/tmp/rq.load`.
- Rollback is all or nothing. A good prefix is lost with the bad sentence, including Ltac definitions from the same chunk. Workers learned not to send `Qed` in the same chunk as a step that might fail, and the lead put that rule into later briefs.
- Success in rq does not mean that `Qed` passes. A chunk can succeed while goals are shelved, a replay through `Admitted` looks clean, and a session can drift from the file on disk. `Print Assumptions` in rq lists imported lemmas as axioms, because the warmed objects are interfaces whose proofs are blanked out.
- The session goes stale after an edit, a rebase or a cache refresh, so workers restarted it after almost every edit. One worker started about 32 servers.
- An idle session holds 2 to 3.6 GB of memory beside the builds that `affected.sh` runs, and nothing accounts for it. Workers killed sessions by hand to avoid the OOM killer.
- Process handling is fragile. Killing the Python server can orphan a busy Rocq worker. `start.sh` always uses the same pid and log files, so a second session silently killed the first. `rq.py` always exits 0, so agents searched its output for `^Error:`.
- Goals are huge. Each one prints an environment 60 entries deep and memory byte by byte, and one replay printed 76,000 lines. Five threads wrote their own filters for this output. Three threads each built a scratch copy of their file with the other proofs admitted, because the full file loaded too slowly.

### How it could be better

The cheapest technical fixes come first. Each chunk should get a default timeout that sends SIGINT, which already rolls back cleanly. `start.sh` should refuse a line that ends inside a sentence, stop a load at its first error, and print that error with its line number. `rq.py` should return a nonzero exit code on error. A mode that runs sentence by sentence would keep the good prefix and report how far it got.

Two larger fixes would close the gaps that cost the most time. A `qed` command would report shelved and given-up goals and try `Qed` in a throwaway state, so that success in rq would mean the file compiles. A `reload` command would compare the file with the loaded text, roll back to the first changed sentence and replay from there, as Proof General does, instead of restarting after every edit. Sessions should also keep their files per socket, kill their whole process group, and exit after an idle period or above a memory cap. An `--admit-others` load would build the fast scratch copy that three threads wrote by hand. A different design would build on coq-lsp or petanque, which already split sentences and keep a state per sentence. The review proposed this itself; no thread tried it.

Agents also need rq to be easier to read. It should show the views that they kept building for themselves: the first error with its context, only the conclusion of a goal or the next IR instruction, and the names of the hypotheses. After every reply it should print a status line with the state number, the open and shelved goals, and whether it rolled back. The rules that agents learned the hard way belong in `rq.py --help` and in `glibc-tools/README.md`, which does not mention rq yet. A load should end on a complete sentence, and a chunk is all or nothing. Success in rq and rq's `Print Assumptions` are not final. An agent should restart the session after a cache refresh, a rebase or an edit to an import, and it should stop the session before a heavy build.
