# How Iris works

Iris is a framework for proving programs correct, built as a library for the Rocq prover. Its logic is a higher-order concurrent separation logic: an assertion describes the resources a piece of code owns (a heap cell, a share of one, a role in a protocol), it may quantify over other assertions, and threads share assertions through invariants. A language joins Iris by giving its step relation, and one theorem, adequacy, turns a proof in the logic into a plain Rocq fact about every run. Iris comes from Derek Dreyer's group at MPI-SWS and Lars Birkedal's at Aarhus, with Ralf Jung and Robbert Krebbers as its main builders, and has been developed in the open since 2015 ([iris-project.org](https://iris-project.org/)).

This page tells where Iris comes from, what its logic can say, how it differs from other ways of verifying C, and how it is built in Rocq. Then it shows how nanofil uses it: the [[machine]] as an Iris language, resources keyed by object [[identity]], and a spike that proves a linked-list program never panics ([logic.md](logic.md) records the decision). Each idea links to its page in the [concept index](concepts/). The shaded notes go deeper, or say where nanofil meets the idea. Rocq is quoted as written, from Iris 4.5 and from nanofil's spikes in [rocq/spikes](https://github.com/mbrock/filnix/tree/main/nanofil/rocq/spikes).

## Hoare logic

In 1967 Robert Floyd attached assertions to the edges of flowcharts, and in 1969 Tony Hoare made that a logic of program text ([An Axiomatic Basis for Computer Programming](https://dl.acm.org/doi/10.1145/363235.363259)). Its judgment is the [[hoare-triple|Hoare triple]] {P} c {Q}: if P holds when c starts and c finishes, Q holds when it does. Each construct has a rule. Assignment substitutes into the postcondition, sequencing chains two triples, and a loop needs an invariant that each iteration keeps. The triple says nothing about a run that never finishes, and neither do Iris's: it is partial correctness.

Hoare logic handles variables and breaks on pointers. Its assignment rule substitutes for the variable assigned, but `c: *p = 1` may change `c: *q` when p and q alias, so every assertion about any cell must say whether it might be the one written. Proofs of pointer programs drowned in such side conditions, as Rod Burstall had already noticed in 1972.

> nanofil's first proofs of single programs are Floyd's method. Cycle.v attaches an assertion to each of 19 points of a loop ([cycle_never_panics]), and [never_panics_by_invariant] is the rule that checks them: every step from a point that holds its assertion lands at a point that holds its own.

## Separation logic

Between 1999 and 2002 John Reynolds, Peter O'Hearn, Samin Ishtiaq and Hongseok Yang fixed this by making an assertion describe only the part of the heap a command owns ([Reynolds, LICS 2002](https://www.cs.cmu.edu/~jcr/seplogic.pdf)). The assertion language came from O'Hearn and Pym's logic of bunched implications. Three connectives carry the idea of [[separation-logic|separation logic]]:

- `ℓ ↦ v`, points-to: cell ℓ holds v, and whoever holds the assertion owns the cell. It is not a fact about the whole heap; it is the permission to read and write one cell.
- `P ∗ Q`, separating conjunction: the heap splits into two disjoint parts, one where P holds and one where Q does. So `ℓ ↦ v ∗ ℓ' ↦ w` implies ℓ ≠ ℓ': the assertion itself rules out aliasing.
- `P -∗ Q`, the [[magic-wand|magic wand]]: owning it and P yields Q. It is a structure with a hole that P fills, as when part of a structure is lent out.

The payoff is the frame rule. Code proved correct on the cells it uses stays correct in any larger heap, and leaves the rest alone. In Iris it is a lemma about weakest preconditions, proved once ([weakestpre.v](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.5.0/iris/program_logic/weakestpre.v)):

```rocq
Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
```

So a specification names only its footprint. Reading a cell needs that cell and nothing else. In the triple notation for heap_lang, Iris's example language, where `! #ℓ` loads from location ℓ:

```rocq
Example load_spec ℓ v : ⊢ {{{ ℓ ↦ v }}} ! #ℓ {{{ RET v; ℓ ↦ v }}}.
```

Recursive data becomes a recursive predicate. The list from p holding xs is null when xs is empty, and otherwise a node owning its cells, separately from the list after it. Since ∗ keeps each node's cells apart from the rest, the predicate excludes cycles and sharing without saying so.

> The model of ∗ is plain set theory: an assertion is a predicate on heap fragments, and P ∗ Q holds of h when h is the disjoint union of an h1 where P holds and an h2 where Q does. nanofil's hand-rolled spike writes exactly that over footprints of identity-keyed pieces (`star` in [Sep.v](https://github.com/mbrock/filnix/blob/a8083f593eeb47a6e1e919a84f53bbe718e8594f/nanofil/rocq/spikes/Sep.v)). The frame rule is sound because every rule of the language leaves alone what it does not own.

## Concurrent separation logic

O'Hearn's [[concurrent-separation-logic|concurrent separation logic]] (CONCUR 2004, with a soundness proof by Stephen Brookes; the two shared the 2016 Gödel Prize) carried ownership across threads. Threads that own disjoint parts of the heap run in parallel without interfering. A lock protects a resource invariant, an assertion that the thread taking the lock receives and must restore before releasing it, so ownership moves with the lock.

Fine-grained concurrent code, which synchronizes through atomic instructions instead of locks, did not fit, and the next decade produced a logic per pattern. Fractional permissions shared cells for reading (Boyland 2003; Bornat, Calcagno, O'Hearn and Parkinson 2005). RGSep mixed in rely-guarantee (Vafeiadis and Parkinson 2007). Concurrent abstract predicates hid shared state behind protocols (Dinsdale-Young et al. 2010), and HOCAP, iCAP, CaReSL, TaDA, FCSL and GPS followed. Each had its own model and its own soundness proof; Matthew Parkinson named the situation "The next 700 separation logics" (2010).

## Iris

Iris was the answer to that zoo. Its first paper claimed that the zoo's mechanisms reduce to two: ghost state the user defines with a partial commutative monoid, and invariants. A new pattern is then a choice of monoid and an invariant, proved inside the logic, instead of a new logic. Later versions shrank the core further and filled its gaps:

- **1.0, 2015**: ghost state from monoids, invariants and a step-indexed model, with the rest derived. Jung, Swasey, Sieczkowski, Svendsen, Turon, Birkedal and Dreyer, [Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning](https://iris-project.org/pdfs/2015-popl-iris1-final.pdf), POPL.
- **2.0, 2016**: [[camera|cameras]], so that ghost state may hold propositions. Jung, Krebbers, Birkedal and Dreyer, [Higher-Order Ghost State](https://iris-project.org/pdfs/2016-icfp-iris2-final.pdf), ICFP.
- **3.0, 2017**: a small base logic, with invariants, [[update-modality|fancy updates]] and weakest preconditions defined in it. Krebbers, Jung, Bizjak, Jourdan, Dreyer and Birkedal, [The Essence of Higher-Order Concurrent Separation Logic](https://iris-project.org/pdfs/2017-esop-iris3-final.pdf), ESOP.
- **3.1, 2018**: the whole construction in one account, the reference to read. Jung, Krebbers, Jourdan, Bizjak, Birkedal and Dreyer, [Iris from the Ground Up](https://www.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf), JFP.
- **4.0, 2022**: later credits, an ownable right to remove a [[later-modality|later]]. Spies, Gäher, Tassarotti, Jung, Krebbers, Birkedal and Dreyer, [Later Credits](https://plv.mpi-sws.org/later-credits/paper-later-credits.pdf), ICFP.

Releases continued, 4.5 in March 2026 for Rocq 9.0 to 9.2, the one nanofil's pinned nixpkgs ships ([changelog](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/CHANGELOG.md)). Beside the logic came the [[iris-proof-mode|Iris Proof Mode]] ([Krebbers, Timany, Birkedal, POPL 2017](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf); generalized as [MoSeL](https://iris-project.org/pdfs/2018-icfp-mosel-final.pdf), ICFP 2018), which made proofs in it practical. Uses followed: [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf) proved that Rust standard libraries built on unsafe code are safe to use (Jung, Jourdan, Krebbers, Dreyer, POPL 2018), and [RefinedC](https://plv.mpi-sws.org/refinedc/paper.pdf), [Cerise](https://iris-project.org/pdfs/2023-jacm-cerise.pdf), Perennial's crash-safe storage and Aneris's distributed systems are all Iris instances. VST, the older C logic, was itself [rebuilt on Iris](https://iris-project.org/pdfs/2024-popl-vst-on-iris.pdf) (POPL 2024).

## What kind of logic it is

### Propositions are resources

An Iris proposition has type `iProp Σ` and describes resources: it holds of some and not of others, and ∗ splits them. Most propositions cannot be duplicated: from `ℓ ↦ v` there is no way to get two. The logic is affine, so a resource may be thrown away but never copied. Some propositions are knowledge rather than ownership, and those are [[persistent-proposition|persistent]]: `□ P` holds when P does without owning anything exclusive, and `□ P` gives `□ P ∗ □ P`. A Rocq fact φ embeds as `⌜φ⌝`, which is persistent.

Higher-order means a proposition may quantify over propositions and predicates, as in `∀ Φ : val → iProp Σ`. That is how a specification abstracts over whatever its caller keeps, how a function that takes a callback states the callback's specification, and how a container is generic in what its elements own.

### Ghost state

[[ghost-state|Ghost state]] exists only in the proof. It records what the program's memory does not: who holds which share of a cell, a counter's history, the phase of a protocol each thread is in. `own γ a` says the proof owns the piece a of the ghost location γ, where a belongs to a resource algebra the user picks, a [[camera]]: a set with a partial composition ⋅ and a validity ✓. Owning two pieces is owning their composition, everything owned together is valid, and allocating and changing ghost state are updates ([own.v](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.5.0/iris/base_logic/lib/own.v)):

```rocq
Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ∗ own γ a2.
Lemma own_valid γ a : own γ a ⊢ ✓ a.
Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
Lemma own_update γ a a' : a ~~> a' → own γ a ⊢ |==> own γ a'.
```

An update `a ~~> a'` must preserve frames: for any piece c another party may own, if a ⋅ c was valid, a' ⋅ c is. So changing your own ghost state never invalidates anyone else's. Choosing a camera is choosing a protocol. Excl gives exclusive ownership, fractions in (0, 1] give shares, Agree gives agreement on a value that never changes, and the authoritative camera gives one party ● a, the whole, and others ◯ b, fragments that must be included in it. Iris's heap is the last: the state interpretation owns ● of a map that equals the real heap, and `ℓ ↦ v` is ◯ of the one-entry map (gen_heap, on ghost_map).

> Iris 1.0's resources were monoids. Iris 2.0 made them cameras, which carry a step-indexed equality, so that ghost state may contain propositions. That is what lets an invariant be defined as ghost state instead of being a primitive, and it is why the model needs the later modality below.

### Invariants

An [[iris-invariant|Iris invariant]] `inv N P` says that P holds, of resources no one owns, between every two steps. It is persistent, so every thread may know it. A thread opens it for one atomic step, takes P out, and puts P back before the step ends ([invariants.v](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.5.0/iris/base_logic/lib/invariants.v)):

```rocq
Lemma inv_alloc N E P : ▷ P ={E}=∗ inv N P.
Lemma inv_acc E N P :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
```

The mask E is the set of invariants that may be opened. Opening N removes it from the mask, so it cannot be opened twice at once, which would duplicate P. CSL's lock invariants, RGSep's shared regions and CAP's protocols are each an invariant over some ghost state. Since Iris 3, `inv` is not a primitive but a persistent proposition defined in the logic, the ability to open:

```rocq
Local Definition inv_def `{!invGS_gen hlc Σ} (N : namespace) (P : iProp Σ) : iProp Σ :=
  □ ∀ E, ⌜↑N ⊆ E⌝ → |={E,E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ True).
```

> An invariant shared between threads is the piece nanofil's planned logic does not need yet. Its model has one thread, and the only other party that touches memory is the [[runtime]] at a [[poll|safepoint]], which Runtime.v bounds by an axiom ([collector_live]: no region changes there) rather than by an invariant.

### The later modality

Invariants, and ghost state that holds propositions, make the model circular: a proposition is a predicate over resources, and a resource may contain a proposition. Iris breaks the circle with step-indexing ([[later-modality|later modality]]). Each proposition holds or fails at each step index n, a budget of steps still to run, and `▷ P`, "later P", holds at n + 1 when P holds at n. A proposition that was stored, in an invariant or in ghost state, comes back only under a ▷, which is why `inv_acc` gives `▷ P`. The program takes a step while an invariant is open, and each step lets the proof remove one ▷.

The same indices give recursion for nothing. Löb induction proves P while assuming P one step later ([derived_laws_later.v](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.5.0/iris/bi/derived_laws_later.v)):

```rocq
Lemma löb `{!BiLöb PROP} P : (▷ P → P) ⊢ P.
```

A loop is proved by assuming the loop safe one step later and showing that its body takes a step before it uses the assumption. The weakest precondition is itself defined that way.

> Step-indexing comes from Appel and McAllester's indexed model of recursive types (TOPLAS 2001) and the "very modal model" of Appel, Melliès, Richards and Vouillon (POPL 2007), whose ▷ is Nakano's modality (LICS 2000). The cost is that a stored P comes back only as `▷ P`, awkward when no program step is at hand. Later credits (Iris 4.0) make the right to remove a ▷ a resource £ n, earned one per step and spent anywhere. [Transfinite Iris](https://iris-project.org/pdfs/2021-pldi-transfinite-iris-final.pdf) (PLDI 2021) indexes by ordinals so that termination and liveness proofs work.

### Update modalities

Changing ghost state is not a program step, so it has its own connective, an [[update-modality|update modality]]. The basic update `|==> P` says P holds once ghost state is changed by frame-preserving updates; `own_alloc` and `own_update` above produce one. The fancy update `|={E1,E2}=> P` may also open and close invariants: it starts with the invariants in E1 closed and ends with those in E2 closed, and `inv_acc` is one. `P ={E}=∗ Q` abbreviates `P -∗ |={E}=> Q`.

### Weakest preconditions

The [[weakest-precondition|weakest precondition]] `WP e {{ v, Φ v }}` says that running e is safe and that, if it ends in a value v, Φ v holds. Iris defines it once for every language, by guarded recursion, as the fixpoint of this function (weakestpre.v):

```rocq
Definition wp_pre `{!irisGS_gen hlc Λ Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κ κs nt,
     state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
         £ (S (num_laters_per_step ns))
         ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
         state_interp σ2 (S ns) κs (length efs + nt) ∗
         wp E e2 Φ ∗
         [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post
  end%I.
```

Read it as a game against the machine. If e1 is a value, update to Φ v. Otherwise the machine names a state σ1 and hands over its [[state-interpretation|state interpretation]] (for heap_lang, the authoritative heap). The proof must show that e1 can step, when the stuckness s is NotStuck, and, for every step e1 can take, after a later, return the new state's interpretation, the weakest precondition of what e1 became, and one for each thread it forked. The proof never sees the state itself. It owns fragments such as `ℓ ↦ v` and learns facts about σ1 by combining them with `state_interp`.

A Hoare triple `{{{ P }}} e {{{ RET v; Q }}}` is notation for `□ ∀ Φ, P -∗ ▷ (Q -∗ Φ v) -∗ WP e {{ Φ }}`. For any continuation Φ, owning P and the promise that Q gives Φ, e is safe and ends in Φ. Specifications in this continuation style compose: the caller's Φ carries everything the caller keeps.

### Adequacy

A proof in the logic is worth something only if it says something about runs. [[adequacy|Adequacy]] says it, once per language, in Rocq's own logic ([adequacy.v](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.5.0/iris/program_logic/adequacy.v)):

```rocq
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.
```

`wp_adequacy` proves `adequate` from a proof, after allocating any invariants and ghost state, of the initial state's interpretation and a WP for e1. Every thread of every reachable configuration is then a value or can step, and a main thread that ends satisfies the postcondition. The proof unfolds the WP along the run, one step and one ▷ at a time, and ends with the base logic's soundness, which turns `⊢ ▷^n ⌜φ⌝` into φ.

## What you can say with it

- **Ownership and framing.** A specification mentions only what the code touches; the frame rule carries the rest. A function that borrows a list and gives it back says so with the same `lst p xs` before and after.
- **Sharing.** A fraction splits `ℓ ↦ v` into read-only shares `ℓ ↦{q} v`, and a cell that never changes again becomes the persistent `ℓ ↦□ v`, which anyone may copy.
- **Protocols.** A camera states the possible states and transitions; an invariant ties them to real memory. A monotone counter, a one-shot flag, a lock and a reference count are a few lines each.
- **Higher-order specifications.** A function that takes a closure quantifies over the closure's specification, and a structure that lends out a part owns `P ∗ (P -∗ whole)`.
- **Logical atomicity.** An operation that takes many steps may be specified as if it took effect at one point, its linearization point (atomic updates, after TaDA). [Prophecy variables](https://plv.mpi-sws.org/prophecies/paper.pdf) (POPL 2020) let a proof use what the program will do later.
- **Logical relations and refinement.** iProp is a good language for semantic types: RustBelt interprets each Rust type as an Iris predicate, and ReLoC and Simuliris prove that one program refines another.
- **Other kinds of program.** Crash recovery (Perennial), distributed systems (Aneris), probabilistic programs (Clutch) and capability machines (Cerise) instantiate the same framework.

What it does not give for free: a plain WP is partial correctness, so termination needs the total weakest precondition or an argument outside the logic; liveness is hard; and Iris is a framework, not a push-button verifier. Automation comes from libraries on top, such as RefinedC's Lithium and Diaframe, and each new language costs an instantiation and its rules.

## How it differs

Each approach makes a different choice of what is trusted and what is proved about which program.

- **A hand-rolled logic**: assertions as predicates on heaps, with a star and its frame lemmas written for one language, everything proved by hand in Rocq. [Sep.v](https://github.com/mbrock/filnix/blob/a8083f593eeb47a6e1e919a84f53bbe718e8594f/nanofil/rocq/spikes/Sep.v) is one; its adequacy is [never_panics_by_invariant], but its framing is manual.
- **VST**: Andrew Appel's Verifiable C, a higher-order impredicative separation logic for CompCert's Clight with its own step-indexed model, proved sound in Rocq against CompCert's semantics, so its proofs reach the assembly; rebuilt on Iris in 2024. It is a logic for C with C's memory model; nanofil proves programs in its own IR, whose memory is Fil-C's.
- **CompCert**: Xavier Leroy's verified C compiler, which proves in Rocq that the assembly simulates the source. It proves a translation, not programs; nanofil proves its [[validator]] sound instead ([valid_no_unchecked]) and checks its passes by [[translation-validation|translation validation]].
- **RefinedC**: refinement types for C built on Iris, with Lithium searching for the typing proof. It is the ownership-types rung of logic.md's ladder: its typing derivations are Iris proofs, so they need no soundness proof of their own.
- **Cerise**: Iris on a CHERI-like capability machine that runs untrusted code. It is the nearest prior art: capabilities and their bounds as Iris resources.
- **VeriFast, Viper, Verus**: separation logic, or implicit dynamic frames, decided by symbolic execution and an SMT solver. Fast and practical, but the verifier is trusted, not proved.

## How it is built in Rocq

Iris is a stack of libraries, each built only on the interface of the one below:

```diagram
 algebra       OFEs; cameras: excl, frac, agree, auth, gmap
    │  uPred: predicates on step index and resource
    ▼
 base logic    iProp Σ with ∗, -∗, ▷, □, own, |==>
    │  bi: the interface of a separation logic
    ▼
 proof mode    iIntros, iDestruct, iFrame, iMod, iLöb
    │  base_logic/lib: defined inside the logic
    ▼
 library       invariants, fancy updates, gen_heap
    │  program_logic: for any language Λ
    ▼
 WP, adequacy  wp_pre, lifting lemmas, wp_adequacy
    │  an instance
    ▼
 heap_lang, or nanofil's machine
```

### The model

A proposition is a predicate on a step index and a resource, closed under taking fewer steps and owning more ([upred.v](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.5.0/iris/base_logic/upred.v)):

```rocq
Record uPred (M : ucmra) : Type := UPred {
  uPred_holds : nat → M → Prop;

  uPred_mono n1 n2 x1 x2 :
    uPred_holds n1 x1 → x1 ≼{n2} x2 → n2 ≤ n1 → uPred_holds n2 x2
}.
```

The connectives are definitions on it. ∗ splits the resource, up to equality at the current index, and ▷ looks one index down:

```rocq
Local Program Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Local Program Definition uPred_later_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
```

`iProp Σ` is `uPred (iResUR Σ)`. Σ lists the camera functors a proof uses, and its resources map each to a finite map from ghost names γ to camera elements. A camera in Σ may mention `iProp Σ` itself, as an invariant's ghost state mentions P, so iProp is the solution of a recursive domain equation, which Iris constructs once, in the style of America and Rutten, over ordered families of equivalences (OFEs). Step-indexing is what makes the solution exist: each recursive occurrence sits under a ▷.

The laws are proved in the model once and packaged as the `bi` interface, for bunched implications. Everything above it, the proof mode included, uses only the interface, so the same proof mode serves other separation logics; that is MoSeL.

> Soundness is where the model meets Rocq. `pure_soundness` says that `⊢ ⌜φ⌝` gives φ, and `laterN_soundness` that `⊢ ▷^n P` gives `⊢ P` ([sbi.v](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.5.0/iris/bi/sbi.v)). Adequacy unfolds the WP n steps along a run of n steps, which leaves a pure fact (the configuration is not stuck) under n laters and updates; these lemmas, and their versions for updates, make it a plain Rocq fact.

### The proof mode

Proving `P ∗ Q ⊢ Q ∗ P` with Rocq's own tactics means rewriting with associativity and commutativity lemmas, and real goals have a dozen conjuncts. The [[iris-proof-mode|Iris Proof Mode]] gives Iris goals their own context. Hypotheses have string names and live in two zones: persistent ones, which can be used any number of times, and spatial ones, which a tactic consumes. Above the double line is Rocq's own context; below it, persistent hypotheses (none here) would come first, then the spatial ones, then the goal under `∗`. A goal of nanofil's spike, in the middle of the proof below, as Rocq prints it, without the section's variables and with shorter rules (the spike's page draws every state of the proof):

```text
m : mem
s : R.state
ps : list (piece * pval)
h : gmap piece pval
Ha : agrees (m, s).1 h
Hd : live_disjoint (m, s).1
Hr : R.ready (m, s).2 (m, s).1
=============================
"Hh" : gen_heap_interp h
"Hps" : pts ps
-----------------------------∗
⌜owned_facts ps m⌝
```

`iIntros "Hσ Hps"` introduces wands, `iDestruct "Hσ" as (h) "[Hh %Hσ]"` opens an existential and a ∗ and moves a pure fact into Rocq's context, `iFrame` cancels hypotheses against the goal, `iSplitL "H"` gives H to the left conjunct, `iMod` runs an update, `iNext` removes a later, and `iLöb as "IH"` starts Löb induction. The tactics are driven by typeclasses (`IntoSep`, `Frame`, `ElimModal`), so a new connective joins them with instances. The whole proof of that goal, [pts_facts]:

```rocq
Lemma pts_facts m s ps : heap_interp (m, s) -∗ pts ps -∗ ⌜owned_facts ps m⌝.
Proof.
  iIntros "Hσ Hps". iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr).
  iDestruct (pts_lookup with "Hh Hps") as %Hl. iPureIntro.
  split; [|split; [exact Hd | exact (R.address_space _ _ Hr)]].
  apply all_agree_intro. intros l v Hin. apply Ha, Hl, Hin.
Qed.
```

### A language

A language is a structure: expressions, values, states, observations, and a step relation that may fork threads ([language.v](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.5.0/iris/program_logic/language.v)):

```rocq
Structure language := Language {
  expr : Type;
  val : Type;
  state : Type;
  observation : Type;
  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → list observation → expr → state → list expr → Prop;
  language_mixin : LanguageMixin of_val to_val prim_step
}.
```

The mixin asks three laws: a value round-trips through `of_val` and `to_val`, and a value takes no step. With that, WP and adequacy exist for the language. The user then picks a state interpretation (an `irisGS_gen` instance) and proves a rule per primitive operation from Iris's lifting lemmas, such as `wp_lift_step`; heap_lang's `wp_load`, `wp_store` and `wp_alloc` are proved that way. A language whose expressions have evaluation contexts (`ectx_language`) also gets `wp_bind`, which proves a subexpression first and the rest under its result.

## nanofil's machine in Iris

nanofil's campaign is now a property of whole programs ([formal.md](formal.md)): [never_panics] says that no run of a module, from any admissible input, with any [[fuel]] and anything the runtime does, reaches a state that [fails]. Campaign 3 already proves that a validated module never makes an [[unchecked]] access; never_panics asks that no check fails either. A check's success depends on facts about the heap (this field points to a live 16-byte object), which belong to whoever owns the object, so the logic is a separation logic. The two spikes prove the same theorem twice, once in a hand-rolled logic and once in Iris; [logic.md](logic.md) compares them and recommends Iris. This section reads the Iris one, the first instantiation of Iris for nanofil. Its files were removed in November 2026 and are linked at their last version; the program logic grew from them in [Language.v](../rocq/theories/logic/Language.v), [Heap.v](../rocq/theories/logic/Heap.v) and [Logic.v](../rocq/theories/logic/Logic.v), and [ListSumLogic.v](../rocq/spikes/ListSumLogic.v) proves the same program there.

### The machine as a language

[IrisLang.v](https://github.com/mbrock/filnix/blob/177d06baaf08b8d144af534c4c73ca7bcdffcf37/nanofil/rocq/spikes/IrisLang.v) wraps the machine. An expression is a configuration without its memory, or the [[outcome]] a run ended with; the Iris state is the memory with the runtime's state:

```rocq
Inductive expr : Type :=
| EConf (fr : frame) (callers : list (frame * pending)) (fuel : Z)
| EEnd (o : outcome).

Definition nstate : Type := (mem * R.state)%type.
```

A primitive step is a machine step from a configuration that does not fail, a refused allocation, or an ending that is not a failure:

```rocq
Inductive prim_step (ge : genv) : expr -> nstate -> list unit -> expr -> nstate -> list expr -> Prop :=
| ps_machine fr callers fuel m s c' s' :
    ~ fails ge (mkConfig fr callers m fuel) ->
    RM.mstep ge (mkConfig fr callers m fuel, s) (c', s') ->
    prim_step ge (EConf fr callers fuel) (m, s) [] (conf_expr c') (c_mem c', s') []
| ps_refused fr callers fuel m s q k :
    Semantics.step ge (mkConfig fr callers m fuel) = Fresh q k ->
    (0 <= req_extent q)%Z ->
    R.alloc s q = None ->
    prim_step ge (EConf fr callers fuel) (m, s) [] (EEnd (Trap OutOfMemory)) (m, s) []
| ps_done fr callers fuel m s o :
    Semantics.step ge (mkConfig fr callers m fuel) = Done o ->
    ~ failure o ->
    prim_step ge (EConf fr callers fuel) (m, s) [] (EEnd o) (m, s) [].
```

This is the whole trick. A panic, a stuck step and a negative allocation are each a configuration with no primitive step, so in Iris's terms it is stuck ([fails_not_reducible]). Running out of fuel, a refusal and a normal return end the run in a value. A [[poll|safepoint]] is an [mstep] that leaves the expression as it was and changes only the state. Nothing forks, and observations are unused.

### Adequacy is never_panics

A WP with stuckness NotStuck demands that every reachable expression be a value or reducible. In this language that is exactly that no reachable configuration fails. So Iris's adequacy, with a bridge from the machine's reachability to Iris's ([adequate_no_fails]), proves Panics.v's statement itself, [wp_never_panics]:

```rocq
Theorem wp_never_panics (hlc : has_lc) Σ `{!invGpreS Σ} md entry (input : list word -> Prop) globals m f :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) entry = Some (Defined f) ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\
     (R.ready R.start m -> forall (fuel : Z) (Hinv : invGS_gen hlc Σ),
        ⊢ |={⊤}=> ∃ stateI : nstate -> iProp Σ,
            let _ : irisGS_gen hlc (nanofil_lang (P.program_genv md globals)) Σ :=
              IrisG Hinv (λ σ _ _ _, stateI σ) (λ _, True%I) (λ _, 0%nat)
                    (λ _ _ _ _, fupd_intro _ _) in
            stateI (m, R.start) ∗
            WP (EConf fr [] fuel : language.expr (nanofil_lang (P.program_genv md globals)))
              @ NotStuck; ⊤ {{ _, True }})) ->
  P.never_panics md entry input.
```

The postcondition is `True`: never_panics is a safety property, so what a run returns does not matter, only that every step it takes is safe. The fuel is universally quantified and [OutOfFuel] is a value, so the WP needs no termination argument. The theorem took 174 lines and an hour. The hard part of an adequacy proof is the logic's model, and Iris has proved that once for every language.

### Resources keyed by identity

What can a proof own in Fil-C's memory? [Pieces.v](../rocq/theories/logic/Pieces.v), shared by both spikes and kept by the program logic, answers: an object's life, one byte, or one [[aux]] slot, each named by the object's [[identity]] and an offset:

```rocq
Inductive piece : Type :=
| PLive (b : Z)
| PByte (b o : Z)
| PAux (b o : Z).
```

Keying by identity is forced, not chosen. In the model a new object may cover addresses a freed object once had ([fresh]), so an address may belong to two objects in turn, but an identity never does ([free_keeps_ids]). An assertion about address a would be about whichever object is there; an assertion about identity b stays about one object for its whole life, and after it.

[IrisHeap.v](https://github.com/mbrock/filnix/blob/177d06baaf08b8d144af534c4c73ca7bcdffcf37/nanofil/rocq/spikes/IrisHeap.v) gives each piece a value, puts the pieces in Iris's gen_heap, and defines the state interpretation: the authoritative ghost heap agrees with the memory, live objects do not overlap, and the runtime is [[ready]]. [pts] owns a list of pieces with their values:

```rocq
Inductive pval : Type := VLive (reg : region) | VByte (v : Z) | VAux (c : cap).

Definition heap_interp (σ : nstate) : iProp Σ :=
  ∃ h : gmap piece pval, gen_heap_interp h ∗ ⌜agrees σ.1 h /\ live_disjoint σ.1 /\ R.ready σ.2 σ.1⌝.

Definition pts (ps : list (piece * pval)) : iProp Σ := [∗ list] lv ∈ ps, pointsto (fst lv) (DfracOwn 1) (snd lv).
```

A [[check]] splits along these pieces. Its bounds test is arithmetic on the object's extent and the pointer's offset, and its free-flag test needs the object still live. logic.md's plan makes those two halves two resources. The [[meta|meta fact]] `meta b n k` (b was allocated with n bytes, of kind k) is persistent, because nothing after an allocation changes what was allocated; it would be a ghost_map element `b ↪□ (n, k)`, which anyone may copy. The [[live|live token]] `live b` is exclusive, or split into fractions for readers, and free consumes it, so only the owner can free. Cells are points-to pieces, as above. The spike needed only `live`: its PLive piece carries the region, and the bounds come from there.

> Raw accesses need no rule. Campaign 3's [valid_no_unchecked] already proves that a validated module's every raw load and store is covered by a check that passed, so the logic needs rules only where a check could fail, and value rules for what a load returns. The run starting [[ready]] and the core machine's stop at external calls are its hypotheses; Campaign 4's labelled machine removes the last. It took [[spares]] as a hypothesis too, until every runtime was shown to meet it, since the collector changes no region at a safepoint ([collector_live]).

### Safepoints, by Löb

A safepoint is where the runtime acts, and Runtime.v's axiom for it is the collector's alone, [collector_live]: no region changes at a safepoint, so no safepoint frees a live object. The spikes once took that as a premise, [keeps_live], as Buffer.v did; with [collector_live] it is a lemma of Pieces.v for every runtime, and no rule or theorem takes it. A safepoint keeps every region and byte, and rewrites only aux slots that hold a dead object's capability ([safepoint_shape], from [collector_live], [non_moving] and [aux_round_trip]), so it keeps [heap_interp] with the same ghost heap.

Every rule of the spike comes from one lifting lemma, [wpc_lift], and that lemma deals with safepoints once:

```rocq
Lemma wpc_lift (Q : iProp Σ) fr callers fuel :
  (forall m s, heap_interp (m, s) -∗ Q -∗ ⌜~ fails ge (mkConfig fr callers m fuel)⌝) ->
  (forall m s, heap_interp (m, s) -∗ Q -∗
     ▷ ∀ e2 σ2, ⌜nosp_step ge (mkConfig fr callers m fuel) s e2 σ2⌝ ==∗ heap_interp σ2 ∗ wpc e2) ->
  Q -∗ wpc (EConf fr callers fuel).
```

Given Q, the configuration is safe if Q and the state interpretation show it does not fail, and if after every step that is not a safepoint ([nosp_step]) they give back the state interpretation and safety of what follows. The safepoint case is missing from the premises because the proof closes it with `iLöb`: a safepoint steps from `EConf fr callers fuel` to itself, so what is to be proved after it is the lemma's own conclusion, one step later, which Löb induction assumes. No program proof mentions safepoints again. The hand-rolled spike, without ▷, needs each function's assertions to survive a safepoint and a lemma per function to say so. Fuel cannot replace Löb here, because a safepoint spends no fuel.

### A list, summed

The program is [listsum.c](../rocq/spikes/listsum.c), compiled by nanofil:

```c
struct node { struct node *next; long v; };

__attribute__((noinline)) long sum(struct node *p) {
  long s = 0;
  while (p) {
    s += p->v;
    p = p->next;
  }
  return s;
}

long listsum(int n) {
  struct node *h = 0;
  for (int i = 0; i < n; i++) {
    struct node *x = __builtin_alloca(sizeof *x);
    x->next = h;
    x->v = i;
    h = x;
  }
  return sum(h);
}
```

In checked IR, `sum` checks each node's value field, half-checks and loads the next pointer with its capability from the aux, and polls on the loop's back edge; `listsum` allocates each node on the collected heap and stores through checked pointers. A node owns its life as a 16-byte heap object, the aux slot of its next pointer, and the bytes of both fields; the list is a recursive predicate, with the pointer's own capability and alignment as pure facts ([IrisListSum.v](https://github.com/mbrock/filnix/blob/177d06baaf08b8d144af534c4c73ca7bcdffcf37/nanofil/rocq/spikes/IrisListSum.v)):

```rocq
Definition node_ps (b : Z) (nx : ptr) (x : Z) : list (piece * pval) :=
  [(PLive b, VLive (mkRegion b (b + 16) Heap Live))] ++ [(PAux b 0, VAux (ptr_cap nx))] ++
  cell b 0 (ptr_addr nx) ++ cell b 8 x.

Fixpoint lst (p : ptr) (xs : list Z) : iProp Σ :=
  match xs with
  | [] => ⌜p = null⌝
  | x :: xs' => ∃ b nx, ⌜p = mkPtr b (Obj b) /\ 0 < b /\ b + 16 <= 2 ^ 48 /\ b mod 16 = 0⌝ ∗
                pts (node_ps b nx x) ∗ lst nx xs'
  end%I.
```

`sum`'s specification, [sum_spec], is in continuation style. The machine keeps the callers stack inside the expression, so there is no evaluation context to bind; instead the caller's resumption, with any result and any fuel, is a resource the callee carries to its return:

```rocq
Local Notation cont cf d callers :=
  (∀ y fuel', wpc lge (EConf (mkFrame (fr_fn cf) (put d (WInt y) (fr_env cf)) (fr_locals cf)
                                       (fr_doomed cf) (fr_at cf)) callers fuel'))%I.

Lemma sum_spec cf d callers p xs fuel :
  ⊢ lst p xs -∗ cont cf d callers -∗
    wpc lge (EConf (mkFrame (ls_fn "sum") [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None))
                   ((cf, mkPending (CResult d L) None) :: callers) fuel).
```

The frame is free: whatever the caller owns besides the list rides inside `cont`. Each loop is a Löb induction at the point after its head's phis, and each step is one rule application with the step computed, as in Symbolic.v. The theorem is then adequacy ([heap_never_panics]) applied to `listsum`'s specification ([listsum_spec]):

```rocq
Theorem listsum_never_panics :
  P.never_panics ls_module (TAtom "listsum") (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  apply (heap_never_panics lsΣ ls_module (TAtom "listsum") _ ls_globals ls_mem (ls_fn "listsum")).
  - exact ls_initial.
  - exact (ls_find_listsum R.free).
  - intros b1 r1 b2 r2 [E _]. vm_compute in E. discriminate E.
  - intros xs (n & rest & ->). eexists. split; [apply listsum_call_frame|].
    intros fuel HinvG HheapG. apply listsum_spec.
Qed.
```

Planting a bug shows what the specification carries: a node without its [PLive] piece makes [lst_head] unable to show the next node is live, only that it was allocated, and `sum`'s checks of it cannot be proved to pass.

### Against the hand-rolled logic

The hand-rolled spike states assertions as predicates on a footprint of pieces and the memory, with ∗ written out:

```rocq
Definition star (P Q : hprop) : hprop :=
  fun S m => exists S1 S2,
    (forall p, S p <-> S1 p \/ S2 p) /\ (forall p, ~ (S1 p /\ S2 p)) /\ P S1 m /\ Q S2 m.
```

It needs no new adequacy, since an invariant of configurations built from its assertions goes straight into [never_panics_by_invariant]. Everything Iris's proof mode does, it does by lemma: `emp ∗ P` is P only up to "the same pieces", four-way stars are reassociated by explicit chains, and walked nodes are dropped by [lst_cons_drop]. The two spikes are the same size and prove the same theorem:

| | Hand-rolled | Iris |
| --- | --- | --- |
| Adequacy | none new | 174 lines, 2 s |
| Generic logic | 932 lines, 3 s | 786 lines, 7 s |
| The program | 626 lines, 29 s | 488 lines, 59 s |
| Safepoints | a stability lemma per function | once, by Löb |
| Loops | assertions at points, as Cycle.v | Löb at the loop head |

In both, most of the program proof's time goes to computing the machine's step on abstract states, which no logic removes. What separates them is where the next proofs spend effort, which is why logic.md recommends Iris: framing, safepoints and the wand that Hello's quotearg needs (`string ret ∗ (string ret -∗ slots)`) all come with it.

### What comes next

From [logic.md](logic.md#recommendation): step lemmas, one per instruction form of the [[core-subset|core subset]], proved once as the WP's rules, so that no program proof computes a step; an `ectx_language` whose context is the callers stack, so that a function's specification returns its resources as an ordinary triple; `meta` as persistent ghost_map elements beside `live` and the cells; then Iris in the main build, hi.c and gc.ir's `sum` through the logic with libc's contracts as triples, and Hello. Campaign 5's certificates and RefinedC-style ownership types would then be fragments of the logic, sound because adequacy is.
