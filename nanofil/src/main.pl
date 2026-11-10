/*  The nanofil command line: the impure driver that reads a C or IR
    file, runs it through the compiler's stages and prints the result.

    ## Commands

    | Command | Does |
    |---|---|
    | `check FILE` | read and validate; prints `ok` |
    | `print FILE` | read, validate, print the IR (ir_text.pl) |
    | `compile FILE` | read, validate, print x86-64 assembly |
    | `cc FILE` | compile C (`.c`, or preprocessed `.i`) to Fil-C assembly |
    | `cc-ir FILE` | compile C, print the IR (unchecked; the Fil-C backend's input is pizlonated) |
    | `tokens FILE` | print C token terms, without locations |
    | `run FILE FN ARG...` | interpret FN on integer arguments |
    | `difftest FILE OUTDIR` | write `OUTDIR/expected.txt`, `OUTDIR/harness.c` and `OUTDIR/mode` for the file's `run(Fn, Args)` facts |
    | `outcomes FILE` | print the checked module of a Fil-C IR file and the interpreter's outcome of each run line, as terms (rocq/) |
    | `asm-terms FILE TEXT` | as `compile` for a Fil-C module, but write the assembly text to the file TEXT and print each asm.pl line as a term (rocq/backend) |
    | `abi-terms FILE` | print the checked module of a Fil-C file, then the reference ABI plan of each of its functions and its weak thunks' plans, as terms (rocq/backend) |
    | `encode FILE OUT` | read, validate and write the module as NFB, the bytecode of nfb.pl, to OUT (docs/nfb.md) |
    | `decode FILE` | read an NFB file, validate, print the IR |
    | `nfb-terms FILE PREFIX` | write the module, and a Fil-C module's checked module, as NFB with NAMES to `PREFIX.unchecked.nfb` and `PREFIX.checked.nfb`, and print each as `nfb_module(Stage, Module)` without its context items (rocq/backend) |
    | `nfb-check FILE` | write the module, and a Fil-C module's checked module, as NFB and read each back: the same term with NAMES, the same words without it (tests/nfb.sh) |
    | `emit-terms FILE` | print the checked module of a Fil-C file, then the reference emission's asm.pl lines, a list for each item, for each weak thunk and for the end of the file, as terms (rocq/backend) |

    A FILE ending in `.c` or `.i` goes through the C frontend, one ending
    in `.nfb` is NFB, and any other FILE is IR text. A `.c` file is preprocessed with the predefined
    macros and include paths of `$FILCC` (default `filcc`).

    ```diagram
    ┌──────┐  ┌─────────┐  ┌─────────┐
    │ c_pp │─▶│ c_parse │─▶│ c_lower │──┐
    └──────┘  └─────────┘  └─────────┘  │
      ┌─────────────────────────────────┘
      ▼
    ┌──────────┐  ┌───────────┐  ┌────────────┐
    │ opt (-O) │─▶│ pizlonate │─▶│ filc_amd64 │
    └──────────┘  └───────────┘  └────────────┘
    ```

    `cc` runs the whole pipeline; c_pp lexes with c_lex. IR text enters
    at the middle end, and a module in plain mode goes to amd64.pl
    instead of pizlonate and filc_amd64.

    ## -O

    `-O` before the command runs the middle end (opt.pl) after loading.
    Without it the IR goes to the backend as loaded, which is the
    reference the optimized path is checked against. With `-O`,
    difftest also runs every run line on the unoptimized module and
    fails unless each optimized outcome refines the original one
    (translation validation), and prints how many allocs promote
    removed.

    `--registers=stack|temps|pointers` independently selects reference
    emission or validated whole-function register homes for scalars with
    validated register operands and frame cells, on a frame with a home
    per scalar temporary (docs/perf.md items 3, 5a-loads and 3d), in the
    Fil-C backend. Pointers is temps with pointer address words as homes
    too, their lowers staying in the frame record (docs/perf.md 5b-2).
    The default is pointers with `-O` and stack without it;
    NANOFIL_REGISTERS supplies the same choice to build harnesses,
    `-O --registers=temps` keeps scalar homes only, and
    `-O --registers=stack` keeps the reference emission. The modes local,
    function, operands, cells and flow were retired in October 2026
    (docs/perf.md, register modes) and are refused.
    The plain backend is unchanged. Options precede the command.

    `--operands=rewrite|regions` selects, under temps or pointers, how
    each straight-line region's operands are chosen once the homes are
    in registers: rewrite, step 3b's forwarding of copies, or regions,
    which selects each region's registers again from the values the
    validated stream computes, operating on homes directly, with `lea`
    and three-address forms (docs/perf.md item 19). Both are checked by
    the same operand checker. The default is regions;
    NANOFIL_OPERANDS supplies the same choice.

    `--registers-limit=N` (or NANOFIL_REGISTERS_LIMIT), opt-in, emits
    each function of more than N checked IR instructions by the
    reference (stack) emission when registers are temps or pointers, to
    save compile time on very large functions (docs/perf.md, compile
    time).

    `--branches=reference|selected` independently selects the reference
    branch on a stored boolean, or a branch on the flags of a compare
    that only the branch reads, with jumps to the next block left to
    fall through (docs/perf.md). The default is selected with `-O` and
    reference without it; NANOFIL_BRANCHES supplies the same choice, and
    `-O --branches=reference` keeps the reference branches.

    `--memcpy=call|inline` independently selects the reference call for
    every memcpy and memmove, or, for a constant 1 to 16 bytes to a
    function the module does not define, an inline copy in front of
    that call, taken only when the runtime's checks would pass and
    neither object has aux (docs/perf.md item 7a). The default is
    inline with `-O` and call without it; NANOFIL_MEMCPY supplies the
    same choice, and nanofil-cc passes call for -fno-builtin,
    -fno-builtin-memcpy, -fno-builtin-memmove and -ffreestanding.

    `--bounds=split|merged|sign|or` selects the bounds check's shape:
    split, the default, tests ptr < lower and ptr > upper - Size with a
    branch each; merged tests both with one unsigned comparison of
    ptr - lower; sign and or test (ptr - lower) | (upper - Size - ptr)
    with one branch (docs/bounds.md). NANOFIL_BOUNDS supplies the same
    choice.

    `--share=none|block|null|upper` shares parts of heap checks of one
    object under split bounds and local selection: block leaves out the
    null test of a check whose lower an earlier check in its block
    tested, null also when that check is in a dominating block, and
    upper also reuses the upper a check of the same object just loaded
    (src/check_share.pl, docs/perf.md item 17). The default is upper
    with `-O`, except with `--checks=reference`, and none otherwise;
    NANOFIL_SHARE supplies the same choice.

    `--lowers=own|shared` selects the frame's GC roots: own, the
    default, gives every pointer temporary its own `lowers[]` entry;
    shared lets a flight use its lower root's entry, kept while the
    flight is live, and validates every frame (src/lower_roots.pl,
    src/lowers_check.pl, docs/lowers.md). NANOFIL_LOWERS supplies the
    same choice.

    `--inline=none|small|wide` independently selects no inlining, or,
    with `-O`, inlining of small static functions before promotion
    (src/inline.pl, docs/perf.md item 4), or that and more:
    always_inline, single-call-site and non-leaf callees, callees first
    (item 20). The default is wide with `-O`; without `-O` nothing
    inlines. NANOFIL_INLINE supplies the same choice, and nanofil-cc
    passes none for -fno-inline and -O0. A trap inside an inlined
    function reports its caller's name, as filcc -O2 does without -g.

    `--simplify=none|full` independently selects, with `-O`, the cheap
    middle end after copy propagation (src/simplify.pl, docs/perf.md
    item 8). The default is full; NANOFIL_SIMPLIFY supplies the same
    choice.

    `--checks=reference|reuse|renew|guard|hoist|schedule|half|forward|combined|hull|getter|extended` independently
    selects the reference checked IR, a check before every access, check
    reuse after pizlonation, reuse followed by renewal of dominated
    checks, both followed by range guards for checks in loops, both
    followed by hoisted bounds, a limit taken before a loop for its full
    checks of a root defined before it, or both followed by scheduled
    checks, which check early the bytes every path ahead needs and renew
    what they cover; a scheduled check may trap before stores that
    precede the failing access, or both followed by half checks, which
    test only the bound an earlier check of the object does not already
    establish, or reuse that also serves pointer loads and covers a check
    by the hull of its object's live facts, then renewal, which moves no
    trap, or that followed by half checks (combined), combined with
    renewal by the hull of two checks (hull), with facts kept across
    repeated getters of local globals (getter), or both (extended)
    (src/check_reuse.pl,
    src/schedule.pl, src/half_check.pl, docs/m7.md, docs/bounds.md,
    docs/schedule.md, docs/half.md, docs/forward.md). The default is
    combined with `-O` and reference without;
    NANOFIL_CHECKS supplies the same choice. With any but reference, `cc`,
    `compile` and difftest's pizlonation comparison use that module.

    GNU vector types and the SSE through AVX2 intrinsics
    (docs/vector-access.md) are on; `--no-vectors` (or `--vectors=off`)
    turns them off, refusing every vector type, and `--vectors` (or
    `--vectors=on`) turns them back on; the last one given wins.
    NANOFIL_VECTORS=0 or 1 supplies the same choice.

    ## difftest

    expected.txt holds the interpreter's result for every run line whose
    outcome a native run can reproduce: a known return value, or for a
    Fil-C module a trap, written just `trap`. harness.c prints the same
    lines from native code; for a Fil-C module it makes one call per
    process, chosen by `argv[1]`, since a trap ends the process. mode
    holds `plain` or `filc`. Other outcomes are reported on stdout and
    left out of the comparison.

    For a Fil-C module, difftest also runs every run line on the
    pizlonated module and fails unless each outcome is the same, traps
    and their reasons included.
*/
:- use_module(ir).
:- use_module(ir_text).
:- use_module(nfb).
% Compile-only commands do not need the interpreter or its CLP(Z) solver.
:- if(current_prolog_flag(dialect, swi)).
:- autoload(interp, [run/5, module_prepared/2, run_prepared/5, outcome_text/2]).
:- else.
:- use_module(interp).
:- endif.
:- use_module(amd64).
:- use_module(filc_amd64).
:- use_module(asm).
:- use_module(c_lex).
:- use_module(c_pp).
:- use_module(c_parse).
:- use_module(c_lower).
:- use_module(opt).
:- use_module(promote).
:- use_module(pizlonate).
:- use_module(check_reuse).
:- use_module(schedule).
:- use_module(half_check).
:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(pio)).
:- use_module(library(dcgs)).
:- use_module(library(pairs)).

:- initialization(main).

%! main is det.
%
%  The command line entry point (bin/nanofil): reads the options from
%  argv and the NANOFIL_* environment variables (options/8 and the
%  *_default predicates), runs command/4, and halts with 0; or prints
%  the error, or "failed" when the command fails, and halts with 1.
main :-
    % Trealla gives argv as character lists, SWI as atoms.
    current_prolog_flag(argv, RawArgv),
    maplist(arg_atom, RawArgv, Argv0),
    % halt/1 outside catch/3: SWI implements halt as an exception.
    catch(( ( vectors_options(Argv0, ArgvV),
              bounds_options(ArgvV, ArgvB),
              share_options(ArgvB, ArgvS),
              lowers_options(ArgvS, ArgvL),
              operands_options(ArgvL, Argv00),
              register_default(Default),
              checks_default(Checks0),
              inline_default(Inline0),
              inline_options(Argv00,Inline0,Inline,Argv1),
              simplify_default(Simplify0),
              simplify_options(Argv1,Simplify0,Simplify,Argv2),
              limit_default(Limit0),
              limit_options(Argv2,Limit0,Limit,Argv3),
              options(Argv3,o0,Default,Checks0,Level,Registers0,Checks,Argv),
              limited_registers(Limit,Registers0,Registers),
              opt_selection(Level,Inline,Simplify,Opt),
              command(Opt,Registers,Checks,Argv) )
          ->  Status = 0
          ;   format(user_error, "nanofil: failed~n", []),
              Status = 1
          ),
          Error,
          ( report(Error),
            Status = 1
          )),
    halt(Status).

% The emission choices: emit(Registers, Branches, Copies).
register_default(emit(Registers, Branches, Copies)) :-
    % Unbound until options/8: the defaults depend on -O.
    ( getenv('NANOFIL_REGISTERS',R) -> register_mode(R), Registers = R ; true ),
    ( getenv('NANOFIL_BRANCHES',B) -> branches_mode(B), Branches = B ; true ),
    ( getenv('NANOFIL_MEMCPY',M) -> memcpy_mode(M), Copies = M ; true ).
register_mode(R) :-
    ( memberchk(R,[stack,temps,pointers]) -> true
    ; memberchk(R,[local,function,operands,cells,flow])
    -> format(atom(Msg), 'registers=~w was retired (docs/perf.md); registers must be stack, temps or pointers', [R]),
       throw(nanofil_error(Msg))
    ; throw(nanofil_error('registers must be stack, temps or pointers')) ).
branches_mode(B) :-
    ( memberchk(B,[reference,selected]) -> true
    ; throw(nanofil_error('branches must be reference or selected')) ).
memcpy_mode(M) :-
    ( memberchk(M,[call,inline]) -> true
    ; throw(nanofil_error('memcpy must be call or inline')) ).
% checks_default(?Checks): NANOFIL_CHECKS, or unbound until -O decides.
checks_default(Checks) :-
    ( getenv('NANOFIL_CHECKS',C) -> checks_mode(C), Checks = C ; true ).
checks_mode(C) :-
    ( memberchk(C,[reference,reuse,renew,guard,hoist,schedule,half,forward,combined,
                   hull,getter,extended]) -> true
    ; throw(nanofil_error('checks must be reference, reuse, renew, guard, hoist, schedule, half, forward, combined, hull, getter or extended')) ).
% vectors_options(+Argv0, -Argv): Argv is Argv0 less its vector
% options, the last of which sets NANOFIL_VECTORS (c_types
% vector_type/4), for drivers that pass only options: --vectors and
% --vectors=on to 1, --no-vectors and --vectors=off to 0.
vectors_options(Argv0, Argv) :-
    exclude(vectors_option, Argv0, Argv),
    (   include(vectors_option, Argv0, Opts), last(Opts, Opt)
    ->  vectors_option(Opt, V), setenv('NANOFIL_VECTORS', V)
    ;   true
    ).

vectors_option(Opt) :- vectors_option(Opt, _).
vectors_option('--vectors', '1').
vectors_option('--vectors=on', '1').
vectors_option('--no-vectors', '0').
vectors_option('--vectors=off', '0').
% bounds_options(+Argv0, -Argv): Argv is Argv0 less its --bounds=
% options, the last of which sets NANOFIL_BOUNDS, the bounds check's
% shape (filc_amd64:bounds_check//4): split, the default, merged, sign
% or or.
bounds_options(Argv0, Argv) :-
    exclude(bounds_option, Argv0, Argv),
    (   include(bounds_option, Argv0, Opts), last(Opts, Opt)
    ->  atom_concat('--bounds=', B, Opt),
        (   memberchk(B, [split, merged, sign, or]) -> setenv('NANOFIL_BOUNDS', B)
        ;   throw(nanofil_error('bounds must be split, merged, sign or or'))
        )
    ;   true
    ).
bounds_option(A) :- atom(A), atom_concat('--bounds=', _, A).
% share_options(+Argv0, -Argv): Argv is Argv0 less its --share=
% options, the last of which sets NANOFIL_SHARE (check_share:share_mode/1).
share_options(Argv0, Argv) :-
    exclude(share_option, Argv0, Argv),
    (   include(share_option, Argv0, Opts), last(Opts, Opt)
    ->  atom_concat('--share=', S, Opt),
        (   memberchk(S, [none, block, null, upper]) -> setenv('NANOFIL_SHARE', S)
        ;   throw(nanofil_error('share must be none, block, null or upper'))
        )
    ;   true
    ).
share_option(A) :- atom(A), atom_concat('--share=', _, A).
% lowers_options(+Argv0, -Argv): Argv is Argv0 less its --lowers=
% options, the last of which sets NANOFIL_LOWERS (lower_roots:lowers_mode/1).
lowers_options(Argv0, Argv) :-
    exclude(lowers_option, Argv0, Argv),
    (   include(lowers_option, Argv0, Opts), last(Opts, Opt)
    ->  atom_concat('--lowers=', S, Opt),
        (   memberchk(S, [own, shared]) -> setenv('NANOFIL_LOWERS', S)
        ;   throw(nanofil_error('lowers must be own or shared'))
        )
    ;   true
    ).
lowers_option(A) :- atom(A), atom_concat('--lowers=', _, A).
% operands_options(+Argv0, -Argv): Argv is Argv0 less its --operands=
% options, the last of which sets NANOFIL_OPERANDS
% (amd64_regs:operand_selection/1).
operands_options(Argv0, Argv) :-
    exclude(operands_option, Argv0, Argv),
    (   include(operands_option, Argv0, Opts), last(Opts, Opt)
    ->  atom_concat('--operands=', S, Opt),
        (   memberchk(S, [rewrite, regions]) -> setenv('NANOFIL_OPERANDS', S)
        ;   throw(nanofil_error('operands must be rewrite or regions'))
        )
    ;   true
    ).
operands_option(A) :- atom(A), atom_concat('--operands=', _, A).
% inline_options(+Argv0, +Inline0, -Inline, -Argv): Argv is Argv0 less
% its --inline= options, the last of which gives Inline.
inline_options([], I, I, []).
inline_options([A|As], I0, I, Args) :-
    (   atom(A), atom_concat('--inline=', I1, A)
    ->  inline_mode(I1), inline_options(As, I1, I, Args)
    ;   Args = [A|Args1], inline_options(As, I0, I, Args1)
    ).
% inline_default(?Inline): NANOFIL_INLINE, or unbound until -O decides.
inline_default(Inline) :-
    ( getenv('NANOFIL_INLINE',I) -> inline_mode(I), Inline = I ; true ).
inline_mode(I) :-
    ( memberchk(I,[none,small,wide]) -> true
    ; throw(nanofil_error('inline must be none, small or wide')) ).
% limit_options(+Argv0, +Limit0, -Limit, -Argv): as inline_options/4,
% for --registers-limit=N; Limit is none or a nonnegative integer.
limit_options([], L, L, []).
limit_options([A|As], L0, L, Args) :-
    (   atom(A), atom_concat('--registers-limit=', N, A)
    ->  limit_mode(N, L1), limit_options(As, L1, L, Args)
    ;   Args = [A|Args1], limit_options(As, L0, L, Args1)
    ).
limit_default(L) :-
    ( getenv('NANOFIL_REGISTERS_LIMIT',N) -> limit_mode(N, L) ; L = none ).
limit_mode(A, N) :-
    (   catch(atom_number(A, N), _, fail), integer(N), N >= 0 -> true
    ;   throw(nanofil_error('registers-limit must be a nonnegative integer'))
    ).
% limited_registers(+Limit, +Emission0, -Emission): limited(R, N) for
% temps or pointers registers under a limit (filc_amd64.pl's
% item_placed_lines/6).
limited_registers(none, E, E) :- !.
limited_registers(N, emit(R,B,M), emit(limited(R,N),B,M)) :- memberchk(R, [temps,pointers]), !.
limited_registers(_, E, E).
% simplify_options(+Argv0, +Simplify0, -Simplify, -Argv): as
% inline_options/4, for --simplify=.
simplify_options([], S, S, []).
simplify_options([A|As], S0, S, Args) :-
    (   atom(A), atom_concat('--simplify=', S1, A)
    ->  simplify_mode(S1), simplify_options(As, S1, S, Args)
    ;   Args = [A|Args1], simplify_options(As, S0, S, Args1)
    ).
% simplify_default(?Simplify): NANOFIL_SIMPLIFY, or unbound until -O decides.
simplify_default(Simplify) :-
    ( getenv('NANOFIL_SIMPLIFY',S) -> simplify_mode(S), Simplify = S ; true ).
simplify_mode(S) :-
    ( memberchk(S,[none,full]) -> true
    ; throw(nanofil_error('simplify must be none or full')) ).
% opt_selection(+Level, ?Inline, ?Simplify, -Opt): the middle end's
% selection (opt.pl). Inlining and simplification need -O, where
% inlining is wide and simplification full unless chosen otherwise.
opt_selection(o0, _, _, o0).
opt_selection(o1, Inline, Simplify, Opt) :-
    ( var(Inline) -> Inline = wide ; true ),
    ( var(Simplify) -> Simplify = full ; true ),
    middle_selection(Simplify, Inline, Opt).
middle_selection(none, none, o1).
middle_selection(none, small, o1(small)).
middle_selection(none, wide, o1(wide, none)).
middle_selection(full, Inline, o1(Inline, full)).
% opt_level(+Opt, -Level): o0 or o1, for difftest's validation.
opt_level(o0, o0).
opt_level(o1, o1).
opt_level(o1(_), o1).
opt_level(o1(_, _), o1).

options(['-O'|As],_,R,C,O,Rs,Cs,Args) :- !, options(As,o1,R,C,O,Rs,Cs,Args).
options([A|As],O,emit(_,B,M),C,Opt,Rs,Cs,Args) :-
    atom_concat('--registers=',R,A), !, register_mode(R),
    options(As,O,emit(R,B,M),C,Opt,Rs,Cs,Args).
options([A|As],O,emit(R,_,M),C,Opt,Rs,Cs,Args) :-
    atom_concat('--branches=',B,A), !, branches_mode(B),
    options(As,O,emit(R,B,M),C,Opt,Rs,Cs,Args).
options([A|As],O,emit(R,B,_),C,Opt,Rs,Cs,Args) :-
    atom_concat('--memcpy=',M,A), !, memcpy_mode(M),
    options(As,O,emit(R,B,M),C,Opt,Rs,Cs,Args).
options([A|As],O,R,_,Opt,Rs,Cs,Args) :-
    atom_concat('--checks=',C,A), !, checks_mode(C),
    options(As,O,R,C,Opt,Rs,Cs,Args).
options(Args,O,emit(R,B,M),C,O,emit(R,B,M),C,Args) :-
    registers_default(O,R), branches_default(O,B), memcpy_default(O,M),
    checks_default(O,C), share_default(O,C).

%! registers_default(+Opt, ?Registers) is det.
%
%  Registers is the register mode for optimization level Opt (o0 or
%  o1) when no --registers option or NANOFIL_REGISTERS chose one: stack,
%  the reference emission, without -O, and pointers, a home per scalar
%  temporary and per pointer address word (amd64_regs.pl), with it.
%  branches_default/2 does the same for branch selection: reference
%  without -O, selected with it.
registers_default(_, R) :- nonvar(R), !.
registers_default(o0, stack).
registers_default(o1, pointers).
branches_default(_, B) :- nonvar(B), !.
branches_default(o0, reference).
branches_default(o1, selected).
% memcpy_default(+Opt, ?Copies): -O inlines small constant copies.
memcpy_default(_, M) :- nonvar(M), !.
memcpy_default(o0, call).
memcpy_default(o1, inline).
% checks_default(+Opt, ?Checks): -O combines forward facts and half
% checks (docs/forward.md, docs/half.md); without it every access keeps
% its full check.
checks_default(_, C) :- nonvar(C), !.
checks_default(o0, reference).
checks_default(o1, combined).
% share_default(+Opt, +Checks): -O shares null tests and uppers
% (check_share.pl) unless --share= or NANOFIL_SHARE chose or the checks
% are the reference's, which stay whole; without -O nothing is shared.
share_default(o0, _).
share_default(o1, C) :-
    (   ( getenv('NANOFIL_SHARE', _) ; C == reference ) -> true
    ;   setenv('NANOFIL_SHARE', upper)
    ).

% arg_atom(+Arg, -Atom): Atom is the command-line argument Arg, which
% is an atom (SWI) or a character list (Trealla).
arg_atom(Atom, Atom) :-
    atom(Atom),
    !.
arg_atom(Cs, Atom) :-
    atom_chars(Atom, Cs).

% report(+Error): print Error on stderr, a nanofil_error by its message
% and anything else as a quoted term. Error is any ball, so the last
% clause is a default and the cut stays.
report(nanofil_error(Msg)) :-
    !,
    format(user_error, "nanofil: ~w~n", [Msg]).
report(Error) :-
    format(user_error, "nanofil: ~q~n", [Error]).

%% Loading

% file_module(+File, -Module): Module is the valid IR module in File. A
% .c or .i file goes through the C frontend, a .nfb file is NFB, and
% anything else is IR text.
file_module(File, Module) :-
    (   (   atom_concat(_, '.c', File)
        ;   atom_concat(_, '.i', File)
        )
    ->  c_file_module(File, Module)
    ;   atom_concat(_, '.nfb', File)
    ->  read_nfb_file(File, Words),
        (   module_nfb(Module, Words) -> true
        ;   format(atom(Msg), '~w: not the NFB of a module', [File]),
            throw(nanofil_error(Msg))
        ),
        valid_module(Module)
    ;   read_ir_file(File, Module, _),
        valid_module(Module)
    ).

% c_file_module(+File, -Module): Module is the valid IR module of the C
% file. c_file_module/4 also gives the assembly lines of its top-level
% asm (c_lower c_toplevel_asm/2), which `cc` prints after the module,
% and its functions' inlining attributes (c_lower c_module/3).
c_file_module(File, Module) :- c_file_module(File, Module, _, _).
c_file_module(File, Module, AsmLines, Attributes) :-
    c_file_tokens(File, Tokens),
    release_stacks,
    (   c_parse(Tokens, Items) -> true
    ;   throw(nanofil_error('C parse failed'))
    ),
    release_stacks,
    % Deterministic stages: a leftover choicepoint would keep the tokens
    % and items of a large translation unit (SQLite) alive to the end.
    once(c_module(Items, Module, Attributes)),
    once(c_toplevel_asm(Items, AsmLines)),
    % The frontend's garbage is gone once its items are: SQLite with
    % FTS3, R-Tree and sessions (nixpkgs' flags) has 220 MB live here,
    % yet without this the validator ran out of the 1 GB stack.
    release_stacks,
    once(valid_module(Module)).

% c_file_tokens(+File, -Tokens): Tokens are the C tokens of File. A .i
% file is already preprocessed; anything else goes through c_pp with the
% predefined macros and include paths of $FILCC (default filcc).
c_file_tokens(File, Tokens) :-
    (   atom_concat(_, '.i', File)
    ->  once(i_file_tokens(File, Tokens0))
    ;   ( getenv('FILCC', Clang) -> true ; Clang = filcc ),
        pp_profile(Clang, Profile),
        pp_file(File, Profile, Tokens0)
    ),
    (   getenv('NANOFIL_STD', Std), Std \== c17, Std \== gnu89
    ->  (   Std == c23 -> c23_tokens(Tokens0, Tokens)
        ;   throw(nanofil_error('NANOFIL_STD must be c17, c23 or gnu89'))
        )
    ;   Tokens = Tokens0
    ).

%% Commands

/* release_stacks: collect garbage and return unused stack memory to the
   system between the stages of a large compile. SWI grows its stacks
   between collections and keeps them grown, and its stack limit counts
   what is allocated, not what is live: gnulib's test-intprops.c, whose
   main has 87,000 blocks, never has more than about 210 MB live, yet
   the frontend leaves the trail at 250 MB and the middle end the global
   stack at 1 GB, and the next collection, which must shift them first,
   exceeds the default 1 GB limit. A host without these predicates
   skips them. */
release_stacks :-
    catch(garbage_collect, error(existence_error(_, _), _), true),
    catch(trim_stacks, error(existence_error(_, _), _), true).

%! command(+Opt, +Registers, +Checks, +Args) is det.
%
%  Runs the command Args, [Command|Operands], such as [cc, File]; the
%  header comment's table lists the commands. Opt is the middle end's
%  selection: o0 without -O, else o1, o1(Inline) or o1(Inline, full)
%  (opt.pl). Registers is the emission choice emit(Registers, Branches,
%  Copies), and Checks the check passes (checks_module/3). Only native
%  emission needs Registers and only the Fil-C checked stage needs
%  Checks (difftest runs it too). Throws nanofil_error(Msg) for a
%  refused program.
command(Opt, Registers, Checks, [compile, File]) :- !,
    file_module(File, Module0),
    % Promote can remove every p from a module; the ABI is the original's.
    module_mode(Module0, Mode),
    optimize(Opt, Module0, Module),
    mode_print_asm(Mode, Registers, Checks, Module).
command(Opt0, Registers, Checks, [cc, File]) :- !,
    c_file_module(File, Module0, AsmLines, Attributes),
    inline_attributes(Opt0, Attributes, Opt),
    release_stacks,
    once(optimize(Opt, Module0, Module)),
    release_stacks,
    mode_print_asm(filc, Registers, Checks, Module),
    forall(member(Line, AsmLines), format("~w~n", [Line])).
command(Opt, Registers, Checks, ['asm-terms', File, Text]) :- !,
    file_module(File, Module0),
    (   module_mode(Module0, filc) -> true
    ;   throw(nanofil_error('asm-terms needs a Fil-C module'))
    ),
    optimize(Opt, Module0, Module),
    checked_module(Checks, Module, Checked),
    open(Text, write, Stream),
    filc_module_emit(Checked, Registers, print_asm_terms(Stream)),
    close(Stream).
command(Opt, _, Checks, ['abi-terms', File]) :- !,
    file_module(File, Module0),
    (   module_mode(Module0, filc) -> true
    ;   throw(nanofil_error('abi-terms needs a Fil-C module'))
    ),
    optimize(Opt, Module0, Module),
    checked_module(Checks, Module, Checked),
    format("~k.~n", [Checked]),
    filc_module_plans(Checked, print_term_line).
command(Opt, _, Checks, ['nfb-check', File]) :- !,
    file_module(File, Module0),
    optimize(Opt, Module0, Module),
    nfb_round_trip(File, unchecked, Module),
    (   module_mode(Module, filc)
    ->  checked_module(Checks, Module, Checked),
        nfb_round_trip(File, checked, Checked)
    ;   true
    ).
command(Opt, _, Checks, ['nfb-terms', File, Prefix]) :- !,
    file_module(File, Module0),
    optimize(Opt, Module0, Module),
    nfb_terms(Prefix, unchecked, Module),
    (   module_mode(Module, filc)
    ->  checked_module(Checks, Module, Checked),
        nfb_terms(Prefix, checked, Checked)
    ;   true
    ).
command(Opt, _, Checks, ['emit-terms', File]) :- !,
    file_module(File, Module0),
    (   module_mode(Module0, filc) -> true
    ;   throw(nanofil_error('emit-terms needs a Fil-C module'))
    ),
    optimize(Opt, Module0, Module),
    checked_module(Checks, Module, Checked),
    format("~k.~n", [Checked]),
    filc_module_emit(Checked, stack, print_term_line).
command(Opt, _, Checks, [difftest, File, Dir]) :- !,
    difftest(Opt, Checks, File, Dir).
command(Opt, _, Checks, [outcomes, File]) :- !,
    outcomes(Opt, Checks, File).
command(Opt, _, _, Args) :- command(Opt,Args).

% inline_attributes(+Opt0, +Attributes, -Opt): wide inlining takes the C
% file's always_inline and noinline functions (c_module/3), which the IR
% does not carry, in its selection. Other selections are unchanged.
inline_attributes(o1(wide, S), Attributes, o1(wide(Attributes), S)) :- !.
inline_attributes(Opt, _, Opt).

% command(+Opt, +Args): carry out the command line Args (without options),
% running the middle end when Opt is o1 (-O given) and not when o0.
% Fails or throws when the command does.
command(_, [tokens, File]) :-
    c_file_tokens(File, Tokens),
    forall(member(tok(Token, _), Tokens),
           ( write_canonical(Token), write('.'), nl )).
command(_, [check, File]) :-
    file_module(File, _),
    format("ok~n", []).
command(Opt, [encode, File, Out]) :-
    file_module(File, Module0),
    optimize(Opt, Module0, Module),
    module_nfb(Module, Words),
    write_nfb_file(Out, Words).
command(_, [decode, File]) :-
    (   atom_concat(_, '.nfb', File) -> true
    ;   throw(nanofil_error('decode needs a .nfb file'))
    ),
    file_module(File, Module),
    print_module(Module).
command(Opt, [print, File]) :-
    file_module(File, Module0),
    optimize(Opt, Module0, Module),
    print_module(Module).
command(Opt0, ['cc-ir', File]) :-
    c_file_module(File, Module0, _, Attributes),
    inline_attributes(Opt0, Attributes, Opt),
    optimize(Opt, Module0, Module),
    print_module(Module).
command(Opt, [run, File, Fn|ArgAtoms]) :-
    file_module(File, Module0),
    optimize(Opt, Module0, Module),
    maplist(atom_number, ArgAtoms, Args0),
    func_named(Module, Fn, func(_, _, _, Params, _)),
    maplist(canonical_arg, Params, Args0, Args),
    max_fuel(Fuel),
    once(run(Module, Fn, Args, Fuel, Outcome)),
    outcome_text(Outcome, Text),
    format("~w~n", [Text]).
difftest(Sel, Checks, File, Dir) :-
    file_module(File, Module0),
    module_mode(Module0, Mode),
    optimize(Sel, Module0, Module),
    opt_level(Sel, Opt),
    file_runs(File, Runs),
    opt_valid_module(Opt, Module),
    module_prepared(Module0, Prepared0),
    module_prepared(Module, Prepared),
    % One findall over all runs, so each run's heap is reclaimed on
    % backtracking before the next starts.
    findall(Result-Verdict,
            ( member(Run, Runs),
              validated_run(Sel, Module0-Prepared0, Module-Prepared, Run,
                            Result, Verdict)
            ),
            ResultVerdicts),
    pairs_keys_values(ResultVerdicts, Results, Verdicts),
    opt_report_validation(Opt, File, Module0, Module, Verdicts),
    mode_pizlonation_agrees(Mode, Checks, File, Module-Prepared, Runs),
    include(comparable(Mode), Results, Compared),
    exclude(comparable(Mode), Results, Skipped),
    atom_concat(Dir, '/expected.txt', ExpectedFile),
    atom_concat(Dir, '/harness.c', HarnessFile),
    atom_concat(Dir, '/mode', ModeFile),
    write_file(ExpectedFile, expected_lines(Compared)),
    write_file(HarnessFile, harness(Mode, Module, Compared)),
    write_file(ModeFile, fmt("~w~n", [Mode])),
    length(Compared, NCompared),
    length(Skipped, NSkipped),
    format("~w: ~w runs compared, ~w not comparable~n",
           [File, NCompared, NSkipped]),
    forall(member(r(Fn, Args, Outcome), Skipped),
           ( outcome_text(Outcome, Text),
             call_text(Fn, Args, CallText),
             format("  ~w = ~w~n", [CallText, Text])
           )).

% nfb_round_trip(+File, +Stage, +Module): Module, written as NFB, reads
% back as itself, and its core sections alone read back as a module
% whose core encoding is those very words (nfb.pl). Prints the sizes;
% throws nanofil_error otherwise.
nfb_round_trip(File, Stage, Module) :-
    module_nfb(Module, Words),
    nfb_core(Words, Core),
    (   module_nfb(Module1, Words), Module1 == Module,
        module_nfb(Module2, Core), module_nfb(Module2, [], Core2), Core2 == Core
    ->  length(Words, N), length(Core, NC),
        format("~w: ~w ~w words, ~w core~n", [File, Stage, N, NC])
    ;   format(atom(Msg), '~w: the ~w module does not read back from NFB', [File, Stage]),
        throw(nanofil_error(Msg))
    ).

% nfb_terms(+Prefix, +Stage, +Module): write Module, its context items
% dropped, as NFB with NAMES to Prefix.Stage.nfb, and print it as
% nfb_module(Stage, Module) for the Gallina reader and writer
% (rocq/backend/tests/nfb.sh).
nfb_terms(Prefix, Stage, module(All)) :-
    findall(I, ( member(I, All), I \= context(_, _) ), Items),
    module_nfb(module(Items), [names], Words),
    format(atom(Out), '~w.~w.nfb', [Prefix, Stage]),
    write_nfb_file(Out, Words),
    format("~k.~n", [nfb_module(Stage, module(Items))]).

%! outcomes(+Opt, +Checks, +File) is det.
%
%  Prints, as Prolog terms, the checked module of the Fil-C IR File
%  (after the middle end when Opt is o1, and the check passes Checks)
%  and then, for each run line, outcome(Fn, Args, Fuel, Outcome), the
%  interpreter's outcome on that module, or error(Fn, Args, Fuel, E)
%  when the run throws E or finds no outcome. An independent model of
%  the checked IR (rocq/, docs/formal.md) reads them.
outcomes(Sel, Checks, File) :-
    file_module(File, Module0),
    module_mode(Module0, Mode),
    (   Mode == filc -> true
    ;   throw(nanofil_error('outcomes needs a Fil-C module'))
    ),
    optimize(Sel, Module0, Module),
    checked_module(Checks, Module, Checked),
    format("~k.~n", [Checked]),
    file_runs(File, Runs),
    module_prepared(Checked, Prepared),
    max_fuel(Fuel),
    forall(member(run(Fn, Args0), Runs),
           ( catch(( module_run_result(Checked-Prepared, run(Fn, Args0), Fuel,
                                       r(_, Args, Outcome))
                   -> Line = outcome(Fn, Args, Fuel, Outcome)
                   ;  Line = error(Fn, Args0, Fuel, failed)
                   ),
                   E, Line = error(Fn, Args0, Fuel, E)),
             format("~k.~n", [Line]) )).

%! mode_print_asm(+Mode, +Registers, +Checks, +Module) is det.
%
%  Prints the assembly of Module by the backend for Mode, filc or plain.
%  Fil-C prints one item at a time (filc_module_emit/3), since a large
%  module's lines (SQLite's) need not all be held at once.
mode_print_asm(plain, _, _, Module) :-
    module_asm(Module, Asm), print_asm(Asm).
mode_print_asm(filc, Registers, Checks, Module) :-
    checked_module(Checks, Module, Checked),
    filc_module_emit(Checked, Registers, print_asm).

% print_asm_terms(+Stream, +Lines): the text of the asm.pl lines Lines
% to Stream, and each line as a canonical term and a full stop to the
% current output. The extracted printer must turn the terms into the
% text (rocq/backend/tests/asm.sh).
print_asm_terms(Stream, Lines) :-
    forall(member(Line, Lines), format("~k.~n", [Line])),
    current_output(Out),
    set_output(Stream),
    print_asm(Lines),
    set_output(Out).

% print_term_line(+Term): Term as a canonical term and a full stop.
print_term_line(Term) :-
    format("~k.~n", [Term]).

%! checked_module(+Checks, +Module, -Checked) is det.
%
%  Checked is Module pizlonated (pizlonate_module/2), validated as
%  checked IR (valid_module/1), and then rewritten by the check passes
%  Checks selects (checks_module/3). Throws if the validator refuses
%  either.
checked_module(Checks, Module, Checked) :-
    once(pizlonate_module(Module, Checked0)),
    release_stacks,
    once(valid_module(Checked0)),
    release_stacks,
    checks_module(Checks, Checked0, Checked).

%! checks_module(+Checks, +Checked0, -Checked) is det.
%
%  Checked is the checked module Checked0 after the check passes of
%  Checks (--checks; docs/m7.md): reference keeps pizlonate's naive
%  checks; reuse deletes a check an earlier live one covers; renew
%  also replaces a dominated check by a test of only the
%  free and read-only flags; guard also puts a span test before a loop
%  and makes its checks renew_if; combined, the -O default, is forward
%  facts followed by half checks; hull, getter and extended add
%  renew_hull and facts across repeated getters (docs/forward.md). Each pass's result must pass its
%  *_refines identity check against its input, and the validator
%  (valid_module/1) then checks the result's evidence again on its own.
checks_module(reference, Checked, Checked).
checks_module(reuse, Checked0, Checked) :-
    reused_module(Checked0, Checked),
    once(valid_module(Checked)).

% Renew (docs/m7.md, round 4) runs after reuse: what reuse keeps, a
% dominating check may renew. Only the result is validated: a renew
% keeps its check's proof and index, so reuse's output is valid if it is.
checks_module(renew, Checked0, Checked) :-
    renewed_module(Checked0, Checked),
    once(valid_module(Checked)).

% Guards (docs/m7.md, round 5) run after renewal: a check renewal left
% in a loop may become a guarded renewal. Only the result is validated.
checks_module(guard, Checked0, Checked) :-
    renewed_module(Checked0, Checked1),
    once(guard_checks(Checked1, Checked)),
    (   guard_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('range guards changed more than checks'))
    ),
    once(valid_module(Checked)).

% Hoisted bounds (docs/bounds.md) run after renewal: a full check
% renewal left in a loop may test its bounds against a limit taken
% before the loop. Only the result is validated.
checks_module(hoist, Checked0, Checked) :-
    renewed_module(Checked0, Checked1),
    once(hoist_checks(Checked1, Checked)),
    (   hoist_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('hoisted bounds changed more than checks'))
    ),
    once(valid_module(Checked)).

% Scheduled checks (docs/schedule.md) run after renewal: a check widens
% over the bytes every path ahead needs from its base, and the checks it
% then covers are renewed at a distance. Only the result is validated.
checks_module(schedule, Checked0, Checked) :-
    renewed_module(Checked0, Checked1),
    once(schedule_checks(Checked1, Checked)),
    (   schedule_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('scheduled checks changed more than checks'))
    ),
    once(valid_module(Checked)).

% Half checks (docs/half.md) run after renewal: a full check renewal left
% whose object an earlier check covers at one end tests only the other.
% Only the result is validated.
checks_module(half, Checked0, Checked) :-
    renewed_module(Checked0, Checked1),
    once(half_checks(Checked1, Checked)),
    (   half_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('half checks changed more than checks'))
    ),
    once(valid_module(Checked)).

% Forward facts (docs/forward.md): reuse that also serves heap pointer
% loads and covers a check by the hull of its object's live facts, then
% renewal at any distance (docs/schedule.md's renew from a related
% pointer's check). No trap moves. Only the result is validated.
checks_module(forward, Checked0, Checked) :-
    forwarded_module(forward, any, Checked0, Checked),
    once(valid_module(Checked)).

% Combined: forward facts, then half checks for what renewal left. Each
% stage keeps its own refines check. Only the result is validated.
checks_module(combined, Checked0, Checked) :-
    combined_module(forward, any, Checked0, Checked).
% Combined with renewal by the hull of two checks (hull), with facts kept
% across repeated getter calls (getter), or both (extended), opt-in
% (docs/forward.md). Each stage keeps its own refines check.
checks_module(hull, Checked0, Checked) :-
    combined_module(forward, hull, Checked0, Checked).
checks_module(getter, Checked0, Checked) :-
    combined_module(getter, any, Checked0, Checked).
checks_module(extended, Checked0, Checked) :-
    combined_module(getter, hull, Checked0, Checked).

combined_module(Reuse, Renew, Checked0, Checked) :-
    forwarded_module(Reuse, Renew, Checked0, Checked1),
    once(half_checks(Checked1, Checked)),
    (   half_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('half checks changed more than checks'))
    ),
    once(valid_module(Checked)).

forwarded_module(Reuse, Renew, Checked0, Checked) :-
    once(reuse_checks(Reuse, Checked0, Checked1)),
    (   reuse_refines(Reuse, Checked0, Checked1) -> true
    ;   throw(nanofil_error('forward reuse changed more than proofs'))
    ),
    once(renew_checks(Renew, Checked1, Checked)),
    (   renew_refines(Renew, Checked1, Checked) -> true
    ;   throw(nanofil_error('check renewal changed more than checks'))
    ).

renewed_module(Checked0, Checked) :-
    reused_module(Checked0, Checked1),
    once(renew_checks(Checked1, Checked)),
    (   renew_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('check renewal changed more than checks'))
    ).

reused_module(Checked0, Checked) :-
    once(reuse_checks(Checked0, Checked)),
    (   reuse_refines(Checked0, Checked) -> true
    ;   throw(nanofil_error('check reuse changed more than proofs'))
    ).

%! mode_pizlonation_agrees(+Mode, +Checks, +File, +Module-Prepared, +Runs) is det.
%
%  For a filc module, the checked Module (checked_module/3 with Checks)
%  has the same outcome as Module on every run of Runs, traps and their
%  reasons included, or the command throws: the explicit checks are
%  exactly the implicit ones. A missing or too weak check shows as the
%  outcome unchecked(Why). Both run with the same fuel, since pizlonate
%  keeps every block. A plain module has nothing to compare.
mode_pizlonation_agrees(plain, _, _, _, _).
mode_pizlonation_agrees(filc, Checks, File, Module-Prepared, Runs) :-
    checked_module(Checks, Module, Checked),
    module_prepared(Checked, CheckedPrepared),
    findall(Bad,
            ( member(Run, Runs),
              pizlonation_verdict(Module-Prepared, Checked-CheckedPrepared,
                                  Run, Bad),
              Bad \== ok
            ),
            Bads),
    forall(member(bad(CallText, Text0, Text), Bads),
           format("PIZLONATION FAILED ~w ~w: ~w unchecked, ~w checked~n",
                  [File, CallText, Text0, Text])),
    (   Bads == [] -> true
    ;   throw(nanofil_error('pizlonation changed an outcome'))
    ).

pizlonation_verdict(Original, Checked, Run, Verdict) :-
    fuel_step(Fuel),
    module_run_result(Original, Run, Fuel, r(Fn, Args, Outcome0)),
    max_fuel(MaxFuel),
    (   Outcome0 \== out_of_fuel
    ;   Fuel == MaxFuel
    ),
    !,
    module_run_result(Checked, Run, Fuel, r(_, _, Outcome)),
    (   (   ground(Outcome0) -> Outcome0 == Outcome
        ;   \+ \+ Outcome0 = Outcome
        )
    ->  Verdict = ok
    % A scheduled check's earlier trap (docs/schedule.md) is accepted
    % exactly when the reference run traps too, whatever its reason.
    ;   Outcome = trap(early(_)), nonvar(Outcome0), Outcome0 = trap(_)
    ->  Verdict = ok
    ;   call_text(Fn, Args, CallText),
        outcome_text(Outcome0, Text0),
        outcome_text(Outcome, Text),
        Verdict = bad(CallText, Text0, Text)
    ).

% opt_valid_module(+Opt, +Module): with -O (o1), the optimized Module is
% valid. valid_module's clauses leave choice points that throw on retry.
opt_valid_module(o0, _).
opt_valid_module(o1, Module) :- once(valid_module(Module)).

% opt_report_validation(+Opt, +File, +Module0, +Module, +Verdicts): with
% -O (o1), report_validation/4.
opt_report_validation(o0, _, _, _, _).
opt_report_validation(o1, File, Module0, Module, Verdicts) :-
    report_validation(File, Module0, Module, Verdicts).

%! report_validation(+File, +Module0, +Module, +Verdicts) is det.
%
%  Prints the -O difftest report: promote's effect, then every
%  validation failure among Verdicts, which together make the command
%  throw.
report_validation(File, Module0, Module, Verdicts) :-
    alloc_count(Module0, Allocs0),
    alloc_count(Module, Allocs),
    format("~w: promote: ~w allocs -> ~w~n", [File, Allocs0, Allocs]),
    forall(member(bad(CallText, Text0, Text), Verdicts),
           format("VALIDATION FAILED ~w ~w: ~w before the middle end, ~w after~n",
                  [File, CallText, Text0, Text])),
    (   memberchk(bad(_, _, _), Verdicts)
    ->  throw(nanofil_error('translation validation failed'))
    ;   true
    ).

%% Running and validating

% Fuel (blocks run) for a command-line run and the last validation step.
max_fuel(1000000).

/* validated_run(+Opt, +Original, +Optimized, +Run, -Result, -Verdict):
   Result is Run's r/3 on the module that difftest compares, and Verdict
   ok or bad(CallText, OriginalText, OptimizedText).

   Translation validation: the unoptimized module's outcome on the same
   run must allow the optimized one's. Both runs happen in the same
   findall step, so an unknown result keeps its constraints. Promote keeps
   every block and branch, so a correct result needs exactly the blocks
   the original needs: both run with the same fuel, starting small and
   growing until the original finishes. A broken pass that loops then
   ends as out_of_fuel, cheaply (the interpreter's memory grows quickly
   with the number of blocks run, so a looping run at full fuel would
   exhaust it). */
validated_run(o0, _, Optimized, Run, Result, ok) :-
    max_fuel(Fuel),
    module_run_result(Optimized, Run, Fuel, Result).
validated_run(Sel, Original, Optimized, Run, Result, Verdict) :-
    opt_level(Sel, o1),
    fuel_step(Fuel),
    module_run_result(Original, Run, Fuel, r(Fn, Args, Outcome0)),
    max_fuel(MaxFuel),
    (   Outcome0 \== out_of_fuel
    ;   Fuel == MaxFuel
    ),
    % Commit to the first fuel step at which the original finishes, or
    % to the last one.
    !,
    optimized_fuel(Sel, Fuel, Fuel1),
    module_run_result(Optimized, Run, Fuel1, Result),
    Result = r(_, _, Outcome),
    (   refines(Outcome0, Outcome) -> Verdict = ok
    ;   call_text(Fn, Args, CallText),
        outcome_text(Outcome0, Text0),
        outcome_text(Outcome, Text),
        Verdict = bad(CallText, Text0, Text)
    ).

% optimized_fuel(+Sel, +Fuel, -Fuel1): the optimized module's fuel.
% Inlining adds a join block per inlined call, at most one block run
% for each block the original runs.
optimized_fuel(o1, Fuel, Fuel).
optimized_fuel(o1(_), Fuel, Fuel1) :- Fuel1 is 2 * Fuel.
optimized_fuel(o1(_, _), Fuel, Fuel1) :- Fuel1 is 2 * Fuel.

% fuel_step(-Fuel) is multi: Fuel is one of the growing fuel limits,
% smallest first, ending at max_fuel.
fuel_step(Fuel) :-
    member(Fuel, [1000, 8000, 64000, 512000, 1000000]).

% canonical_arg(+Param, +Arg0, -Arg): Arg is Arg0 reduced modulo the
% class of Param.
canonical_arg(param(Class, _), Arg0, Arg) :-
    modulus(Class, Modulus),
    Arg is Arg0 mod Modulus.

% module_run_result(+Module-Prepared, +Run, +Fuel, -Result): Result is
% the r(Fn, Args, Outcome) of the "# run:" line Run on a module and the
% interpreter's preparation of it, with Fuel. Throws if the line does
% not fit the module or the interpreter finds no outcome.
module_run_result(Module-Prepared, run(Fn, Args0), Fuel,
                  r(Fn, Args, Outcome)) :-
    (   func_named(Module, Fn, func(_, export, _, Params, _)) -> true
    ;   throw(nanofil_error(
                  Fn-'run line names a function that is not exported'))
    ),
    (   length(Params, N), length(Args0, N) -> true
    ;   throw(nanofil_error(
                  Fn-'run line has the wrong number of arguments'))
    ),
    maplist(canonical_arg, Params, Args0, Args),
    (   once(run_prepared(Prepared, Fn, Args, Fuel, Outcome)) -> true
    ;   call_text(Fn, Args, CallText),
        throw(nanofil_error(CallText-'interpreter found no outcome'))
    ).

% comparable(+Mode, +Result) is semidet: a native run in Mode (plain or
% filc) reproduces Result's outcome, a known return value or, for
% filc, a trap or a reached unreachable, both a Fil-C safety panic
% natively. Nothing else has a native counterpart.
comparable(_, r(_, _, ret(V))) :-
    integer(V).
comparable(_, r(_, _, ret)).
comparable(filc, r(_, _, trap(_))).
comparable(filc, r(_, _, unreachable)).

% call_text(+Fn, +Args, -Text): Text is the atom 'Fn(A1, A2, ...)'.
call_text(Fn, Args, Text) :-
    atomic_list_concat(Args, ', ', ArgText),
    format(atom(Text), '~w(~w)', [Fn, ArgText]).

%% difftest output files

% write_file(+File, :Body_2): write the characters Body_2 (a DCG body)
% describes to File.
write_file(File, Body_2) :-
    phrase(Body_2, Cs),
    open(File, write, Stream),
    format(Stream, "~s", [Cs]),
    close(Stream).

% expected_lines(+Results)//: one "CALL = OUTCOME" line per result, a
% trap's outcome shown as just "trap" (the native run cannot tell why).
% Only Fil-C mode compares unreachable, which panics there.
expected_lines([]) --> [].
expected_lines([r(Fn, Args, Outcome)|Results]) -->
    { call_text(Fn, Args, CallText),
      (   Outcome = trap(_) -> Text = trap
      ;   Outcome == unreachable -> Text = trap
      ;   outcome_text(Outcome, Text)
      ) },
    fmt("~w = ~w~n", [CallText, Text]),
    expected_lines(Results).

% harness(+Mode, +Module, +Results)//: a C program that calls Module's
% functions as Results do and prints what expected_lines//1 prints.
harness(plain, Module, Results) -->
    "#include <stdio.h>\n#include <stdint.h>\n\n",
    { results_fns(Results, Fns) },
    prototypes(Fns, Module),
    "\nint main(void) {\n",
    harness_calls(Results, Module, labelled),
    "    return 0;\n}\n".
% Fil-C: one run per process, selected by argv[1], since a trap ends the
% process. The call text is printed first, so a trap leaves it unfinished.
harness(filc, Module, Results) -->
    "#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n\n",
    { results_fns(Results, Fns) },
    prototypes(Fns, Module),
    "\nint main(int argc, char **argv) {\n    switch (atoi(argv[1])) {\n",
    filc_cases(Results, 0, Module),
    "    }\n    return 0;\n}\n".

% results_fns(+Results, -Fns): Fns is the ordset of the functions
% Results call.
results_fns(Results, Fns) :-
    findall(Fn, member(r(Fn, _, _), Results), Fns0),
    sort(Fns0, Fns).

% filc_cases(+Results, +I, +Module)//: the switch cases I, I+1, ... of
% the Fil-C harness, one per result.
filc_cases([], _, _) --> [].
filc_cases([Result|Results], I, Module) -->
    { Result = r(Fn, Args, _),
      call_text(Fn, Args, CallText) },
    fmt("    case ~w: fputs(\"~w = \", stdout); fflush(stdout);~n",
        [I, CallText]),
    harness_calls([Result], Module, bare),
    "        break;\n",
    { I1 is I + 1 },
    filc_cases(Results, I1, Module).

% prototypes(+Fns, +Module)//: an extern C declaration of each of Fns.
prototypes([], _) --> [].
prototypes([Fn|Fns], Module) -->
    { func_named(Module, Fn, func(_, _, Ret, Params, _)),
      c_type(Ret, RetType),
      findall(Type, ( member(param(Class, _), Params), c_type(Class, Type) ),
              ParamTypes),
      types_text(ParamTypes, ParamText) },
    fmt("extern ~w ~w(~w);~n", [RetType, Fn, ParamText]),
    prototypes(Fns, Module).

% types_text(+Types, -Text): Text is the C parameter list of Types.
types_text([], void).
types_text([Type|Types], Text) :-
    atomic_list_concat([Type|Types], ', ', Text).

% c_type(?Class, ?Type): Type is the C type of the IR class.
c_type(w, uint32_t).
c_type(l, uint64_t).
c_type(void, void).

% harness_calls(+Results, +Module, +Style)//: Style labelled prints
% "CALL = ret N" lines from one main; bare prints "ret N" inside a case.
harness_calls([], _, _) --> [].
harness_calls([r(Fn, Args, _)|Results], Module, Style) -->
    { func_named(Module, Fn, func(_, _, Ret, _, _)),
      call_text(Fn, Args, CallText),
      findall(CArg, ( member(X, Args), format(atom(CArg), '~wull', [X]) ),
              CArgs),
      atomic_list_concat(CArgs, ', ', CArgText) },
    harness_call(Style, Ret, Fn, CArgText, CallText),
    harness_calls(Results, Module, Style).

% harness_call(+Style, +Ret, +Fn, +CArgText, +CallText)//: the line of
% harness_calls//3 for one call of Fn, which returns Ret.
harness_call(Style, Ret, Fn, CArgText, CallText) -->
    { ret_result(Ret, Result) },
    style_call(Style, Result, Fn, CArgText, CallText).

% ret_result(?Ret, ?Result): a function that returns Ret has a Result of
% none or value.
ret_result(void, none).
ret_result(w, value).
ret_result(l, value).
ret_result(p, value).
ret_result(tuple(_), value).

% style_call(+Style, +Result, +Fn, +CArgText, +CallText)//: as
% harness_call//5, for a call with Result.
style_call(bare, Result, Fn, CArgText, _) -->
    bare_call(Result, Fn, CArgText).
style_call(labelled, Result, Fn, CArgText, CallText) -->
    labelled_call(Result, Fn, CArgText, CallText).

% bare_call(+Result, +Fn, +CArgText)//: a case's line for a call of Fn.
bare_call(none, Fn, CArgText) -->
    fmt("        ~w(~w); puts(\"ret\");~n", [Fn, CArgText]).
bare_call(value, Fn, CArgText) -->
    fmt("        printf(\"ret %llu\\n\", (unsigned long long)~w(~w));~n",
        [Fn, CArgText]).

% labelled_call(+Result, +Fn, +CArgText, +CallText)//: main's line for
% a call of Fn.
labelled_call(none, Fn, CArgText, CallText) -->
    fmt("    ~w(~w); printf(\"%s = ret\\n\", \"~w\");~n",
        [Fn, CArgText, CallText]).
labelled_call(value, Fn, CArgText, CallText) -->
    fmt("    printf(\"%s = ret %llu\\n\", \"~w\", (unsigned long long)~w(~w));~n",
        [CallText, Fn, CArgText]).

%% Runs

% file_runs(+File, -Runs): Runs are the run(Fn, Args) facts of IR File,
% in order.
file_runs(File, Runs) :- read_ir_file(File, _, Runs).

% library(format)'s format_//2 raises type_error(list, '') for an argument
% of '' (Trealla 12f4cbd), which a call with no arguments produces.
% fmt(+Format, +Args)//: the characters format/3 makes of Format and Args.
fmt(Format, Args) -->
    { format(chars(Cs), Format, Args) },
    seq(Cs).
