/*  NFB, the nanofil bytecode: a module of ir.pl written as little-endian
    32-bit words in a sectioned container, and read back
    (docs/nfb.md). The encoding is a function of the module, and the
    reader accepts only its image, so the words are the module's
    identity.

    One table, nfb_form/3, states every instruction: its opcode, its
    term with the parts as variables, and the fields its words hold
    in order. The writer reads the table with the term given, the
    reader with the opcode given, so the two directions cannot
    disagree about a layout. module_nfb/2 is the relation between a
    module and its words; it runs either way, and its reading checks
    that writing the module gives the very words it read.

    ## The container

    | Words | Hold |
    |---|---|
    | header | magic `0x0042464E`, version, flags (stage, mode, ordered), section count |
    | STRINGS (1) | symbol names and `loc` files, sorted bytes |
    | CONSTANTS (2) | constants an operand word cannot hold, sorted, 3 words each |
    | SYMBOLS (3) | defined symbols in item order, then the named-only sorted |
    | DATA (4), FUNCTIONS (5) | the data objects and the function bodies, in symbol order |
    | NAMES (0x100) | the names of temporaries, labels and locals, as terms |
    | CONTEXT (0x101) | the `context/2` items and where they stood |

    ## Ids

    A temporary's id is its place among the function's first
    definitions: the parameters, then each definition in stream
    order. A later definition of the same temporary (ir.pl's IR is
    not strict SSA) is preceded by a `rebind` word naming its id.
    Blocks and named locals are numbered in stream order. Without
    NAMES, the reader names each by its id, an integer.
*/
:- module(nfb, [module_nfb/2, module_nfb/3, nfb_core/2, write_nfb_file/2,
                read_nfb_file/2, nfb_form/3, nfb_code/3]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(dcgs)).
:- use_module(ir, [module_mode/2, module_stage/2]).

%% The table

%! nfb_code(?Enum, ?Term, ?Code) is nondet.
%
%  Code is the word that stands for Term in a field of enumeration
%  Enum. Classes and widths share codes, so that a store's width and a
%  load's type read like the class they hold.
nfb_code(class, w, 1). nfb_code(class, l, 2). nfb_code(class, s, 3).
nfb_code(class, d, 4). nfb_code(class, x, 5). nfb_code(class, p, 6).
nfb_code(class, a, 7). nfb_code(class, f, 8).
nfb_code(width, W, C) :- nfb_code(class, W, C), C =< 6.
nfb_code(width, b, 9). nfb_code(width, h, 10).
nfb_code(load, T, C) :- member(T, [l, s, d, x, p]), nfb_code(class, T, C).
nfb_code(load, T, C) :- narrow_code(T, C).
nfb_code(ext, T, C) :- member(T, [s, d]), nfb_code(class, T, C).
nfb_code(ext, T, C) :- narrow_code(T, C).
nfb_code(cas, T, C) :- member(T, [l, p]), nfb_code(class, T, C).
nfb_code(cas, T, C) :- narrow_code(T, C).
nfb_code(cond, Cond, C) :-
    nth0(C, [eq, ne, sle, slt, sge, sgt, ule, ult, uge, ugt, le, lt, ge, gt, o, uo], Cond).
nfb_code(rights, read, 0). nfb_code(rights, write, 1).
nfb_code(bound, upper, 0). nfb_code(bound, lower, 1).
nfb_code(setjmp, setjmp, 0). nfb_code(setjmp, '_setjmp', 1). nfb_code(setjmp, sigsetjmp, 2).
nfb_code(effect, E, C) :-
    nth0(C, [aux_read, lower_resolve, address_read, aux_ensure, lower_barrier,
             rooted_reload, lower_write, address_write, atomic_read, atomic_write,
             atomic_cas], E).
nfb_code(flight, copy, 0). nfb_code(flight, add, 1). nfb_code(flight, sub, 2).
nfb_code(mnemonic, M, C) :-
    nth0(C, [cpuid, xgetbv, rdtsc, rdtscp, lfence, sfence, pause], M).
nfb_code(register, R, C) :- nth0(C, [a, b, c, d], R).
nfb_code(func_linkage, L, C) :- nth0(C, [export, local, weak], L).
nfb_code(data_linkage, L, C) :-
    nth0(C, [export, local, weak, ro(export), ro(local), ro(weak), tls(export),
             tls(local), init(ctor, priority), init(dtor, priority), init(ctor, none),
             init(dtor, none), extern(weak)], L).
nfb_code(alias_linkage, export, 0). nfb_code(alias_linkage, weak, 2).

narrow_code(T, C) :- nth0(I, [sw, uw, sh, uh, sb, ub], T), C is 16 + I.

%! nfb_form(?Opcode, ?Term, ?Fields) is nondet.
%
%  The instruction, phi or jump Term is written as the header word of
%  Opcode, then Fields in order. Each field names a part of Term:
%
%  | Field | Words |
%  |---|---|
%  | `def(D)` | none: `tmp(D)` takes the next temporary id |
%  | `class(K)`, `enum(E, X)` | one code (nfb_code/3) |
%  | `u32(N)`, `i64(N)` | N as one word, or as two (low, high), signed |
%  | `opnd(V)` | an operand word: a temporary, constant or symbol |
%  | `label(L)`, `target(T)` | a block index; for a target shifted left, bit 0 for `poll` |
%  | `local(X)`, `local_def(X)` | a local's id; the definition writes none |
%  | `str(A)` | a STRINGS id |
%  | `result(R)` | a call's result word, defining its temporaries |
%  | `alt(X, Alts)` | a tag word, then the fields of the alternative Tag-X-Fields |
%  | `count(Xs, X, Fs)` | the length of Xs, then Fs for each element X |
%  | `rest(Xs, X, Fs)` | Fs for each element X, to the instruction's end |
%
%  Each opcode belongs to one group: 1 is the rebind prefix, 8 the
%  phi, 0x10 to 0x7F plain instructions and 0x80 to 0x8F jumps.
nfb_form(0x08, phi(tmp(D), K, Ps), [def(D), class(K), rest(Ps, L-V, [label(L), opnd(V)])]).
nfb_form(Code, let(tmp(D), K, Op, [A, B]), [def(D), class(K), opnd(A), opnd(B)]) :-
    binary_op(Code, Op).
nfb_form(Code, let(tmp(D), K, Op, [A]), [def(D), class(K), opnd(A)]) :-
    unary_op(Code, Op).
nfb_form(0x38, let(tmp(D), K, cmp(C, K1), [A, B]),
         [def(D), class(K), enum(cond, C), class(K1), opnd(A), opnd(B)]).
nfb_form(0x39, let(tmp(D), K, ext(T), [A]), [def(D), class(K), enum(ext, T), opnd(A)]).
nfb_form(0x3A, let(tmp(D), K, load(T), [A]), [def(D), class(K), enum(load, T), opnd(A)]).
nfb_form(0x3B, let(tmp(D), K, alloc(Al), [A]), [def(D), class(K), u32(Al), opnd(A)]).
nfb_form(0x3C, let(tmp(D), K, va_args, [A]), [def(D), class(K), opnd(A)]).
nfb_form(0x3D, let(tmp(D), K, va_arg, [A]), [def(D), class(K), opnd(A)]).
nfb_form(0x3E, let(tmp(D), K, setjmp(J), [A, B]),
         [def(D), class(K), enum(setjmp, J), opnd(A), opnd(B)]).
nfb_form(0x3F, let(tmp(D), K, atomic_load(p), [A]), [def(D), class(K), opnd(A)]).
nfb_form(0x40, let(tmp(D), K, cas(T), [A, B, C]),
         [def(D), class(K), enum(cas, T), opnd(A), opnd(B), opnd(C)]).
nfb_form(0x50, let(tmp(D), K, check(Lo, Hi, R, Al), [P]),
         [def(D), class(K), i64(Lo), i64(Hi), enum(rights, R), u32(Al), opnd(P)]).
nfb_form(0x51, let(tmp(D), K, check_ahead(Lo, Hi, R, Al, AHi), [P]),
         [def(D), class(K), i64(Lo), i64(Hi), enum(rights, R), u32(Al), i64(AHi), opnd(P)]).
nfb_form(Code, let(tmp(D), K, Op, [A, B]),
         [def(D), class(K), i64(Lo), i64(Hi), enum(rights, R), u32(Al), opnd(A), opnd(B)]) :-
    range_op(Code, Op, Lo, Hi, R, Al).
nfb_form(0x53, let(tmp(D), K, renew_hull(Lo, Hi, R, Al), [A, B, C]),
         [def(D), class(K), i64(Lo), i64(Hi), enum(rights, R), u32(Al), opnd(A), opnd(B), opnd(C)]).
nfb_form(0x54, let(tmp(D), K, half_check(Bd, Lo, Hi, R, Al), [A, B]),
         [def(D), class(K), enum(bound, Bd), i64(Lo), i64(Hi), enum(rights, R), u32(Al),
          opnd(A), opnd(B)]).
nfb_form(0x55, let(tmp(D), K, span_test(Lo, Hi), [P]), [def(D), class(K), i64(Lo), i64(Hi), opnd(P)]).
nfb_form(0x57, let(tmp(D), K, limit(Size), [P]), [def(D), class(K), u32(Size), opnd(P)]).
nfb_form(0x59, let(tmp(D), K, check_local(X, Off, Bytes, R, Al), []),
         [def(D), class(K), local(X), i64(Off), i64(Bytes), enum(rights, R), u32(Al)]).
nfb_form(0x5A, let(tmp(D), K, check_function, [P]), [def(D), class(K), opnd(P)]).
nfb_form(0x5B, let(tmp(D), K, raw_load(T, Off), [A]),
         [def(D), class(K), enum(load, T), i64(Off), opnd(A)]).
nfb_form(0x5C, let(tmp(D), K, raw_load_pointer(Off, Es), [A]),
         [def(D), class(K), i64(Off), opnd(A), rest(Es, E, [enum(effect, E)])]).
nfb_form(0x5D, let(tmp(D), K, raw_cas(T, Off), [A, B, C]),
         [def(D), class(K), enum(cas, T), i64(Off), opnd(A), opnd(B), opnd(C)]).
nfb_form(0x60, store(W, V, A), [enum(width, W), opnd(V), opnd(A)]).
nfb_form(0x61, atomic_store(p, V, A), [opnd(V), opnd(A)]).
nfb_form(0x62, fence, []).
nfb_form(0x63, access(R, A, Size, Al), [enum(rights, R), u32(Size), u32(Al), opnd(A)]).
nfb_form(0x64, local_alloc(X, Size), [local_def(X), i64(Size)]).
nfb_form(0x65, local_load(tmp(D), K, T, X, Off),
         [def(D), class(K), enum(load, T), local(X), i64(Off)]).
nfb_form(0x66, local_store(W, V, X, Off), [enum(width, W), local(X), i64(Off), opnd(V)]).
nfb_form(0x67, call(Res, F, Args), [result(Res), opnd(F), rest(Args, arg(K, V), [class(K), opnd(V)])]).
nfb_form(0x68, asm_fixed(M, Ins, Outs),
         [enum(mnemonic, M), count(Ins, R-V, [enum(register, R), opnd(V)]),
          rest(Outs, R1-tmp(D), [enum(register, R1), def(D)])]).
nfb_form(0x69, loc(File, Line), [str(File), u32(Line)]).
nfb_form(0x70, touch(V), [opnd(V)]).
nfb_form(0x71, raw_call(Res, F, Args),
         [result(Res), opnd(F), rest(Args, arg(K, V), [class(K), opnd(V)])]).
nfb_form(0x72, flight(tmp(D), Op, Args, Lower),
         [def(D), enum(flight, Op), alt(Lower, [0-none-[], 1-lower(P)-[opnd(P)]]),
          rest(Args, X, [alt(X, [1-address(Q)-[opnd(Q)], 0-V-[opnd(V)]])])]).
nfb_form(0x73, raw_store(W, Off, V, A), [enum(width, W), i64(Off), opnd(V), opnd(A)]).
nfb_form(0x74, raw_store_pointer(Off, V, A, Es),
         [i64(Off), opnd(V), opnd(A), rest(Es, E, [enum(effect, E)])]).
nfb_form(0x80, goto(T), [target(T)]).
nfb_form(0x81, branch(V, T1, T2), [opnd(V), target(T1), target(T2)]).
nfb_form(0x82, ret(V), [opnd(V)]).
nfb_form(0x83, rets(Vs), [rest(Vs, V, [opnd(V)])]).
nfb_form(0x84, ret, []).
nfb_form(0x85, unreachable, []).

binary_op(Code, Op) :-
    nth0(I, [add, sub, mul, div, udiv, rem, urem, and, or, xor, sar, shr, shl], Op),
    Code is 0x10 + I.
unary_op(Code, Op) :-
    nth0(I, [neg, copy, cast, truncd, truncx, ptoi, itop, stosi, stoui, dtosi, dtoui,
             xtosi, xtoui, swtof, uwtof, sltof, ultof, sqrt], Op),
    Code is 0x20 + I.
range_op(0x52, renew(Lo, Hi, R, Al), Lo, Hi, R, Al).
range_op(0x56, renew_if(Lo, Hi, R, Al), Lo, Hi, R, Al).
range_op(0x58, check_limit(Lo, Hi, R, Al), Lo, Hi, R, Al).

rebind_opcode(0x01).

% group(+Opcode, ?Group): phi, plain or jump.
group(C, G) :- opcode_group(C, G0), G = G0.
opcode_group(0x08, phi) :- !.
opcode_group(C, jump) :- C >= 0x80, !.
opcode_group(_, plain).

%% The relation

magic(0x0042464E).
version(0x00000001).

%! module_nfb(?Module, ?Words) is semidet.
%
%  Words is the NFB of Module, NAMES and CONTEXT included. With Module
%  ground it writes; otherwise it reads Words, and fails unless they
%  are exactly what writing the module they decode to gives. Throws
%  nanofil_error(Msg) for a module that has no encoding.
module_nfb(M, Ws) :-
    (   ground(M) -> module_nfb(M, [names, context], Ws)
    ;   is_list(Ws), maplist(integer, Ws) -> read_words(Ws, M)
    ).

%! module_nfb(+Module, +Sides, -Words) is det.
%
%  Words is the NFB of Module with the side sections Sides, a subset of
%  `[names, context]`.
module_nfb(module(All), Sides, Ws) :-
    partition_items(All, 0, Items, Contexts),
    module_tables(Items, T),
    T = tables(Strs, Consts, Syms, _, _, _),
    phrase(funcs(Items, T, true, Ordered, NameRecs), FuncWs),
    phrase(data_objects(Items, T), DataWs),
    phrase(symbols_words(Syms, T), SymWs),
    phrase(strings_words(Strs), StrWs),
    phrase(constants_words(Consts), ConstWs),
    Core = [1-StrWs-Strs, 2-ConstWs-Consts, 3-SymWs-Syms, 4-DataWs-DataWs, 5-FuncWs-FuncWs],
    (   memberchk(names, Sides), NameRecs \== [] -> names_words(NameRecs, NamesWs), Side1 = [0x100-NamesWs]
    ;   Side1 = []
    ),
    (   memberchk(context, Sides), Contexts \== [] -> context_words(Contexts, CtxWs), Side2 = [0x101-CtxWs]
    ;   Side2 = []
    ),
    findall(Id-Ws1, ( member(Id-Ws1-Tab, Core), Tab \== [] ), CoreSecs),
    append(CoreSecs, Side1, Secs0), append(Secs0, Side2, Secs),
    length(Secs, NSecs),
    module_stage(module(Items), Stage), module_mode(module(Items), Mode),
    flags(Stage, Mode, Ordered, Flags),
    magic(Magic), version(Version),
    phrase(sections(Secs), SecWs),
    Ws = [Magic, Version, Flags, NSecs|SecWs].

flags(Stage, Mode, Ordered, Flags) :-
    ( Stage == checked -> S = 1 ; S = 0 ),
    ( Mode == filc -> F = 2 ; F = 0 ),
    ( Ordered == true -> O = 4 ; O = 0 ),
    Flags is S \/ F \/ O.

sections([]) --> [].
sections([Id-Ws|Ss]) --> { length(Ws, N) }, [Id, N], seq(Ws), sections(Ss).

%! nfb_core(+Words, -Core) is det.
%
%  Core is the NFB Words without its side sections: the words the
%  module's identity is taken over.
nfb_core(Ws, Core) :- sections_below(0x100, Ws, Core).

% sections_below(+Limit, +Ws, -Ws1): Ws with only its sections of ids
% below Limit.
sections_below(Limit, [Magic, Version, Flags, _|SecWs], [Magic, Version, Flags, N|Ws]) :-
    split_sections(SecWs, Secs),
    secs_below(Secs, Limit, Kept),
    length(Kept, N),
    phrase(sections(Kept), Ws).
secs_below([], _, []).
secs_below([Id-Ws|Ss], Limit, Kept) :-
    ( Id < Limit -> Kept = [Id-Ws|Kept1] ; Kept = Kept1 ),
    secs_below(Ss, Limit, Kept1).

split_sections([], []).
split_sections([Id, N|Ws0], [Id-Ws|Ss]) :-
    phrase(take(N, Ws), Ws0, Ws1), !,
    split_sections(Ws1, Ss).

% partition_items(+All, +I, -Items, -Contexts): the context items of
% All, each with the number of other items before it, and the rest.
partition_items([], _, [], []).
partition_items([C|Is], I, Items, [I-C|Cs]) :- C = context(_, _), !,
    partition_items(Is, I, Items, Cs).
partition_items([It|Is], I, [It|Items], Cs) :- I1 is I + 1, partition_items(Is, I1, Items, Cs).

%% Tables: strings, constants and symbols

% module_tables(+Items, -Tables): tables(Strs, Consts, Syms, SymIds,
% StrIds, ConstIds), each Ids an assoc from a name or constant to its id. Syms lists sym(Name, Kind, Item): the defined symbols in item
% order, then the named-only by name.
module_tables(Items, tables(Strs, Consts, Syms, SymIds, StrIds, ConstIds)) :-
    findall(sym(N, Kind, It), ( member(It, Items), item_symbol(It, N, Kind) ), Defined),
    findall(N, ( member(sym(N, _, _), Defined) ), DefNames),
    findall(P, ( member(It, Items), item_part(It, P) ), Parts0),
    sort(Parts0, Parts),
    findall(N-t, member(N, DefNames), Ds0), sort(Ds0, Ds), list_to_assoc(Ds, DefSet),
    findall(S, ( member(global(S), Parts), \+ get_assoc(S, DefSet, _) ), Named0),
    maplist(must_atom, DefNames), maplist(must_atom, Named0),
    sort_by_bytes(Named0, Named),
    findall(sym(N, named, none), member(N, Named), NamedSyms),
    append(Defined, NamedSyms, Syms),
    first_ids(Syms, 0, [], SymPairs), list_to_assoc(SymPairs, SymIds),
    findall(F, member(file(F), Parts), Files),
    maplist(must_atom, Files),
    append(DefNames, Named, SymNames), append(SymNames, Files, Strs0),
    sort(Strs0, Strs1), sort_by_bytes(Strs1, Strs),
    numbered(Strs, 0, StrPairs), list_to_assoc(StrPairs, StrIds),
    findall(C, ( member(const(C), Parts), \+ inline_const(C) ), Cs0),
    maplist(must_wide, Cs0),
    sort(Cs0, Consts),
    numbered(Consts, 0, CPairs), list_to_assoc(CPairs, ConstIds).


must_wide(N) :- integer(N), N >= -(1 << 95), N < 1 << 95, !.
must_wide(N) :- nfb_error('~q does not fit in 96 bits', [N]).

% first_ids(+Syms, +I, +Seen, -Pairs): each name's first symbol id.
first_ids([], _, Ps0, Ps) :- sort(Ps0, Ps1), first_keys(Ps1, Ps).
first_ids([sym(N, _, _)|Ss], I, Ps0, Ps) :- I1 is I + 1, first_ids(Ss, I1, [N-I|Ps0], Ps).
first_keys([], []).
first_keys([K-V|Ps], [K-V|Qs]) :- drop_key(K, Ps, Ps1), first_keys(Ps1, Qs).
drop_key(K, [K1-_|Ps], Qs) :- K1 == K, !, drop_key(K, Ps, Qs).
drop_key(_, Ps, Ps).

numbered([], _, []).
numbered([X|Xs], I, [X-I|Ps]) :- I1 is I + 1, numbered(Xs, I1, Ps).

must_atom(A) :- atom(A), !.
must_atom(A) :- nfb_error('a symbol or file name must be an atom: ~q', [A]).

sort_by_bytes(As, Sorted) :-
    findall(Bs-A, ( member(A, As), atom_bytes(A, Bs) ), Ps0),
    msort(Ps0, Ps), pairs_values_(Ps, Sorted).
pairs_values_([], []).
pairs_values_([_-V|Ps], [V|Vs]) :- pairs_values_(Ps, Vs).

item_symbol(func(N, _, _, _, _), N, func).
item_symbol(data(N, _, _, _), N, data).
item_symbol(alias(N, _, _), N, alias).

% item_part(+Item, -Part): the item refers to the symbol of global(S),
% uses the constant const(N) or the file file(F), as its forms say.
item_part(func(_, _, _, _, Bs), P) :-
    member(block(_, Phis, Insts, J), Bs),
    ( member(I, Phis) ; member(I, Insts) ; I = J ),
    form_of(I, _, Fields), phrase(fparts(Fields), Ps), member(P, Ps).
item_part(data(_, _, _, Its), P) :-
    member(It, Its), ( It = item(_, sym(S, _)), P = global(S) ; It = item(_, const(N)), P = const(N) ).
item_part(alias(_, _, S), global(S)).

fparts([]) --> [].
fparts([F|Fs]) --> fpart(F), fparts(Fs).
fpart(opnd(V)) --> !, ( { V = global(_) ; V = const(_) } -> [V] ; [] ).
fpart(str(A)) --> !, [file(A)].
fpart(rest(Xs, X, Fs)) --> !, elems_parts(Xs, X, Fs).
fpart(count(Xs, X, Fs)) --> !, elems_parts(Xs, X, Fs).
fpart(alt(X, Alts)) --> !, { member(_-X1-Fs, Alts), copy_term(X1-Fs, X-Fs1) -> true ; Fs1 = [] }, fparts(Fs1).
fpart(_) --> [].
elems_parts([], _, _) --> [].
elems_parts([E|Es], X, Fs) --> { copy_term(X-Fs, E-Fs1) -> true ; Fs1 = [] }, fparts(Fs1), elems_parts(Es, X, Fs).

inline_const(N) :- integer(N), N >= -(1 << 29), N < 1 << 29.

strings_words([]) --> !.
strings_words(Strs) --> { length(Strs, N) }, [N], strings(Strs).
strings([]) --> [].
strings([A|As]) --> { atom_bytes(A, Bs) }, bytes_words(Bs), strings(As).

constants_words([]) --> !.
constants_words(Cs) --> { length(Cs, N) }, [N], wides(Cs).
wides([]) --> [].
wides([C|Cs]) --> wide(C), wides(Cs).

symbols_words([], _) --> !.
symbols_words(Syms, T) --> { length(Syms, N) }, [N], symbols(Syms, T).
symbols([], _) --> [].
symbols([S|Ss], T) --> symbol(S, T), symbols(Ss, T).

symbol(sym(N, Kind, It), T) -->
    { T = tables(_, _, _, SymIds, StrIds, _), get_assoc(N, StrIds, Sid),
      symbol_kind(Kind, It, SymIds, K, L, Extra),
      W is K \/ L << 8 },
    [Sid, W, Extra].

symbol_kind(func, func(_, Lk, _, _, _), _, 0, L, 0) :- linkage_code(func_linkage, Lk, L).
symbol_kind(data, data(_, Lk, _, _), _, 1, L, Extra) :-
    (   Lk = init(W, P), integer(P) -> must_u32(P), linkage_code(data_linkage, init(W, priority), L), Extra = P
    ;   linkage_code(data_linkage, Lk, L), Extra = 0
    ).
symbol_kind(alias, alias(_, Lk, Tg), SymIds, 2, L, Extra) :-
    linkage_code(alias_linkage, Lk, L),
    ( get_assoc(Tg, SymIds, Extra) -> true ; nfb_error('no symbol ~q', [Tg]) ).
symbol_kind(named, _, _, 3, 0, 0).

% A priority stands for the integer in the symbol's extra word.
linkage_code(E, Lk, C) :- Lk \= init(_, priority), nfb_code(E, Lk, C), !.
linkage_code(E, init(W, priority), C) :- !, nfb_code(E, init(W, priority), C).
linkage_code(E, Lk, _) :- nfb_error('no ~w code for ~q', [E, Lk]).

%% Data

data_objects([], _) --> [].
data_objects([data(_, _, Al, Its)|Is], T) --> !,
    { must_u32(Al), length(Its, N) }, [Al, N], data_items(Its, T), data_objects(Is, T).
data_objects([_|Is], T) --> data_objects(Is, T).

data_items([], _) --> [].
data_items([It|Its], T) --> data_item(It, T), data_items(Its, T).

data_item(item(b, str(Cs)), _) --> !, { maplist(char_byte, Cs, Bs) }, [1], bytes_words(Bs).
data_item(item(W, const(N)), T) --> !, [0], code(width, W), const_word(N, T).
data_item(item(W, sym(S, Off)), T) --> !,
    { memberchk(W, [l, p]), T = tables(_, _, _, SymIds, _, _), get_assoc(S, SymIds, Sid) },
    [2], code(width, W), [Sid], i64(Off).
data_item(zero(N), _) --> !, [3], i64(N).
data_item(It, _) --> { nfb_error('no encoding for the data item ~q', [It]) }.

char_byte(C, B) :- atom(C), atom_length(C, 1), char_code(C, B), B =< 255, !.
char_byte(C, _) :- nfb_error('a str/1 element is not a byte: ~q', [C]).

%% Functions

% funcs(+Items, +T, +O0, -O, -NameRecs)//: the FUNCTIONS payload; O is
% true when O0 is and every body is ordered, and NameRecs the names of
% each function's temporaries, labels and locals.
funcs([], _, O, O, []) --> [].
funcs([func(N, _, Ret, Ps, Bs)|Is], T, O0, O, [Rec|Recs]) --> !,
    { catch(body_words(Ret, Ps, Bs, T, BodyWs, O1, Rec), nanofil_error(Msg),
            ( format(atom(Msg1), '~w: ~w', [N, Msg]), throw(nanofil_error(Msg1)) )),
      length(BodyWs, L),
      ( O1 == true -> O2 = O0 ; O2 = false ) },
    [L], seq(BodyWs),
    funcs(Is, T, O2, O, Recs).
funcs([_|Is], T, O0, O, Recs) --> funcs(Is, T, O0, O, Recs).

% fctx(Temps, Labels, Locals, Tables): a function's ids, assocs from
% each name to its id.
body_words(Ret, Ps, Bs, T, Ws, Ordered, names(TempNames, Labels, LocalNames)) :-
    func_ids(Ps, Bs, Temps, NT, TempNames, Labels, LabelIds, Locals, NL, LocalNames),
    length(Ps, NP), length(Bs, NB),
    Ctx = fctx(Temps, LabelIds, Locals, T),
    maplist(param_class, Ps, PKs),
    phrase(blocks(Bs, 0, Ctx, NP, _, true, Ordered), Stream),
    phrase(( ret_word(Ret), [NP], seq(PKs), [NB, NT, NL], seq(Stream) ), Ws).

param_class(param(K, tmp(_)), C) :- memberchk(K, [w, l, p, s, d]), nfb_code(class, K, C), !.
param_class(P, _) :- nfb_error('no encoding for the parameter ~q', [P]).

ret_word(void) --> !, [0].
ret_word(tuple([K1, K2])) --> !, { nfb_code(class, K1, C1), nfb_code(class, K2, C2), W is 0x100 + 16 * C1 + C2 }, [W].
ret_word(K) --> { nfb_code(class, K, C) }, !, [C].
ret_word(R) --> { nfb_error('no encoding for the return type ~q', [R]) }.

% func_ids(...): each temporary's id by first definition, each label's
% block index and each local's id, and the names in id order.
func_ids(Ps, Bs, Temps, NT, TempNames, Labels, LabelIds, Locals, NL, LocalNames) :-
    findall(D, member(param(_, tmp(D)), Ps), PDs),
    findall(D, ( member(block(_, Phis, Insts, _), Bs),
                 ( member(I, Phis) ; member(I, Insts) ),
                 inst_defs(I, D) ), BDs),
    append(PDs, BDs, Ds),
    length(PDs, NP), sort(PDs, SPDs), length(SPDs, NSP),
    ( NSP =:= NP -> true ; nfb_error('two parameters share a name', []) ),
    first_defs(Ds, TempNames),
    length(TempNames, NT), numbered(TempNames, 0, TPs), list_to_assoc(TPs, Temps),
    findall(L, member(block(L, _, _, _), Bs), Labels),
    unique(Labels, label), numbered(Labels, 0, LPs), list_to_assoc(LPs, LabelIds),
    findall(X, ( member(block(_, _, Insts, _), Bs), member(local_alloc(X, _), Insts) ), LocalNames),
    unique(LocalNames, local), length(LocalNames, NL),
    numbered(LocalNames, 0, XPs), list_to_assoc(XPs, Locals).

unique(Xs, What) :-
    msort(Xs, S), sort(Xs, U), length(S, N), length(U, M),
    ( N =:= M -> true ; nfb_error('two ~ws share a name', [What]) ).

% first_defs(+Ds, -Firsts): Ds without the repeats, first occurrence kept.
first_defs(Ds, Firsts) :- first_defs(Ds, t, Firsts).
first_defs([], _, []).
first_defs([D|Ds], Seen0, Fs) :-
    (   Seen0 \== t, get_assoc(D, Seen0, _) -> Fs = Fs1, Seen = Seen0
    ;   ( Seen0 == t -> empty_assoc(E) ; E = Seen0 ), put_assoc(D, E, x, Seen), Fs = [D|Fs1]
    ),
    first_defs(Ds, Seen, Fs1).

% inst_defs(+Inst, -D): D is a temporary Inst defines, in order.
inst_defs(I, D) :-
    form_of(I, _, Fields), field_defs(Fields, Ds), member(D, Ds).

form_of(I, Code, Fields) :-
    (   nfb_form(Code, I, Fields) -> true
    ;   nfb_error('no encoding for ~q', [I])
    ).

field_defs(Fs, Ds) :- phrase(fdefs(Fs), Ds).
fdefs([]) --> [].
fdefs([F|Fs]) --> fdef(F), fdefs(Fs).
fdef(def(D)) --> !, [D].
fdef(result(R)) --> !, result_defs(R).
fdef(rest(Xs, X, Fs)) --> !, elems_defs(Xs, X, Fs).
fdef(count(Xs, X, Fs)) --> !, elems_defs(Xs, X, Fs).
fdef(alt(X, Alts)) --> !, { member(_-X1-Fs, Alts), copy_term(X1-Fs, X-Fs1) -> true ; Fs1 = [] }, fdefs(Fs1).
fdef(_) --> [].
elems_defs([], _, _) --> [].
elems_defs([E|Es], X, Fs) --> { copy_term(X-Fs, E-Fs1) -> true ; Fs1 = [] }, fdefs(Fs1), elems_defs(Es, X, Fs).
result_defs(void) --> [].
result_defs(result(tmp(D), _)) --> [D].
result_defs(tuple(Rs)) --> { findall(D, member(result(tmp(D), _), Rs), Ds) }, seq(Ds).

% blocks(+Bs, +I, +Ctx, +N0, -N, +O0, -O)//: the stream of the blocks
% from index I, N0 temporaries defined before them, O whether ordered.
blocks([], _, _, N, N, O, O) --> [].
blocks([block(_, Phis, Insts, J)|Bs], I, Ctx, N0, N, O0, O) -->
    ( { I =:= 0, Phis \== [] } -> { nfb_error('the entry block has phis', []) } ; [] ),
    insts(Phis, phi, I, Ctx, N0, N1, O0, O1),
    insts(Insts, plain, I, Ctx, N1, N2, O1, O2),
    insts([J], jump, I, Ctx, N2, N3, O2, O3),
    { I1 is I + 1 },
    blocks(Bs, I1, Ctx, N3, N, O3, O).

insts([], _, _, _, N, N, O, O) --> [].
insts([X|Xs], G, B, Ctx, N0, N, O0, O) -->
    inst(X, G, B, Ctx, N0, N1, O0, O1),
    insts(Xs, G, B, Ctx, N1, N, O1, O).

inst(X, G, B, Ctx, N0, N, O0, O) -->
    { form_of(X, Code, Fields),
      ( group(Code, G) -> true ; nfb_error('~q is not a ~w', [X, G]) ),
      phrase(fields(Fields, Ctx, B, Defs, [], Uses, [], Polls, []), Ws),
      Ctx = fctx(Temps, _, _, _),
      rebinds(Defs, Temps, N0, N, Rebinds),
      ( ordered_uses(G, Uses, N0), ordered_targets(Polls, B) -> O = O0 ; O = false ),
      length(Ws, L0), L is L0 + 1, must_length(L), Header is Code \/ L << 16 },
    (   { member(R, Rebinds), R > 0 }
    ->  { rebind_opcode(RC), length(Rebinds, RL0), RL is RL0 + 1, RH is RC \/ RL << 16 },
        [RH], seq(Rebinds)
    ;   []
    ),
    [Header], seq(Ws).

must_length(L) :- L < 1 << 16, !.
must_length(L) :- nfb_error('an instruction of ~w words is longer than 65535', [L]).

% rebinds(+Defs, +Temps, +N0, -N, -Words): each definition's rebind
% word, 0 for a first definition (it takes the next id, N0) or Id+1.
rebinds([], _, N, N, []).
rebinds([D|Ds], Temps, N0, N, [W|Ws]) :-
    get_assoc(D, Temps, Id),
    (   Id =:= N0 -> W = 0, N1 is N0 + 1
    ;   W is Id + 1, N1 = N0
    ),
    rebinds(Ds, Temps, N1, N, Ws).

ordered_uses(phi, _, _) :- !.
ordered_uses(_, Uses, N0) :- forall(member(U, Uses), U < N0).
ordered_targets(Polls, B) :- forall(member(I-P, Polls), ( I > B ; P == 1 )).

% fields(+Fields, +Ctx, +B, Defs, Uses, Polls)//: the words of Fields.
fields([], _, _, Ds, Ds, Us, Us, Ps, Ps) --> [].
fields([F|Fs], Ctx, B, Ds0, Ds, Us0, Us, Ps0, Ps) -->
    field(F, Ctx, B, Ds0, Ds1, Us0, Us1, Ps0, Ps1),
    fields(Fs, Ctx, B, Ds1, Ds, Us1, Us, Ps1, Ps).

field(def(D), _, _, [D|Ds], Ds, Us, Us, Ps, Ps) --> !.
field(local_def(_), _, _, Ds, Ds, Us, Us, Ps, Ps) --> !.
field(class(K), _, _, Ds, Ds, Us, Us, Ps, Ps) --> !, code(class, K).
field(enum(E, X), _, _, Ds, Ds, Us, Us, Ps, Ps) --> !, code(E, X).
field(u32(N), _, _, Ds, Ds, Us, Us, Ps, Ps) --> !, { must_u32(N) }, [N].
field(i64(N), _, _, Ds, Ds, Us, Us, Ps, Ps) --> !, i64(N).
field(opnd(V), Ctx, _, Ds, Ds, Us0, Us, Ps, Ps) --> !, operand(V, Ctx, Us0, Us).
field(label(L), fctx(_, Ls, _, _), _, Ds, Ds, Us, Us, Ps, Ps) --> !, { label_index(L, Ls, I) }, [I].
field(target(T), fctx(_, Ls, _, _), _, Ds, Ds, Us, Us, [I-P|Ps], Ps) --> !,
    { ( T = poll(L) -> P = 1 ; L = T, P = 0 ), label_index(L, Ls, I), W is I << 1 \/ P }, [W].
field(local(X), fctx(_, _, Xs, _), _, Ds, Ds, Us, Us, Ps, Ps) --> !,
    { get_assoc(X, Xs, I) -> true ; nfb_error('no local named ~q', [X]) }, [I].
field(str(A), fctx(_, _, _, tables(_, _, _, _, Strs, _)), _, Ds, Ds, Us, Us, Ps, Ps) --> !,
    { must_atom(A), get_assoc(A, Strs, I) }, [I].
field(result(R), _, _, Ds0, Ds, Us, Us, Ps, Ps) --> !, { phrase(result_defs(R), Ds0, Ds) }, result_word(R).
field(alt(X, Alts), Ctx, B, Ds0, Ds, Us0, Us, Ps0, Ps) --> !,
    { member(Tag-X1-Fs, Alts), copy_term(X1-Fs, X-Fs1) -> true ; nfb_error('no alternative for ~q', [X]) },
    [Tag], fields(Fs1, Ctx, B, Ds0, Ds, Us0, Us, Ps0, Ps).
field(count(Xs, X, Fs), Ctx, B, Ds0, Ds, Us0, Us, Ps0, Ps) --> !,
    { length(Xs, N) }, [N], elems(Xs, X, Fs, Ctx, B, Ds0, Ds, Us0, Us, Ps0, Ps).
field(rest(Xs, X, Fs), Ctx, B, Ds0, Ds, Us0, Us, Ps0, Ps) --> !,
    { is_list(Xs) -> true ; nfb_error('not a list: ~q', [Xs]) },
    elems(Xs, X, Fs, Ctx, B, Ds0, Ds, Us0, Us, Ps0, Ps).

elems([], _, _, _, _, Ds, Ds, Us, Us, Ps, Ps) --> [].
elems([E|Es], X, Fs, Ctx, B, Ds0, Ds, Us0, Us, Ps0, Ps) -->
    { copy_term(X-Fs, X1-Fs1), ( X1 = E -> true ; nfb_error('no encoding for the element ~q', [E]) ) },
    fields(Fs1, Ctx, B, Ds0, Ds1, Us0, Us1, Ps0, Ps1),
    elems(Es, X, Fs, Ctx, B, Ds1, Ds, Us1, Us, Ps1, Ps).

label_index(L, Ls, I) :- get_assoc(L, Ls, I), !.
label_index(L, _, _) :- nfb_error('no block labelled ~q', [L]).

result_word(void) --> !, [0].
result_word(result(tmp(_), K)) --> !, code(class, K).
result_word(tuple([result(tmp(_), K1), result(tmp(_), K2)])) --> !,
    { nfb_code(class, K1, C1), nfb_code(class, K2, C2), W is 0x100 + 16 * C1 + C2 }, [W].
result_word(R) --> { nfb_error('no encoding for the call result ~q', [R]) }.

code(E, X) --> { nfb_code(E, X, C) }, !, [C].
code(E, X) --> { nfb_error('no ~w code for ~q', [E, X]) }.

operand(tmp(N), fctx(Temps, _, _, _), [Id|Us], Us) --> !,
    { get_assoc(N, Temps, Id) -> true ; nfb_error('tmp(~q) is read but never defined', [N]) },
    { W is Id << 2 }, [W].
operand(const(N), fctx(_, _, _, T), Us, Us) --> !, const_word(N, T).
operand(global(S), fctx(_, _, _, tables(_, _, _, SymIds, _, _)), Us, Us) --> !,
    { get_assoc(S, SymIds, I), W is I << 2 \/ 3 }, [W].
operand(V, _, _, _) --> { nfb_error('no encoding for the value ~q', [V]) }.

const_word(N, _) --> { inline_const(N) }, !, { W is (N mod (1 << 30)) << 2 \/ 1 }, [W].
const_word(N, tables(_, _, _, _, _, Cs)) --> { integer(N), get_assoc(N, Cs, I), !, W is I << 2 \/ 2 }, [W].
const_word(N, _) --> { nfb_error('no encoding for the constant ~q', [N]) }.

%% Words

must_u32(N) :- integer(N), N >= 0, N < 1 << 32, !.
must_u32(N) :- nfb_error('~q does not fit in a word', [N]).

i64(N) -->
    { ( integer(N), N >= -(1 << 63), N < 1 << 63 ) -> true ; nfb_error('~q does not fit in 64 bits', [N]) },
    { U is N mod (1 << 64), Lo is U /\ 0xFFFFFFFF, Hi is U >> 32 }, [Lo, Hi].

% wide(N)//: N, from -2^95 to 2^95-1, as three words, low first.
wide(N) -->
    { ( integer(N), N >= -(1 << 95), N < 1 << 95 ) -> true ; nfb_error('~q does not fit in 96 bits', [N]) },
    { U is N mod (1 << 96), W0 is U /\ 0xFFFFFFFF, W1 is (U >> 32) /\ 0xFFFFFFFF, W2 is U >> 64 },
    [W0, W1, W2].

% bytes_words(+Bs)//: the length of Bs, then Bs four to a word, low
% byte first, the last word padded with zero bytes.
bytes_words(Bs) --> { length(Bs, N) }, [N], packed(Bs).
packed([]) --> !.
packed(Bs) -->
    { take4(Bs, B0, B1, B2, B3, Rest), W is B0 \/ B1 << 8 \/ B2 << 16 \/ B3 << 24 },
    [W], packed(Rest).
take4([B0, B1, B2, B3|R], B0, B1, B2, B3, R) :- !.
take4(Bs, B0, B1, B2, B3, []) :- append(Bs, Pad, [B0, B1, B2, B3]), maplist(=(0), Pad).

% atom_bytes(+A, -Bs): the UTF-8 bytes of the atom A.
atom_bytes(A, Bs) :- atom_codes(A, Cs), phrase(utf8(Cs), Bs).
utf8([]) --> [].
utf8([C|Cs]) --> utf8_code(C), utf8(Cs).
utf8_code(C) --> { C < 0x80 }, !, [C].
utf8_code(C) --> { C < 0x800 }, !, { B0 is 0xC0 \/ C >> 6, B1 is 0x80 \/ C /\ 0x3F }, [B0, B1].
utf8_code(C) --> { C < 0x10000 }, !,
    { B0 is 0xE0 \/ C >> 12, B1 is 0x80 \/ (C >> 6) /\ 0x3F, B2 is 0x80 \/ C /\ 0x3F }, [B0, B1, B2].
utf8_code(C) -->
    { B0 is 0xF0 \/ C >> 18, B1 is 0x80 \/ (C >> 12) /\ 0x3F,
      B2 is 0x80 \/ (C >> 6) /\ 0x3F, B3 is 0x80 \/ C /\ 0x3F }, [B0, B1, B2, B3].

nfb_error(Fmt, Args) :-
    format(atom(Msg), Fmt, Args),
    atom_concat('nfb: ', Msg, Msg1),
    throw(nanofil_error(Msg1)).

%% Side sections: terms

% A side section's terms are written with their own string pool: the
% atoms and functors they use, sorted by bytes. A term is a tag word
% and its parts: 0 an integer (wide/1), 1 an atom, 2 a compound (its
% functor, its arity, its arguments), 3 a proper list (its length, its
% elements).
side_terms_words(Terms, Body) :-
    findall(A, ( member(T, Terms), term_atom(T, A) ), As0),
    sort(As0, As1), sort_by_bytes(As1, Pool),
    numbered(Pool, 0, Ps), list_to_assoc(Ps, Ids),
    phrase(strings_words(Pool), PoolWs0),
    ( Pool == [] -> PoolWs = [0] ; PoolWs = PoolWs0 ),
    Body = Ids-PoolWs.

term_atom(T, A) :- is_list(T), !, member(X, T), term_atom(X, A).
term_atom(T, T) :- atom(T), !.
term_atom(T, A) :- compound(T), T =.. [F|As], ( A = F ; member(X, As), term_atom(X, A) ).

side_term(T, Ids) --> { is_list(T) }, !, { length(T, N) }, [3, N], side_terms(T, Ids).
side_term(T, Ids) --> { atom(T) }, !, { get_assoc(T, Ids, I) }, [1, I].
side_term(T, _) --> { integer(T) }, !, [0], wide(T).
side_term(T, Ids) --> { compound(T), compound_name_arity(T, _, N), N > 0 }, !,
    { T =.. [F|As], get_assoc(F, Ids, I) }, [2, I, N], side_terms(As, Ids).
side_term(T, _) --> { nfb_error('a side section cannot hold ~q', [T]) }.
side_terms([], _) --> [].
side_terms([T|Ts], Ids) --> side_term(T, Ids), side_terms(Ts, Ids).

% names_words(+Recs, -Ws): NAMES: the pool, then per function its
% temporaries', labels' and locals' names, each list in id order.
names_words(Recs, Ws) :-
    findall(N, ( member(names(Ts, Ls, Xs), Recs), ( member(N, Ts) ; member(N, Ls) ; member(N, Xs) ) ), All),
    side_terms_words(All, Ids-PoolWs),
    phrase(( seq(PoolWs), names_recs(Recs, Ids) ), Ws).
names_recs([], _) --> [].
names_recs([names(Ts, Ls, Xs)|Rs], Ids) -->
    name_list(Ts, Ids), name_list(Ls, Ids), name_list(Xs, Ids), names_recs(Rs, Ids).
name_list(Ns, Ids) --> { length(Ns, N) }, [N], side_list(Ns, Ids).
side_list([], _) --> [].
side_list([T|Ts], Ids) --> side_term(T, Ids), side_list(Ts, Ids).

% context_words(+Contexts, -Ws): CONTEXT: the pool, the count, then
% each context item's position among the other items and its term.
context_words(Contexts, Ws) :-
    findall(C, member(_-C, Contexts), Cs),
    side_terms_words(Cs, Ids-PoolWs),
    length(Contexts, N),
    phrase(( seq(PoolWs), [N], context_list(Contexts, Ids) ), Ws).
context_list([], _) --> [].
context_list([P-C|Cs], Ids) --> [P], side_term(C, Ids), context_list(Cs, Ids).

%% Reading

% read_words(+Ws, -M): M is the module the NFB Ws encode; Ws must be
% exactly its encoding, with the side sections Ws has.
read_words(Ws, M) :-
    Ws = [Magic, Version, Flags, NSecs|SecWs],
    magic(Magic), version(Version),
    Flags /\ \7 =:= 0,
    split_sections(SecWs, Secs), length(Secs, NSecs),
    section_ids_increase(Secs, -1),
    forall(member(Id-_, Secs), ( Id >= 0x200 ; memberchk(Id, [1, 2, 3, 4, 5, 0x100, 0x101]) )),
    sec(1, Secs, [0], StrWs), sec(2, Secs, [0], ConstWs), sec(3, Secs, [0], SymWs),
    sec(4, Secs, [], DataWs), sec(5, Secs, [], FuncWs),
    phrase(read_strings(Strs), StrWs),
    phrase(read_constants(Consts), ConstWs),
    phrase(read_symbols(Syms0), SymWs),
    StrT =.. [s|Strs], ConstT =.. [c|Consts],
    maplist(symbol_name(StrT), Syms0, Syms),
    SymT =.. [y|Syms],
    (   memberchk(0x100-NamesWs, Secs) -> phrase(read_names(Names), NamesWs), Sides0 = [names]
    ;   Names = none, Sides0 = []
    ),
    (   memberchk(0x101-CtxWs, Secs) -> phrase(read_contexts(Contexts), CtxWs), Sides = [context|Sides0]
    ;   Contexts = [], Sides = Sides0
    ),
    R = r(StrT, ConstT, SymT),
    phrase(read_data(Syms, R, Datas), DataWs),
    phrase(read_funcs(Syms, R, Names, Funcs), FuncWs),
    build_items(Syms, SymT, Datas, Funcs, Items),
    insert_contexts(Contexts, 0, Items, All),
    M = module(All),
    catch(module_nfb(M, Sides, Ws1), nanofil_error(_), fail),
    sections_below(0x200, Ws, Ws2),
    Ws1 == Ws2.

section_ids_increase([], _).
section_ids_increase([Id-_|Ss], Prev) :- Id > Prev, section_ids_increase(Ss, Id).

% sec(+Id, +Secs, +Empty, -Ws): the payload of section Id, or Empty, the
% payload that means none, when it is absent.
sec(Id, Secs, _, Ws) :- memberchk(Id-Ws, Secs), !.
sec(_, _, Ws, Ws).

read_strings(Strs) --> [N], read_n(N, read_string, Strs).
read_string(A) --> read_bytes(Bs), { phrase(utf8_decode(Cs), Bs), atom_codes(A, Cs) }.
read_bytes(Bs) --> [N], { NW is (N + 3) // 4 }, read_n(NW, word_, Ws), { unpack(Ws, Bs0), length(Bs, N), append(Bs, _, Bs0) }.
word_(W) --> [W].
unpack([], []).
unpack([W|Ws], [B0, B1, B2, B3|Bs]) :-
    B0 is W /\ 0xFF, B1 is (W >> 8) /\ 0xFF, B2 is (W >> 16) /\ 0xFF, B3 is W >> 24,
    unpack(Ws, Bs).

utf8_decode([]) --> [].
utf8_decode(_) --> [B], { B >= 0xF8 }, !, { fail }.
utf8_decode([C|Cs]) --> [B0], { B0 < 0x80 }, !, { C = B0 }, utf8_decode(Cs).
utf8_decode([C|Cs]) --> [B0, B1], { B0 >= 0xC0, B0 < 0xE0 }, !,
    { C is (B0 /\ 0x1F) << 6 \/ (B1 /\ 0x3F) }, utf8_decode(Cs).
utf8_decode([C|Cs]) --> [B0, B1, B2], { B0 >= 0xE0, B0 < 0xF0 }, !,
    { C is (B0 /\ 0x0F) << 12 \/ (B1 /\ 0x3F) << 6 \/ (B2 /\ 0x3F),
      \+ ( C >= 0xD800, C =< 0xDFFF ) }, utf8_decode(Cs).
utf8_decode([C|Cs]) --> [B0, B1, B2, B3], { B0 >= 0xF0 }, !,
    { C is (B0 /\ 0x07) << 18 \/ (B1 /\ 0x3F) << 12 \/ (B2 /\ 0x3F) << 6 \/ (B3 /\ 0x3F),
      C =< 0x10FFFF }, utf8_decode(Cs).

read_n(0, _, []) --> !.
read_n(N, G, [X|Xs]) --> call(G, X), { N1 is N - 1 }, read_n(N1, G, Xs).

read_constants(Cs) --> [N], read_n(N, read_wide, Cs).
read_wide(N) --> [W0, W1, W2], { U is W0 \/ W1 << 32 \/ W2 << 64, ( U >= 1 << 95 -> N is U - (1 << 96) ; N = U ) }.
read_i64(N) --> [Lo, Hi], { U is Lo \/ Hi << 32, ( U >= 1 << 63 -> N is U - (1 << 64) ; N = U ) }.

read_symbols(Ss) --> [N], read_n(N, read_symbol, Ss).
read_symbol(sym(Sid, K, L, Extra)) --> [Sid, W, Extra], { K is W /\ 0xFF, L is W >> 8 }.

% table_arg(+I, +Table, ?X): X is the Ith element of a table the reader
% built with =.., which has no arguments when it is empty.
table_arg(I, T, X) :- compound(T), arg(I, T, X).

symbol_name(StrT, sym(Sid, K, L, E), sym(Name, K, L, E)) :- I is Sid + 1, table_arg(I, StrT, Name).

% read_data(+Syms, +R, -Datas)//: data(Name, Linkage, Align, Items) of
% each kind-1 symbol, in order.
read_data([], _, []) --> [].
read_data([sym(N, 1, L, E)|Ss], R, [data(N, Lk, Al, Its)|Ds]) --> !,
    { nfb_code(data_linkage, Lk0, L), ( Lk0 = init(W, priority) -> Lk = init(W, E) ; Lk = Lk0 ) },
    [Al, NI], read_n(NI, read_data_item(R), Its), read_data(Ss, R, Ds).
read_data([_|Ss], R, Ds) --> read_data(Ss, R, Ds).

read_data_item(_, item(b, str(Cs))) --> [1], !, read_bytes(Bs), { maplist(byte_char, Bs, Cs) }.
read_data_item(R, item(W, const(N))) --> [0], !, [CW], { nfb_code(width, W, CW) }, read_const(R, N).
read_data_item(R, item(W, sym(S, Off))) --> [2], !, [CW, Sid], { nfb_code(width, W, CW), sym_name(R, Sid, S) }, read_i64(Off).
read_data_item(_, zero(N)) --> [3], read_i64(N).

byte_char(B, C) :- char_code(C, B).

read_const(r(_, ConstT, _), N) --> [W], { const_value(W, ConstT, N) }.
const_value(W, _, N) :- W /\ 3 =:= 1, !, P is W >> 2, ( P >= 1 << 29 -> N is P - (1 << 30) ; N = P ).
const_value(W, ConstT, N) :- W /\ 3 =:= 2, I is (W >> 2) + 1, table_arg(I, ConstT, N).

sym_name(r(_, _, SymT), Sid, Name) :- I is Sid + 1, table_arg(I, SymT, sym(Name, _, _, _)).

% build_items(+Syms, +SymT, +Datas, +Funcs, -Items): the items in symbol
% order: each defined symbol's function, data or alias.
build_items([], _, [], [], []).
build_items([sym(_, 0, _, _)|Ss], SymT, Ds, [F|Fs], [F|Is]) :- !, build_items(Ss, SymT, Ds, Fs, Is).
build_items([sym(_, 1, _, _)|Ss], SymT, [D|Ds], Fs, [D|Is]) :- !, build_items(Ss, SymT, Ds, Fs, Is).
build_items([sym(N, 2, L, Tg)|Ss], SymT, Ds, Fs, [alias(N, Lk, TgN)|Is]) :- !,
    nfb_code(alias_linkage, Lk, L), I is Tg + 1, table_arg(I, SymT, sym(TgN, _, _, _)),
    build_items(Ss, SymT, Ds, Fs, Is).
build_items([sym(_, 3, _, _)|Ss], SymT, Ds, Fs, Is) :- build_items(Ss, SymT, Ds, Fs, Is).

insert_contexts([], _, Is, Is) :- !.
insert_contexts([P-C|Cs], I, Is, [C|All]) :- P =:= I, !, insert_contexts(Cs, I, Is, All).
insert_contexts(Cs, I, [It|Is], [It|All]) :- I1 is I + 1, insert_contexts(Cs, I1, Is, All).

% Side sections.
read_pool(PoolT) --> read_strings(Pool), { PoolT =.. [p|Pool] }.
read_side_term(P, T) --> [Tag], read_side_term(Tag, P, T).
read_side_term(0, _, N) --> read_wide(N).
read_side_term(1, P, A) --> [I], { I1 is I + 1, table_arg(I1, P, A) }.
read_side_term(2, P, T) --> [I, N], { I1 is I + 1, table_arg(I1, P, F) }, read_n(N, read_side_term(P), As), { T =.. [F|As] }.
read_side_term(3, P, T) --> [N], read_n(N, read_side_term(P), T).

read_names(names(Recs)) --> read_pool(P), read_name_recs(P, Recs).
read_name_recs(_, []) --> at_end, !.
read_name_recs(P, [names(Ts, Ls, Xs)|Rs]) -->
    [NT], read_n(NT, read_side_term(P), Ts), [NL], read_n(NL, read_side_term(P), Ls),
    [NX], read_n(NX, read_side_term(P), Xs), read_name_recs(P, Rs).

read_contexts(Cs) --> read_pool(P), [N], read_n(N, read_context(P), Cs).
read_context(P, Pos-C) --> [Pos], read_side_term(P, C).

% read_funcs(+Syms, +R, +Names, -Funcs)//: the function of each kind-0
% symbol, named from Names or by ids.
read_funcs(Syms, R, Names, Funcs) -->
    { ( Names = names(Recs) -> true ; Recs = none ) },
    read_funcs_(Syms, R, Recs, Funcs).
read_funcs_([], _, Recs, []) --> { Recs == none ; Recs == [] }, !.
read_funcs_([sym(N, 0, L, _)|Ss], R, Recs0, [F|Fs]) --> !,
    { ( Recs0 == none -> Rec = none, Recs = none ; Recs0 = [Rec|Recs] ),
      nfb_code(func_linkage, Lk, L) },
    [Len], take(Len, BodyWs),
    { phrase(read_body(R, Rec, N, Lk, F), BodyWs) },
    read_funcs_(Ss, R, Recs, Fs).
read_funcs_([_|Ss], R, Recs, Fs) --> read_funcs_(Ss, R, Recs, Fs).

read_body(R, Rec, Name, Lk, func(Name, Lk, Ret, Ps, Bs)) -->
    [RW], { read_ret(RW, Ret) },
    [NP], read_n(NP, word_, PKs),
    [NB, NT, NL],
    % Each block, definition and local takes a word of the stream at
    % least, so a count beyond its length is refused before it sizes a
    % table.
    lookahead(Rest),
    { length(Rest, Left), NB =< Left, NT - NP =< Left, NL =< Left,
      name_tables(Rec, NT, NB, NL, TN, LN, XN),
      numlist_(0, NP, PIds),
      maplist(read_param(TN), PKs, PIds, Ps),
      Ctx = dctx(TN, LN, XN, R) },
    read_blocks(0, NB, Ctx, NP, NT, 0, NL, Bs).

read_param(TN, C, Id, param(K, tmp(D))) :-
    nfb_code(class, K, C), memberchk(K, [w, l, p, s, d]), I is Id + 1, table_arg(I, TN, D).

read_ret(0, void) :- !.
read_ret(W, tuple([K1, K2])) :- W >= 0x100, !, C1 is (W - 0x100) >> 4, C2 is W /\ 15, nfb_code(class, K1, C1), nfb_code(class, K2, C2).
read_ret(W, K) :- nfb_code(class, K, W).

numlist_(N, N, []) :- !.
numlist_(I, N, [I|Is]) :- I1 is I + 1, numlist_(I1, N, Is).

% name_tables(+Rec, +NT, +NB, +NL, -TN, -LN, -XN): terms whose
% arguments are the names by id: from NAMES, or the ids themselves.
name_tables(none, NT, NB, NL, TN, LN, XN) :- !,
    numlist_(0, NT, Ts), numlist_(0, NB, Ls), numlist_(0, NL, Xs),
    TN =.. [t|Ts], LN =.. [l|Ls], XN =.. [x|Xs].
name_tables(names(Ts, Ls, Xs), NT, NB, NL, TN, LN, XN) :-
    length(Ts, NT), length(Ls, NB), length(Xs, NL),
    TN =.. [t|Ts], LN =.. [l|Ls], XN =.. [x|Xs].

% read_blocks(+I, +NB, +Ctx, +N0, +NT, +X0, +NL, -Bs)//: the blocks
% from index I; N0 temporaries and X0 locals defined before them.
read_blocks(NB, NB, _, NT, NT, NL, NL, []) --> !.
read_blocks(I, NB, Ctx, N0, NT, X0, NL, [block(L, Phis, Insts, J)|Bs]) -->
    { I < NB, I1 is I + 1, Ctx = dctx(_, LN, _, _), table_arg(I1, LN, L) },
    read_group(phi, Ctx, N0, N1, X0, X1, Phis),
    { I =:= 0 -> Phis == [] ; true },
    read_group(plain, Ctx, N1, N2, X1, X2, Insts),
    read_inst(Ctx, N2, N3, X2, X3, jump, J),
    read_blocks(I1, NB, Ctx, N3, NT, X3, NL, Bs).

read_group(G, Ctx, N0, N, X0, X, [I|Is]) --> lookahead(Ws), { next_group(Ws, G) }, !,
    read_inst(Ctx, N0, N1, X0, X1, G, I), read_group(G, Ctx, N1, N, X1, X, Is).
read_group(_, _, N, N, X, X, []) --> [].

lookahead(Ws, Ws, Ws).

% at_end//: no words are left.
at_end([], []).

% next_group(+Ws, ?G): the next instruction of Ws, after any rebind, is
% of group G.
next_group([H|Ws], G) :-
    Op is H /\ 0xFFFF,
    (   rebind_opcode(Op)
    ->  L is (H >> 16) - 1, L >= 1, length(Skip, L), append(Skip, [H2|_], Ws),
        Op2 is H2 /\ 0xFFFF, \+ rebind_opcode(Op2), group(Op2, G)
    ;   group(Op, G)
    ).

take(0, []) --> !.
take(N, [X|Xs]) --> [X], { N1 is N - 1 }, take(N1, Xs).

read_inst(Ctx, N0, N, X0, X, G, Inst) -->
    (   [H], { H /\ 0xFFFF =:= 0x01 } -> { L is H >> 16, RL is L - 1, RL >= 1 }, take(RL, Rebinds)
    ;   { Rebinds = none }
    ),
    [H1], { Code is H1 /\ 0xFFFF, L1 is H1 >> 16, L1 >= 1, group(Code, G), nfb_form(Code, Inst, Fields), N1 is L1 - 1 },
    take(N1, Ws),
    { phrase(read_fields(Fields, Ctx, X0, X, Slots, []), Ws),
      bind_defs(Slots, Rebinds, Ctx, N0, N) }.

% bind_defs(+Slots, +Rebinds, +Ctx, +N0, -N): each definition's name: the
% next id's, or the rebound id's.
bind_defs(Slots, none, Ctx, N0, N) :- !,
    length(Slots, K), length(Ws, K), maplist(=(0), Ws), bind_defs(Slots, Ws, Ctx, N0, N).
bind_defs([], [], _, N, N).
bind_defs([D|Ds], [W|Ws], Ctx, N0, N) :-
    Ctx = dctx(TN, _, _, _),
    (   W =:= 0 -> Id = N0, N1 is N0 + 1 ; Id is W - 1, Id < N0, N1 = N0 ),
    I is Id + 1, table_arg(I, TN, D),
    bind_defs(Ds, Ws, Ctx, N1, N).

read_fields([], _, X, X, Ds, Ds) --> [].
read_fields([F|Fs], Ctx, X0, X, Ds0, Ds) -->
    read_field(F, Ctx, X0, X1, Ds0, Ds1), read_fields(Fs, Ctx, X1, X, Ds1, Ds).

read_field(def(D), _, X, X, [D|Ds], Ds) --> !.
read_field(local_def(N), dctx(_, _, XN, _), X0, X, Ds, Ds) --> !,
    { X is X0 + 1, table_arg(X, XN, N) }.
read_field(class(K), _, X, X, Ds, Ds) --> !, [C], { nfb_code(class, K, C) }.
read_field(enum(E, V), _, X, X, Ds, Ds) --> !, [C], { nfb_code(E, V, C) }.
read_field(u32(N), _, X, X, Ds, Ds) --> !, [N].
read_field(i64(N), _, X, X, Ds, Ds) --> !, read_i64(N).
read_field(opnd(V), dctx(TN, _, _, R), X, X, Ds, Ds) --> !, [W], { operand_value(W, TN, R, V) }.
read_field(label(L), dctx(_, LN, _, _), X, X, Ds, Ds) --> !, [I], { I1 is I + 1, table_arg(I1, LN, L) }.
read_field(target(T), dctx(_, LN, _, _), X, X, Ds, Ds) --> !,
    [W], { I is (W >> 1) + 1, table_arg(I, LN, L), ( W /\ 1 =:= 1 -> T = poll(L) ; T = L ) }.
read_field(local(N), dctx(_, _, XN, _), X, X, Ds, Ds) --> !, [I], { I1 is I + 1, table_arg(I1, XN, N) }.
read_field(str(A), dctx(_, _, _, r(StrT, _, _)), X, X, Ds, Ds) --> !, [I], { I1 is I + 1, table_arg(I1, StrT, A) }.
read_field(result(Res), _, X, X, Ds0, Ds) --> !, [W], { read_result(W, Res, Ds0, Ds) }.
read_field(alt(V, Alts), Ctx, X0, X, Ds0, Ds) --> !,
    [Tag], { member(Tag-V1-Fs, Alts), !, copy_term(V1-Fs, V-Fs1) },
    read_fields(Fs1, Ctx, X0, X, Ds0, Ds).
read_field(count(Xs, E, Fs), Ctx, X0, X, Ds0, Ds) --> !, [N], read_elems(N, Xs, E, Fs, Ctx, X0, X, Ds0, Ds).
read_field(rest(Xs, E, Fs), Ctx, X0, X, Ds0, Ds) --> !, read_rest(Xs, E, Fs, Ctx, X0, X, Ds0, Ds).

read_elems(0, [], _, _, _, X, X, Ds, Ds) --> !.
read_elems(N, [V|Vs], E, Fs, Ctx, X0, X, Ds0, Ds) -->
    { copy_term(E-Fs, V-Fs1) }, read_fields(Fs1, Ctx, X0, X1, Ds0, Ds1),
    { N1 is N - 1 }, read_elems(N1, Vs, E, Fs, Ctx, X1, X, Ds1, Ds).

read_rest([], _, _, _, X, X, Ds, Ds) --> at_end, !.
read_rest([V|Vs], E, Fs, Ctx, X0, X, Ds0, Ds) -->
    { copy_term(E-Fs, V-Fs1) }, read_fields(Fs1, Ctx, X0, X1, Ds0, Ds1),
    read_rest(Vs, E, Fs, Ctx, X1, X, Ds1, Ds).

read_result(0, void, Ds, Ds) :- !.
read_result(W, tuple([result(tmp(D1), K1), result(tmp(D2), K2)]), [D1, D2|Ds], Ds) :- W >= 0x100, !,
    C1 is (W - 0x100) >> 4, C2 is W /\ 15, nfb_code(class, K1, C1), nfb_code(class, K2, C2).
read_result(W, result(tmp(D), K), [D|Ds], Ds) :- nfb_code(class, K, W).

operand_value(W, TN, R, V) :-
    Tag is W /\ 3, P is W >> 2,
    (   Tag =:= 0 -> I is P + 1, table_arg(I, TN, N), V = tmp(N)
    ;   Tag =:= 3 -> sym_name(R, P, S), V = global(S)
    ;   R = r(_, ConstT, _), const_value(W, ConstT, N), V = const(N)
    ).

%% Files

%! write_nfb_file(+File, +Words) is det.
%
%  Write Words to File, each as four bytes, low byte first.
write_nfb_file(File, Ws) :-
    setup_call_cleanup(open(File, write, S, [type(binary)]),
                       maplist(put_word(S), Ws),
                       close(S)).
put_word(S, W) :-
    B0 is W /\ 0xFF, B1 is (W >> 8) /\ 0xFF, B2 is (W >> 16) /\ 0xFF, B3 is W >> 24,
    put_byte(S, B0), put_byte(S, B1), put_byte(S, B2), put_byte(S, B3).

%! read_nfb_file(+File, -Words) is det.
%
%  Words are the little-endian words of File. Throws nanofil_error(Msg)
%  when its length is not a multiple of four.
read_nfb_file(File, Ws) :-
    setup_call_cleanup(open(File, read, S, [type(binary)]),
                       read_file_words(S, Ws),
                       close(S)).
read_file_words(S, Ws) :-
    get_byte(S, B0),
    (   B0 =:= -1 -> Ws = []
    ;   get_byte(S, B1), get_byte(S, B2), get_byte(S, B3),
        (   B3 =:= -1 -> nfb_error('the file is not a whole number of words', []) ; true ),
        W is B0 \/ B1 << 8 \/ B2 << 16 \/ B3 << 24,
        Ws = [W|Ws1], read_file_words(S, Ws1)
    ).
