/*  The playground's page: what nanofil makes of one C file, as an
    <article> drawn with dterm.

    play_html(+File, +Opt, -Html): Html (a string) holds one <section>
    per view, by id: stages (their times), failure (the stage that
    failed and why), c (the C syntax terms of File's own items), ir (the
    IR terms), data (each data object's bytes), symbols (what the module
    defines and imports), irtext (the IR as text, src/ir_text.pl) and
    asm (the Fil-C amd64 assembly as terms beside the AT&T line each
    prints as).

    Terms are drawn by dterm.pl's term//4 (web/dterm.pl), without source
    positions: IR and assembly terms have no source text and no comments,
    so only dterm's term layer is used. SWI-Prolog only, like dterm; load
    dterm.pl and this file before src/swi/compat.pl, which would make
    their string literals character lists.
*/
:- module(play_view, [play_html/3]).
:- set_prolog_flag(double_quotes, codes).

:- use_module(library(lists)).
:- use_module(library(apply)).

play_html(File, Opt, Html) :-
    play:play(File, Opt, Stages),
    phrase(article(File, Stages), Cs),
    string_codes(Html, Cs).

% dterm's el//3 calls its body in module dterm, so the elements are
% built here; only escaping and terms come from dterm.
el(T, C, B) --> el(T, C, [], B).
el(T, C, As, B) -->
    "<", dterm:raw(T),
    (   { C == none } -> [] ; " class=\"", dterm:raw(C), "\"" ),
    attrs(As), ">", B, "</", dterm:raw(T), ">".

attrs([]) --> [].
attrs([K=V|As]) --> " ", dterm:raw(K), "=\"", esc(V), "\"", attrs(As).

seq([], _) --> [].
seq([X|Xs], G) --> call(G, X), seq(Xs, G).

% nanofil's text is character lists; dterm escapes codes.
esc([C|Cs]) --> { atom(C) }, !, { atom_chars(A, [C|Cs]) }, dterm:esc(A).
esc(X) --> dterm:esc(X).
term(T) --> dterm:term(T, _, 999, ctx(play, data)).

article(File, Stages) -->
    el(article, "dterm play", (
        stages_(Stages),
        failure_(Stages),
        (   { memberchk(term(syntax, All), Stages) }
        ->  { play_items(File, All, Items) },
            section_(c, seq(Items, item_))
        ;   []
        ),
        (   { memberchk(term(ir, M), Stages) }
        ->  ir_(M), data_(M), symbols_(M)
        ;   []
        ),
        (   { memberchk(text(ir, IR), Stages) }
        ->  section_(irtext, el(pre, "text", esc(IR)))
        ;   []
        ),
        (   { memberchk(term(asm, Lines), Stages) } -> asm_(Lines) ; [] )
    )).

% The page moves each section into its own place: stages under the
% Compile button, c, ir, irtext and asm into tabs, data and symbols beside.
section_(Id, Body) --> el(section, none, [id=Id], Body).

%% Stages

stages_(Stages) -->
    { include([S]>>(S = stage(_, _, _)), Stages, Ss),
      foldl([stage(_, T, _), A0, A]>>(A is A0 + T), Ss, 0, Total) },
    section_(stages,
        el(table, "stages", (
            seq(Ss, stage_row),
            el(tr, "total", ( el(td, none, []), el(td, "time", ms(Total)) ))
        ))).

stage_row(stage(Name, T, R)) -->
    { R = ok -> Class = ok ; Class = bad },
    el(tr, Class, (
        el(td, "name", esc(Name)),
        el(td, "time", ms(T))
    )).

ms(T) --> { format(codes(Cs), "~0f ms", [T * 1000]) }, esc(Cs).

% The stage that failed, and why.
failure_(Stages) -->
    (   { member(stage(Name, _, R), Stages), R \== ok, R \== skipped }
    ->  section_(failure, (
            el(span, "name", esc(Name)),
            el(pre, "why", why(R))
        ))
    ;   []
    ).

why(error(E)) --> !,
    { (   E = nanofil_error(Msg) -> true
      ;   message_to_codes(E, Msg)
      ) },
    esc(Msg).
why(R) --> esc(R).

message_to_codes(E, Cs) :-
    catch(( message_to_codes_(E, Cs) ), _, format(codes(Cs), "~q", [E])).
message_to_codes_(E, Cs) :-
    '$messages':translate_message(E, Lines, []),
    with_output_to(codes(Cs), print_message_lines(current_output, '', Lines)).

%% C syntax: the items of the input file, not of its headers.

play_items(File, Items0, Items) :-
    include(item_in(File), Items0, Items).

item_in(File, Item) :-
    compound(Item), arg(1, Item, F:_), F == File.

% String literals are code lists in the syntax tree; draw them as strings.
item_(Item0) --> { strings(Item0, Item) }, el(div, "clause item", term(Item)).

strings(T0, T) :- var(T0), !, T = T0.
strings(str(Cs), str(S)) :- is_list(Cs), Cs \== [], maplist(integer, Cs), !, string_codes(S, Cs).
strings(T0, T) :- compound(T0), !, T0 =.. [F|As0], maplist(strings, As0, As), T =.. [F|As].
strings(T, T).

%% IR terms: a function is its head over its blocks, a block its label
%% over one instruction per row; a data object its head over its items.
%% Each folds away under its head.

ir_(module(Items)) -->
    section_(ir, seq(Items, ir_item)).

ir_item(func(Name, Linkage, Ret, Params, Blocks)) --> !,
    folding("clause func", Name,
        dterm:compound_(func(Name, Linkage, Ret, Params, '$VAR'('Blocks')), _, ctx(play, head)),
        seq(Blocks, block_)).
ir_item(data(Name, Linkage, Align, Items0)) -->
    { text_runs(Items0, Items), length(Items, N), shown(N, Max) },
    folding("clause data", Name,
        dterm:compound_(data(Name, Linkage, Align, '$VAR'('Items')), _, ctx(play, head)),
        ( seq_max(Items, Max, row), more(N, Max) )).

folding(Class, Name, Head, Goals) -->
    { atom_codes(Name, Cs), append("ir-", Cs, Id) },
    el(details, Class, [id=Id, open=""], (
        el(summary, "head", Head),
        el(div, "goals", Goals)
    )).

% A run of byte items that is text draws as the one item(b, str(S)) it
% means: "hello, world\n\0" rather than fourteen item(b, c(N)) rows.
text_runs([], []).
text_runs([item(b, c(C))|Is0], [item(b, str(S))|Is]) :-
    text_byte(C), Is0 = [item(b, c(D))|_], text_byte(D), !,
    take_text(Is0, Cs, Is1),
    string_codes(S, [C|Cs]),
    text_runs(Is1, Is).
text_runs([I|Is0], [I|Is]) :- text_runs(Is0, Is).

take_text([item(b, c(C))|Is0], [C|Cs], Is) :- text_byte(C), !, take_text(Is0, Cs, Is).
take_text(Is, [], Is).

text_byte(C) :- integer(C), ( between(32, 126, C) ; memberchk(C, [0, 9, 10, 13]) ), !.

block_(blk(Label, Phis, Insts, Jump)) -->
    el(div, "block-ir", (
        el(div, "label", ( el(span, "f pat", esc(Label)), el(span, "neck", ":") )),
        el(div, "goals", (
            seq(Phis, row),
            seq(Insts, row),
            row(Jump)
        ))
    )).

row(T) --> el(div, "goal", term(T)).

shown(N, Max) :- ( N > 80 -> Max = 64 ; Max = N ).

seq_max([], _, _) --> [].
seq_max([X|Xs], N, G) --> ( { N > 0 } -> call(G, X), { N1 is N - 1 }, seq_max(Xs, N1, G) ; [] ).

more(N, Max) -->
    (   { N > Max } -> { K is N - Max }, el(div, "more", ( "… ", esc(K), " more" )) ; [] ).

%% Data: each object's bytes, sixteen to a row, as hex and as text.
%% A pointer item is the symbol it points at; a long run of zeros is
%% one row.

data_(module(Items)) -->
    { include([I]>>(I = data(_, _, _, _)), Items, Ds) },
    (   { Ds == [] } -> [] ; section_(data, seq(Ds, data_object)) ).

data_object(data(Name, _, _, Items)) -->
    { foldl(data_rows, Items, 0-[], Size-Rows0), reverse(Rows0, Rows1),
      lines(Rows1, Rows), length(Rows, N), shown(N, Max) },
    el(details, "object", [open=""], (
        el(summary, none, (
            el(span, "name", esc(Name)),
            el(span, "size", ( esc(Size), " bytes" ))
        )),
        el(table, "hex", ( seq_max(Rows, Max, hex_row), more(N, Max) ))
    )).

% data_rows(+Item, +Off0-Rows0, -Off-Rows): Rows in reverse, each
% bytes(Off, Bytes) | zero(Off, N) | sym(Off, Name, Plus).
data_rows(item(W, sym(S, Plus)), O0-Rs, O-[sym(O0, S, Plus)|Rs]) :- !,
    width(W, K), O is O0 + K.
data_rows(zero(N), O0-Rs, O-[zero(O0, N)|Rs]) :- N > 64, !, O is O0 + N.
data_rows(Item, O0-Rs0, O-Rs) :-
    item_bytes(Item, Bs), length(Bs, K), O is O0 + K,
    (   Rs0 = [bytes(Start, Bs0)|Rs1]
    ->  append(Bs0, Bs, Bs1), Rs = [bytes(Start, Bs1)|Rs1]
    ;   Rs = [bytes(O0, Bs)|Rs0]
    ).

item_bytes(zero(N), Bs) :- length(Bs, N), maplist(=(0), Bs).
item_bytes(item(b, str(Cs)), Bs) :- maplist([C, B]>>(char_code(C, X), B is X /\ 255), Cs, Bs).
item_bytes(item(W, c(N)), Bs) :- width(W, K), le_bytes(K, N, Bs).

width(b, 1). width(h, 2). width(w, 4). width(s, 4). width(l, 8). width(d, 8). width(p, 8).

le_bytes(0, _, []) :- !.
le_bytes(K, N, [B|Bs]) :- B is N /\ 255, N1 is N >> 8, K1 is K - 1, le_bytes(K1, N1, Bs).

% Byte runs break into lines of sixteen.
lines([], []).
lines([bytes(O, Bs)|Rs0], Rs) :- !, chop(O, Bs, Rs, Rs1), lines(Rs0, Rs1).
lines([R|Rs0], [R|Rs]) :- lines(Rs0, Rs).

chop(_, [], Rs, Rs) :- !.
chop(O, Bs, [bytes(O, L)|Rs], Rs0) :-
    length(Bs, N),
    (   N > 16 -> length(L, 16), append(L, More, Bs) ; L = Bs, More = [] ),
    O1 is O + 16,
    chop(O1, More, Rs, Rs0).

hex_row(bytes(O, Bs)) -->
    { foldl([B, A0, A]>>(format(codes(H), "~|~`0t~16r~2+ ", [B]), append(A0, H, A)), Bs, [], Hex0),
      ( append(Hex, " ", Hex0) -> true ; Hex = Hex0 ),
      maplist([B, C]>>( between(32, 126, B) -> C = B ; C = 0'· ), Bs, Text) },
    el(tr, none, ( off(O), el(td, "bytes", esc(Hex)), el(td, "text", esc(Text)) )).
hex_row(zero(O, N)) -->
    el(tr, "zero", ( off(O), el(td, "bytes", ( "00 × ", esc(N) )), el(td, none, []) )).
hex_row(sym(O, S, Plus)) -->
    el(tr, "sym", ( off(O), el(td, "bytes", ( "→ ", sym_ref(S), plus(Plus) )), el(td, none, []) )).

off(O) --> { format(codes(Cs), "~|~`0t~16r~4+", [O]) }, el(td, "off", esc(Cs)).

plus(0) --> !.
plus(N) --> " + ", esc(N).

sym_ref(S) --> { atom_codes(S, Cs), append("#ir-", Cs, H) }, el(a, none, [href=H], esc(S)).

%% Symbols: what the module defines, and what it uses but does not.

symbols_(module(Items)) -->
    { findall(N, ( member(I, Items), arg(1, I, N) ), Defined),
      findall(S, sub_term(glo(S), Items), Used0), sort(Used0, Used),
      subtract(Used, Defined, Imports) },
    section_(symbols,
        el(table, "symbols", (
            seq(Items, symbol_row),
            seq(Imports, import_row(Items))
        ))).

symbol_row(func(Name, Linkage, Ret, Params, _)) -->
    { maplist([par(K, _), K]>>true, Params, Ks), sig(Ret, Ks, Sig) },
    sym_tr(Name, function, Sig, Linkage).
symbol_row(data(Name, Linkage, _, Items)) -->
    { foldl(data_rows, Items, 0-[], Size-_), format(codes(Cs), "~d bytes", [Size]) },
    sym_tr(Name, object, Cs, Linkage).

% An import called somewhere has the kinds of its first call.
import_row(Items, Name) -->
    (   { sub_term(call(Res, glo(Name), Args), Items) }
    ->  { ( Res = to(_, R) -> true ; R = Res ),
          maplist([arg(K, _), K]>>true, Args, Ks), sig(R, Ks, Sig) },
        el(tr, "import", ( el(td, "name", esc(Name)), el(td, none, "function"),
                           el(td, "type", esc(Sig)), el(td, none, "import") ))
    ;   el(tr, "import", ( el(td, "name", esc(Name)), el(td, none, "object"),
                           el(td, none, []), el(td, none, "import") ))
    ).

sym_tr(Name, Kind, Type, Linkage) -->
    { ( Linkage = ro(L) -> format(codes(Ls), "~w, read-only", [L]) ; format(codes(Ls), "~w", [Linkage]) ) },
    el(tr, none, (
        el(td, "name", sym_ref(Name)),
        el(td, none, esc(Kind)),
        el(td, "type", esc(Type)),
        el(td, none, esc(Ls))
    )).

sig(Ret, Ks, Sig) :-
    ( is_list(Ret) -> R = tuple ; Ret = tuple(_) -> R = tuple ; R = Ret ),
    atomic_list_concat(Ks, ', ', A),
    format(codes(Sig), "~w(~w)", [R, A]).

%% Assembly: each line's term beside the text it prints as.

% Drawing a line costs about 0.15 ms natively and 0.4 ms in WebAssembly,
% so a long listing draws its first lines and prints the rest as text.
asm_term_lines(1500).

asm_(Lines) -->
    { length(Lines, N), asm_term_lines(Max) },
    (   { N =< Max }
    ->  section_(asm, el(table, "asm", seq(Lines, asm_row)))
    ;   { length(First, Max), append(First, _, Lines),
          with_output_to(codes(Text), asm:print_asm(Lines)) },
        section_(asm, (
            el(table, "asm", seq(First, asm_row)),
            el(pre, "text", esc(Text))
        ))
    ).

asm_row(L) -->
    { with_output_to(codes(Cs0), asm:print_asm([L])),
      ( append(Cs, [0'\n], Cs0) -> true ; Cs = Cs0 ),
      ( L = label(_) -> Class = "label" ; Class = none ) },
    el(tr, Class, (
        el(td, "term", term(L)),
        el(td, "att", el(code, none, esc(Cs)))
    )).
