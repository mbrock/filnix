/*  The playground's page: what nanofil makes of one C file, as an
    <article> drawn with dterm.

    play_html(+File, +Opt, -Html): Html (a string) shows play/3's stages
    with their times, then the C syntax terms of File's own items, the IR
    terms (a function as its head over its blocks, a block as its label
    over one instruction per row), the IR as QBE text, and the Fil-C
    amd64 assembly as terms beside the AT&T line each prints as.

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
        (   { memberchk(term(syntax, _), Stages) }
        ->  { memberchk(term(syntax, All), Stages), play_items(File, All, Items, NAll) },
            syntax_(Items, NAll)
        ;   []
        ),
        (   { memberchk(term(ir, M), Stages) } -> ir_(M) ; [] ),
        (   { memberchk(text(ir, IR), Stages) }
        ->  section_(qbe, "IR as QBE text", el(pre, "text", esc(IR)))
        ;   []
        ),
        (   { memberchk(term(asm, Lines), Stages) } -> asm_(Lines) ; [] )
    )).

section_(Id, Title, Body) -->
    el(section, Id, [id=Id], ( el(h2, none, esc(Title)), Body )).

%% Stages

stages_(Stages) -->
    { include([S]>>(S = stage(_, _, _)), Stages, Ss),
      foldl([stage(_, T, _), A0, A]>>(A is A0 + T), Ss, 0, Total) },
    section_(stages, "Stages",
        el(table, "stages", (
            seq(Ss, stage_row),
            el(tr, "total", ( el(td, none, "total"), el(td, "time", ms(Total)), el(td, none, []) ))
        ))).

stage_row(stage(Name, T, R)) -->
    { R = ok -> Class = ok ; Class = bad },
    el(tr, Class, (
        el(td, "name", esc(Name)),
        el(td, "time", ms(T)),
        el(td, "result", result_(R))
    )).

ms(T) --> { format(codes(Cs), "~0f ms", [T * 1000]) }, esc(Cs).

result_(ok) --> !, "✓".
result_(error(E)) --> !,
    { (   E = nanofil_error(Msg) -> true
      ;   message_to_codes(E, Msg)
      ) },
    el(span, "error", esc(Msg)).
result_(R) --> esc(R).

message_to_codes(E, Cs) :-
    catch(( message_to_codes_(E, Cs) ), _, format(codes(Cs), "~q", [E])).
message_to_codes_(E, Cs) :-
    '$messages':translate_message(E, Lines, []),
    with_output_to(codes(Cs), print_message_lines(current_output, '', Lines)).

%% C syntax: the items of the input file, not of its headers.

play_items(File, Items0, Items, N) :-
    length(Items0, N),
    include(item_in(File), Items0, Items).

item_in(File, Item) :-
    compound(Item), arg(1, Item, F:_), F == File.

syntax_(Items, NAll) -->
    { length(Items, N), NH is NAll - N,
      plural(N, item, Its), plural(NH, item, HIts),
      format(codes(Note), "~d ~w from this file; ~d more ~w from the headers it includes.", [N, Its, NH, HIts]) },
    section_(syntax, "C syntax terms", (
        el(p, "note", esc(Note)),
        seq(Items, item_)
    )).

plural(1, W, W) :- !.
plural(_, W, Ws) :- atom_concat(W, s, Ws).

item_(Item) --> el(div, "clause item", term(Item)).

%% IR terms

ir_(module(Items)) -->
    section_(ir, "IR terms", (
        el(p, "note", "The module's terms (ir.pl's grammar). A function is its head over its Blocks, a block blk(Label, Phis, Insts, Jump) its label over a row for each phi, instruction and the jump."),
        seq(Items, ir_item)
    )).

ir_item(func(Name, Linkage, Ret, Params, Blocks)) --> !,
    el(div, "clause func", (
        el(div, "head", ( dterm:compound_(func(Name, Linkage, Ret, Params, '$VAR'('Blocks')), _, ctx(play, head)) )),
        el(div, "goals", seq(Blocks, block_))
    )).
ir_item(Item) --> el(div, "clause data", term(Item)).

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

%% Assembly: each line's term beside the text it prints as.

% Drawing a line costs about 0.15 ms natively and 0.4 ms in WebAssembly,
% so a long listing draws its first lines and prints the rest as text.
asm_term_lines(1500).

asm_(Lines) -->
    { length(Lines, N), asm_term_lines(Max) },
    (   { N =< Max }
    ->  { format(codes(Note), "~d lines.", [N]) },
        section_(asm, "Fil-C amd64 assembly", (
            el(p, "note", esc(Note)),
            el(table, "asm", seq(Lines, asm_row))
        ))
    ;   { length(First, Max), append(First, _, Lines),
          format(codes(Note), "~d lines; the first ~d drawn as terms, then the whole listing as text.", [N, Max]),
          with_output_to(codes(Text), asm:print_asm(Lines)) },
        section_(asm, "Fil-C amd64 assembly", (
            el(p, "note", esc(Note)),
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
