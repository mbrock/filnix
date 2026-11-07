/*  dterm_html: what dterm.pl and dterm-nix share. Pages as DCGs over
    codes (el//3, esc//1, seq//2), and the little Markdown that comments
    are written in: blocks/2 reads a comment's lines as paragraphs, lists,
    preformatted text, headings, pipe tables and fences, which each
    drawer sets with its own inline//N. Included, not a module, so the
    drawers call these as their own.
*/

%% HTML

write_page(Path, Body) :-
    phrase(Body, Cs),
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]),
                       format(S, "~s", [Cs]),
                       close(S)).

% A deterministic drawer releases fragments with html_flush//0. Closing
% the current difference list and resuming with a fresh one keeps enclosing
% elements without retaining their already-written children. Checkpoint
% observes allocation before writing/collection; phrase/2 callers stay pure.
write_streamed_page(Path, Body, Checkpoint) :-
    current_prolog_flag(stack_limit, Limit), Budget is Limit // 8,
    statistics(globalused, Used), GCAt is Used + Budget,
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]),
      setup_call_cleanup(nb_setval(dterm_streaming, true),
                         write_html_chunks(phrase(Body, Cs), Cs, S, Budget, GCAt, Checkpoint),
                         nb_delete(dterm_streaming)),
      close(S)).

write_html_chunks(Goal, Cs, S, Budget, GCAt, Checkpoint) :-
    once(reset(Goal, Signal, Cont)),
    call(Checkpoint),
    (   Cont == 0 -> format(S, "~s", [Cs])
    ;   Signal = dterm_html_chunk(Tail, Next), Tail = [],
        format(S, "~s", [Cs]),
        % SWI's adaptive GC otherwise lets disposable fragments accumulate
        % almost to the limit. Batch collection, not one GC per hypothesis.
        statistics(globalused, Used),
        (   Used >= GCAt
        ->  garbage_collect, statistics(globalused, Live), NextGC is Live + Budget
        ;   NextGC = GCAt
        ),
        write_html_chunks(Cont, Next, S, Budget, NextGC, Checkpoint)
    ).

html_flush(Cs, Next) :-
    ( nb_current(dterm_streaming, true) -> shift(dterm_html_chunk(Cs, Next)) ; Cs = Next ).

esc(X) --> { text_codes(X, Cs) }, esc_codes(Cs).

text_codes(X, Cs) :- string(X), !, string_codes(X, Cs).
text_codes(X, Cs) :- atom(X), !, atom_codes(X, Cs).
text_codes(X, Cs) :- is_list(X), !, Cs = X.
text_codes(X, Cs) :- format(codes(Cs), "~w", [X]).

esc_codes([]) --> [].
esc_codes([C|Cs]) --> esc_code(C), esc_codes(Cs).

esc_code(0'<) --> !, "&lt;".
esc_code(0'>) --> !, "&gt;".
esc_code(0'&) --> !, "&amp;".
esc_code(0'") --> !, "&quot;".
esc_code(C) --> [C].

raw(X) --> { text_codes(X, Cs) }, Cs.

%  el(Tag, Class, Body): an element with a class attribute (none for no
%  class).
el(Tag, Class, Body) --> el(Tag, Class, [], Body).
el(Tag, Class, Attrs, Body) -->
    "<", raw(Tag),
    (   { Class == none } -> [] ; " class=\"", raw(Class), "\"" ),
    attrs(Attrs), ">", Body, "</", raw(Tag), ">".

attrs([]) --> [].
attrs([K=V|As]) --> " ", raw(K), "=\"", esc(V), "\"", attrs(As).

seq([], _) --> [].
seq([X|Xs], G) --> call(G, X), seq(Xs, G).

%% The Markdown of comments

trim_blank_ends(Ls0, Ls) :-
    exclude_leading_blank(Ls0, Ls1),
    reverse(Ls1, R1),
    exclude_leading_blank(R1, R2),
    reverse(R2, Ls).

exclude_leading_blank([L|Ls0], Ls) :- blank(L), !, exclude_leading_blank(Ls0, Ls).
exclude_leading_blank(Ls, Ls).

blank(S) :- split_string(S, "", " \t", [""]).

dedent(Ls0, Ls) :-
    exclude(blank, Ls0, NonBlank),
    maplist(indent, NonBlank, Is),
    ( min_list(Is, Min) -> true ; Min = 0 ),
    maplist(drop(Min), Ls0, Ls).

indent(S, I) :-
    string_codes(S, Cs), phrase(spaces(I), Cs, _).

spaces(I) --> " ", !, spaces(I0), { I is I0 + 1 }.
spaces(0) --> [].

drop(N, S0, S) :- ( blank(S0) -> S = "" ; sub_string(S0, N, _, 0, S) ).

%  blocks(Lines, Blocks): p(Text), ul(Items), pre(Lines), and a little
%  Markdown for module headers: h(Level, Text) from "## Text" (h3, as
%  the page's own sections are h2),
%  table(Head, Rows) from lines of | cells | (the second line |---|),
%  and fence(Lang, Lines) from ``` blocks. A prolog fence is drawn as
%  terms, a diagram fence as box drawing.
blocks([], []).
blocks([L|Ls], Bs) :- blank(L), !, blocks(Ls, Bs).
blocks([L|Ls0], [fence(Lang, Body)|Bs]) :- string_concat("```", Lang0, L), !,
    split_string(Lang0, "", " ", [Lang]),
    (   append(Body, [End|Ls], Ls0), string_concat("```", _, End) -> true
    ;   Body = Ls0, Ls = []
    ),
    blocks(Ls, Bs).
blocks([L|Ls0], [h(N, Text)|Bs]) :- heading(L, N, Text), !, blocks(Ls0, Bs).
blocks([L|Ls0], [table(Head, Rows)|Bs]) :-
    table_line(L, Head), Ls0 = [Sep|Ls1], table_line(Sep, Cells), maplist(rule_cell, Cells), !,
    take_table(Ls1, Rows, Ls), blocks(Ls, Bs).
blocks([L|Ls0], [ul(Items)|Bs]) :- item_start(L, _), !,
    list_items([L|Ls0], Items, Ls), blocks(Ls, Bs).
blocks([L|Ls0], [pre([L|Pre])|Bs]) :- indent(L, I), I > 0, !,
    take_indented(Ls0, Pre0, Ls), trim_blank_ends(Pre0, Pre1), append(Pre1, [], Pre),
    blocks(Ls, Bs).
blocks([L|Ls0], [p(Text)|Bs]) :-
    take_para(Ls0, Para, Ls),
    atomic_list_concat([L|Para], ' ', Text0), atom_string(Text0, Text),
    blocks(Ls, Bs).

item_start(L, Rest) :-
    ( string_concat("- ", Rest, L) ; string_concat("* ", Rest, L) ), !.

list_items([L|Ls0], [Text|Items], Ls) :-
    item_start(L, First),
    take_cont(Ls0, Cont, Ls1),
    maplist([S0, S]>>split_string(S0, "", " ", [S]), Cont, Cont1),
    atomic_list_concat([First|Cont1], ' ', T), atom_string(T, Text),
    (   Ls1 = [L1|_], item_start(L1, _) -> list_items(Ls1, Items, Ls)
    ;   Ls1 = [B, L1|_], blank(B), item_start(L1, _) -> Ls1 = [_|Ls2], list_items(Ls2, Items, Ls)
    ;   Items = [], Ls = Ls1
    ).

take_cont([L|Ls0], [L|Cs], Ls) :- \+ blank(L), indent(L, I), I > 0, !, take_cont(Ls0, Cs, Ls).
take_cont(Ls, [], Ls).

take_indented([L|Ls0], [L|Cs], Ls) :- ( blank(L) ; indent(L, I), I > 0 ), !, take_indented(Ls0, Cs, Ls).
take_indented(Ls, [], Ls).

take_para([L|Ls0], [L|Ps], Ls) :-
    \+ blank(L), \+ item_start(L, _), indent(L, 0),
    \+ string_concat("```", _, L), \+ heading(L, _, _), \+ table_line(L, _), !,
    take_para(Ls0, Ps, Ls).
take_para(Ls, [], Ls).

heading(L, N, Text) :-
    member(Mark-N, ["### "-4, "## "-3]), string_concat(Mark, Text, L), !.

% table_line(+L, -Cells): L is | A | B |, Cells its trimmed cells. A |
% inside `code` belongs to the cell, so `N | none` stays whole.
table_line(L, Cells) :-
    string_codes(L, [0'||Cs]), append(Body, [0'|], Cs), !,
    cells(Body, Cells0), maplist([C0, C]>>(string_codes(S, C0), split_string(S, "", " ", [C])), Cells0, Cells).

cells(Cs, [Cell|Cells]) :- cell(Cs, Cell, Rest), ( Rest = [0'||More] -> cells(More, Cells) ; Cells = [] ).

%  As in GitHub's tables, \| is a | in the cell, inside backticks too.
cell([], [], []).
cell([0'\\, 0'||Cs], [0'||Cell], Rest) :- !, cell(Cs, Cell, Rest).
cell([0'||Cs], [], [0'||Cs]) :- !.
cell([0'`|Cs0], [0'`|Cell], Rest) :- append(Code0, [0'`|Cs1], Cs0), !,
    unescape_pipes(Code0, Code),
    cell(Cs1, Cell0, Rest), append(Code, [0'`|Cell0], Cell).
cell([C|Cs0], [C|Cell], Rest) :- cell(Cs0, Cell, Rest).

unescape_pipes([], []).
unescape_pipes([0'\\, 0'||Cs0], [0'||Cs]) :- !, unescape_pipes(Cs0, Cs).
unescape_pipes([C|Cs0], [C|Cs]) :- unescape_pipes(Cs0, Cs).

rule_cell(C) :- string_codes(C, Cs), Cs \== [], forall(member(X, Cs), memberchk(X, `-:`)).

take_table([L|Ls0], [Cells|Rows], Ls) :- table_line(L, Cells), !, take_table(Ls0, Rows, Ls).
take_table(Ls, [], Ls).
