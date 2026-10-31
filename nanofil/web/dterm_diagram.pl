/*  Diagrams: a ```diagram fence, written in box-drawing characters so it
    reads on GitHub and in the source, drawn on the page as HTML that
    reflows with the width and links the modules and predicates it names
    (included by dterm.pl, docs/dterm.md).

    Four shapes are read, each only when it accounts for every line:

    | Shape | Written as | Drawn as |
    |---|---|---|
    | frame | one box split by ├ rules, notes right of it | a stack of regions, its edges and words labelled |
    | pipeline | data lines, with │ and ▼ steps between them | data boxes joined by the steps that make them |
    | chains | `Label: A ─▶ B ─▶ C` lines | a row of chips per label, wrapping |
    | boxes | boxes joined by arrows, a title above | the boxes in reading order, joined by arrows |

    Anything else stays the text, in a block that scrolls sideways.
*/

diagram(Lines0, F) -->
    { dedent(Lines0, Lines1), exclude_leading_blank(Lines1, Lines2),
      reverse(Lines2, R0), exclude_leading_blank(R0, R1), reverse(R1, Lines),
      dg_parse(Lines, D) }, !,
    dg_draw(D, F).
diagram(Lines0, _) -->
    { dedent(Lines0, Ls), atomic_list_concat(Ls, '\n', T) },
    el(pre, "fence diagram", esc(T)).

%% Reading

dg_parse(Ls, frame(Items)) :-
    Ls = [Top|_], string_concat("┌", _, Top),
    last(Ls, Bot), string_concat("└", _, Bot),
    once(sub_string(Top, W0, 1, _, "┐")),
    \+ ( sub_string(Top, X, 1, _, "┌"), X > 0 ),
    W is W0 + 1,
    maplist(frame_line(W), Ls, Items).
dg_parse(Ls, pipe(Items)) :-
    \+ ( member(L, Ls), sub_string(L, _, _, _, "┌") ),
    once(( member(L, Ls), pipe_rail(L, _, _) )),
    pipe_items(Ls, Items0), merge_more(Items0, Items),
    Items = [data(_, _)|_].
dg_parse(Ls, chains(Cs)) :-
    \+ ( member(L, Ls), ( sub_string(L, _, _, _, "┌") ; sub_string(L, _, _, _, "│") ) ),
    once(( member(L, Ls), sub_string(L, _, _, _, "▶") )),
    chain_lines(Ls, none, Cs), Cs \== [].
dg_parse(Ls, boxes(Title, Boxes)) :-
    once(( member(L, Ls), ( sub_string(L, _, _, _, "▶") ; sub_string(L, _, _, _, "▼") ) )),
    findall(I-C-W, box_top(Ls, I, C, W), Tops), Tops = [I0-_-_|_],
    maplist(box_rows(Ls), Tops, Boxes),
    length(Pre, I0), append(Pre, _, Ls),
    \+ ( member(P, Pre), box_char_line(P) ),
    exclude(blank, Pre, Title0),
    maplist([S0, S]>>split_string(S0, "", " ", [S]), Title0, Title).

frame_line(W, L, Item) :-
    sub_string(L, 0, W, _, Box), sub_string(L, W, _, 0, Ann0),
    split_string(Ann0, "", " ", [Ann]),
    sub_string(Box, 0, 1, _, C),
    (   memberchk(C, ["┌", "├", "└"])
    ->  ( string_concat("←", R, Ann) -> split_string(R, "", " ", [A]) ; A = Ann ),
        Item = edge(C, A)
    ;   C == "│", sub_string(Box, _, 1, 0, "│"),
        sub_string(Box, 1, _, 1, T0), split_string(T0, "", " ", [T]),
        Item = row(T, Ann)
    ).

%  pipe_rail(+Line, -Mark, -Rest): Line is a step line, │ or ▼ after
%  spaces, Rest after the mark.
pipe_rail(L, Mark, Rest) :-
    split_string(L, "", " ", [T]), T \== "",
    sub_string(T, 0, 1, _, Mark), memberchk(Mark, ["│", "▼"]),
    sub_string(L, B, 1, _, Mark), !, B1 is B + 1, sub_string(L, B1, _, 0, Rest).

pipe_items([], []).
pipe_items([L|Ls], Items) :- blank(L), !, pipe_items(Ls, Items).
pipe_items([L|Ls], Items) :- pipe_rail(L, Mark, Rest), !,
    split_string(Rest, "", " ", [R]),
    (   R == "" -> Items = Items1
    ;   ( Mark == "▼" ; sub_string(Rest, 0, 10, _, "          ") ) -> Items = [more(R)|Items1]
    ;   cols(R, Call, Desc), Items = [step(Call, Desc)|Items1]
    ),
    pipe_items(Ls, Items1).
pipe_items([L|Ls], Items) :-
    split_string(L, "", " ", [T]),
    data_line(T, Is), append(Is, Items1, Items),
    pipe_items(Ls, Items1).

%  A data line, or one with an inline last step: A ── call ──▶ B.
data_line(T, [data(A, ""), step(C, ""), data(B, "")]) :-
    sub_string(T, I, _, J, "──▶"), !,
    sub_string(T, 0, I, _, Left), sub_string(T, _, J, 0, B0), split_string(B0, "", " ─", [B]),
    sub_string(Left, K, _, L, " ── "), !,
    sub_string(Left, 0, K, _, A), sub_string(Left, _, L, 0, C0), split_string(C0, "", " ─", [C]).
data_line(T, [data(N, Fs)]) :- cols(T, N, Fs).

%  cols(+Text, -A, -B): Text split at its first run of two spaces.
cols(R, A, B) :-
    (   sub_string(R, I, 2, _, "  ")
    ->  sub_string(R, 0, I, _, A), sub_string(R, I, _, 0, B0), split_string(B0, "", " ", [B])
    ;   A = R, B = ""
    ).

merge_more([], []).
merge_more([step(C, D), more(M)|Is], Out) :- !,
    atomic_list_concat([D, M], ' ', D1), atom_string(D1, D2),
    merge_more([step(C, D2)|Is], Out).
merge_more([more(M)|_], _) :- !, M = fail.
merge_more([I|Is], [I|Os]) :- merge_more(Is, Os).

chain_lines([], _, []).
chain_lines([L|Ls], P, Cs) :- blank(L), !, chain_lines(Ls, P, Cs).
chain_lines([L|Ls], P, Cs) :-
    split_string(L, "", " ", [T]),
    (   \+ sub_string(T, _, _, _, "▶")
    ->  string_concat(Lab, ":", T), chain_lines(Ls, Lab, Cs)
    ;   (   sub_string(T, B, 2, _, ": "), sub_string(T, 0, B, _, Lab0),
            \+ sub_string(Lab0, _, _, _, "─")
        ->  B2 is B + 2, sub_string(T, B2, _, 0, R), Lab = Lab0
        ;   R = T, Lab = P
        ),
        Lab \== none,
        split_string(R, "▶", " ─", Items),
        Cs = [chain(Lab, Items)|Cs1],
        chain_lines(Ls, none, Cs1)
    ).

box_char_line(L) :- member(C, ["┌", "│", "└", "─"]), sub_string(L, _, _, _, C), !.

%  box_top(+Lines, -I, -C, -W): a box of width W starts at column C of
%  line I.
box_top(Ls, I, C, W) :-
    nth0(I, Ls, L), sub_string(L, C, 1, _, "┌"),
    once(( sub_string(L, C2, 1, _, "┐"), C2 > C )),
    \+ ( sub_string(L, Cx, 1, _, "┌"), Cx > C, Cx < C2 ),
    W is C2 - C + 1.

box_rows(Ls, I-C-W, Rows) :-
    I1 is I + 1, box_rows_from(Ls, I1, C, W, Rows).
box_rows_from(Ls, J, C, W, Rows) :-
    nth0(J, Ls, L), sub_string(L, C, 1, _, Ch),
    (   Ch == "└" -> Rows = []
    ;   Ch == "│", W2 is W - 2, C1 is C + 1, sub_string(L, C1, W2, _, T0),
        split_string(T0, "", " ", [T]), Rows = [T|Rows1],
        J1 is J + 1, box_rows_from(Ls, J1, C, W, Rows1)
    ).

%% Drawing

dg_draw(frame(Items), F) --> el(div, "dg dg-frame", seq(Items, frame_item(F))).
dg_draw(pipe(Items), F) --> el(div, "dg dg-pipe", seq(Items, pipe_item(F))).
dg_draw(chains(Cs), F) --> el(div, "dg dg-chains", seq(Cs, chain_(F))).
dg_draw(boxes(Title, Boxes), F) -->
    el(div, "dg dg-boxes",
       ( seq(Title, [T]>>el(div, "dg-title", dlabel(T, F))),
         el(div, "dg-flow", boxes_(Boxes, F)) )).

frame_item(F, edge(C, A)) -->
    { edge_class(C, K) },
    el(div, K, ( el(span, "dg-rule", []),
                 el(span, "dg-at", ( { A == "" } -> [] ; "← ", dlabel(A, F) )) )).
frame_item(F, row(T, A)) -->
    el(div, "dg-row", ( el(span, "dg-cell", dlabel(T, F)), el(span, "dg-off", dlabel(A, F)) )).

edge_class("┌", "dg-edge dg-top").
edge_class("├", "dg-edge dg-mid").
edge_class("└", "dg-edge dg-bot").

pipe_item(F, data(N, Fs)) -->
    el(div, "dg-data", ( el(span, "dg-name", dlabel(N, F)), opt_span("dg-forms", Fs, F) )).
pipe_item(F, step(C, D)) -->
    el(div, "dg-step", ( el(span, "dg-call", dlabel(C, F)), opt_span("dg-what", D, F) )).

opt_span(_, "", _) --> !, [].
opt_span(K, T, F) --> el(span, K, dlabel(T, F)).

chain_(F, chain(Lab, Items)) -->
    el(div, "dg-chain", ( el(span, "dg-label", dlabel(Lab, F)),
                          el(span, "dg-links", chips(Items, F)) )).

% Each arrow is bound to the chip after it, so a wrapped row starts "→ B".
chips([I|Is], F) --> chip(I, F), hops(Is, F).

hops([], _) --> [].
hops([I|Is], F) -->
    " ", el(span, "dg-hop", ( el(span, "dg-arrow", "→"), " ", chip(I, F) )), hops(Is, F).

chip(I, F) -->
    { string_concat("[", R, I), string_concat(In, "]", R) }, !,
    el(span, "dg-chip dg-opt", [title="when selected"], dlabel(In, F)).
chip(I, F) --> el(span, "dg-chip", dlabel(I, F)).

boxes_([B|Bs], F) --> box_(B, F), box_hops(Bs, F).

box_hops([], _) --> [].
box_hops([B|Bs], F) -->
    " ", el(span, "dg-hop", ( el(span, "dg-arrow", "→"), " ", box_(B, F) )), box_hops(Bs, F).

box_(Rows, F) --> el(div, "dg-box", seq(Rows, box_row(F))).
box_row(F, T) -->
    { cols(T, A, B) },
    (   { B == "" } -> el(div, "dg-brow", dlabel(A, F))
    ;   el(div, "dg-brow dg-kv", ( el(span, "dg-k", dlabel(A, F)), el(span, "dg-v", dlabel(B, F)) ))
    ).

%  dlabel(+Text, +File): a diagram's words: a term drawn as one, a
%  variable, or text whose module and predicate names link to them.
dlabel(T, F) --> { string_codes(T, Cs), Cs \== [], code_term(Cs, X) }, !,
    el(code, term, term(X, _, 999, ctx(F, data))).
dlabel(T, _) --> { atom_string(A, T), atom_codes(A, [C|Cs]), code_type(C, upper),
                   maplist([X]>>code_type(X, csym), Cs) }, !,
    var_(A).
dlabel(T, F) --> { string_codes(T, Cs) }, dl(Cs, F).

dl([], _) --> [].
dl(Cs0, F) --> { word(Cs0, W, Cs1), W \== [] }, !, dword(W, Cs1, F).
dl([C|Cs], F) --> esc_code(C), dl(Cs, F).

dword(W, [0':|Cs0], F) -->
    { word(Cs0, W2, Cs1), W2 \== [], pred_ref(W2, Cs1, Ref0, PI, Cs),
      atom_codes(M, W), defined(PI, M, Id) }, !,
    { append([W, `:`, Ref0], Ref), uri_encoded(fragment, Id, Frag),
      format(atom(Href), "~w.html#~w", [M, Frag]) },
    el(a, ref, [href=Href], el(code, none, esc(Ref))), dl(Cs, F).
dword(W, Cs0, F) --> { pred_ref(W, Cs0, Ref, PI, Cs), pred_href(F, PI, Href) }, !,
    el(a, ref, [href=Href], el(code, none, esc(Ref))), dl(Cs, F).
dword(W, Cs0, F) -->
    { atom_codes(M, W), defined(_, M, _),
      ( append(`.pl`, Cs, Cs0), \+ ( Cs = [C|_], code_type(C, csym) ) -> append(W, `.pl`, Text)
      ; Cs = Cs0, Text = W ),
      atom_concat(M, '.html', Href) }, !,
    el(a, "ref module", [href=Href], esc(Text)), dl(Cs, F).
dword(W, Cs, F) --> esc(W), dl(Cs, F).
