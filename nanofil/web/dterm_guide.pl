/*  Documents as dterm pages: docs/guide.md and docs/formal.md, each
    drawn beside the module pages it explains as NAME.html (included by
    dterm.pl, docs/dterm.md).

    The Markdown stays the source and reads as it is on GitHub. Here it
    is read as blocks (headings, paragraphs, lists, tables, fences) and
    drawn with dterm's own pieces:

    - an example output between `<!-- guide: NAME -->` and
      `<!-- /guide -->` is drawn from its terms, the `output(NAME, Items)`
      fact tests/guide.sh wrote to docs/guide/outputs.pl, not from the
      text in the fence; outputs that are not terms (assembly, C) stay
      text;
    - inline code that reads as a term is drawn as one, and IR
      temporaries as the playground draws them; in a document that
      names Rocq, Rocq that only Rocq writes (`Ret v`,
      `cap := None | Obj base`, a `Theorem`) and ```rocq fences are
      drawn by dterm-rocq (rocq/rocq_draw.pl);
    - a predicate reference, `name/N`, `name//N` or `module:name/N`,
      links to its definition, with its PlDoc signature in a card shown
      on hover; `name.pl` links to the module's page;
    - glossary entries get anchors, and an emphasized or code mention of
      a glossary term, in any of the documents, links to its entry;
    - a link to a .nix file goes to its dterm-nix page (../nix/), and a
      link to another of the documents to its page;
    - each module page links back to each document's sections that name
      it, its module-map entry, or, in a document without one, the
      sections that mention it; each predicate links to the sections
      that mention it.

    A reference that does not resolve is broken: an unknown predicate,
    one defined in several modules that its section does not choose
    between, an unknown module, a missing anchor or document, a prolog
    output with no terms, or a glossary entry that names no source.
    Broken references fail the site build and `dterm.pl --check`, which
    the Nix check runs.

    Every fact below names its document first, by its file name without
    `.md`: guide, formal.
*/

%  Rocq in the documents (formal.md) is drawn by dterm-rocq.
:- use_module(rocq/rocq_draw, [rocq_inline//1, rocq_fence//1]).

%  guide_rocq(Doc): Doc is about Rocq (names it), so its inline code may
%  be Rocq.
:- dynamic guide_rocq/1, guide_slug/2, guide_broken/1, guide_mention/5, guide_heading/5, guide_gloss/3,
           guide_output/2, guide_module/1, pred_doc/4, guide_entry_ref/1.

%  guide_heading(Doc, Id, Level, Title, Modules): a heading of Doc, its
%  anchor, and the modules (name.pl) it names.
%  guide_gloss(Doc, Key, Id): a glossary entry's term (lower case) and
%  anchor.
%  guide_mention(Doc, Module, What, SecId, SecTitle): the section SecId
%  names Module's predicate What (Name/Arity), or Module itself (module).
%  pred_doc(File, PI, Key, Doc): the documentation dterm draws for PI.

%% Reading

%  guide_render(+Paths, +Sources, -Pages): Pages are Doc-Page for each
%  document, its references resolved against the indexed Sources and
%  against every document's headings and glossary.
guide_render(Paths, Sources, Pages) :-
    forall(member(src(Base, _, _, _), Sources), assertz(guide_module(Base))),
    forall(member(Src, Sources), index_docs(Src)),
    maplist(doc_name, Paths, Docs),
    nb_setval(guide_docs, Docs),
    maplist(read_doc, Paths, Read),
    maplist(render_doc, Read, Pages).

%  doc_name(+Path, -Doc): docs/formal.md is formal.
doc_name(Path, Doc) :- file_base_name(Path, F), file_name_extension(Doc, _, F).

%  doc_label(+Doc, -Label): how a module page names the document.
doc_label(guide, "the guide") :- !.
doc_label(formal, "the formal campaign") :- !.
doc_label(Doc, Doc).

read_doc(Path, doc(Doc, Dir, Blocks)) :-
    doc_name(Path, Doc),
    file_directory_name(Path, Dir),
    read_file_to_string(Path, Text, [encoding(utf8)]),
    split_string(Text, "\n", "", Lines),
    md_blocks(Lines, Blocks),
    ( sub_string(Text, _, _, _, "Rocq") -> assertz(guide_rocq(Doc)) ; true ),
    nb_setval(guide_doc, Doc),
    retractall(guide_slug(_, _)),
    guide_prepass(Blocks).

render_doc(doc(Doc, Dir, Blocks), Doc-Page) :-
    nb_setval(guide_doc, Doc),
    nb_setval(guide_dir, Dir),
    retractall(guide_output(_, _)),
    directory_file_path(Dir, Doc, OutDir),
    directory_file_path(OutDir, 'outputs.pl', Outputs),
    load_outputs(Outputs),
    nb_setval(dterm_file, guide),
    nb_setval(guide_h2, ""),
    nb_setval(guide_sec, sec(top, "", [])),
    nb_setval(guide_entry, none),
    phrase(guide_page(Doc, Blocks), Page).

index_docs(src(Base, _, _, Events)) :-
    entries(Events, Es),
    forall(( member(pred(Key, Doc, _), Es), Doc \== none ),
           ( key_pred(Key, PI), assertz(pred_doc(Base, PI, Key, Doc)) )).

load_outputs(Path) :-
    (   exists_file(Path)
    ->  setup_call_cleanup(open(Path, read, S, [encoding(utf8)]), read_outputs(S), close(S))
    ;   true
    ).

read_outputs(S) :-
    read_term(S, T, []),
    (   T == end_of_file -> true
    ;   ( T = output(N, Items) -> atom_string(N, Name), assertz(guide_output(Name, Items)) ; true ),
        read_outputs(S)
    ).

broken(Fmt, Args) :-
    format(string(M), Fmt, Args),
    nb_getval(guide_sec, sec(_, Title, _)), nb_getval(guide_doc, Doc),
    format(string(Msg), "~w.md: ~w (in \"~w\")", [Doc, M, Title]),
    (   guide_broken(Msg) -> true ; assertz(guide_broken(Msg)) ).

%% Blocks: a little of GitHub's Markdown

%  md_blocks(+Lines, -Blocks): h(Level, Text), p(Text), ul(Items) with
%  each item a list of blocks, table(Head, Rows), fence(Lang, Lines) and
%  output(Name, Lang, Lines).
md_blocks([], []).
md_blocks([L|Ls], Bs) :- blank(L), !, md_blocks(Ls, Bs).
md_blocks([L|Ls0], [output(Name, Lang, Body)|Bs]) :-
    string_concat("<!-- guide: ", R, L), !,
    split_string(R, " ", " ", [Name|_]),
    append(Inner, ["<!-- /guide -->"|Ls], Ls0), !,
    Inner = [Open|Rest], string_concat("```", Lang, Open),
    append(Body, [_], Rest),
    md_blocks(Ls, Bs).
md_blocks([L|Ls0], Bs) :- string_concat("<!--", _, L), !,
    (   sub_string(L, _, _, _, "-->") -> Ls = Ls0
    ;   append(_, [E|Ls], Ls0), sub_string(E, _, _, _, "-->") -> true
    ;   Ls = []
    ),
    md_blocks(Ls, Bs).
md_blocks([L|Ls0], [fence(Lang, Body)|Bs]) :- string_concat("```", Lang0, L), !,
    split_string(Lang0, "", " ", [Lang]),
    (   append(Body, [End|Ls], Ls0), string_concat("```", _, End) -> true
    ;   Body = Ls0, Ls = []
    ),
    md_blocks(Ls, Bs).
md_blocks([L|Ls0], [h(N, T)|Bs]) :- md_heading(L, N, T), !, md_blocks(Ls0, Bs).
md_blocks([L|Ls0], [table(Head, Rows)|Bs]) :-
    table_line(L, Head), Ls0 = [Sep|Ls1], table_line(Sep, Cells), maplist(rule_cell, Cells), !,
    take_table(Ls1, Rows, Ls), md_blocks(Ls, Bs).
md_blocks([L|Ls0], [ul(Items)|Bs]) :- item_start(L, _), !,
    md_items([L|Ls0], Items, Ls), md_blocks(Ls, Bs).
md_blocks([L|Ls0], [p(Text)|Bs]) :-
    md_para(Ls0, Para, Ls),
    maplist([S0, S]>>split_string(S0, "", " ", [S]), [L|Para], Ws),
    atomic_list_concat(Ws, ' ', A), atom_string(A, Text),
    md_blocks(Ls, Bs).

md_heading(L, N, T) :-
    string_codes(L, Cs), phrase(hashes(N), Cs, [0' |Rest]), N >= 1, N =< 6, !,
    string_codes(T0, Rest), split_string(T0, "", " ", [T]).

hashes(N) --> "#", !, hashes(N0), { N is N0 + 1 }.
hashes(0) --> [].

md_para([L|Ls0], [L|Ps], Ls) :-
    \+ blank(L), \+ md_heading(L, _, _), \+ string_concat("```", _, L),
    \+ string_concat("<!--", _, L), \+ item_start(L, _), \+ string_concat("|", _, L), !,
    md_para(Ls0, Ps, Ls).
md_para(Ls, [], Ls).

%  An item is its first line and the lines indented under it, blank
%  lines between them included, read again as blocks.
md_items([L|Ls0], [Bs|Items], Ls) :-
    item_start(L, First),
    take_item(Ls0, Cont0, Ls1),
    maplist(undent2, Cont0, Cont),
    md_blocks([First|Cont], Bs),
    (   Ls1 = [L1|_], item_start(L1, _) -> md_items(Ls1, Items, Ls)
    ;   Ls1 = [B, L1|_], blank(B), item_start(L1, _) -> Ls1 = [_|Ls2], md_items(Ls2, Items, Ls)
    ;   Items = [], Ls = Ls1
    ).

take_item([L|Ls0], [L|Cs], Ls) :- \+ blank(L), indent(L, I), I >= 2, !, take_item(Ls0, Cs, Ls).
take_item([B, L|Ls0], [B|Cs], Ls) :- blank(B), \+ blank(L), indent(L, I), I >= 2, !,
    take_item([L|Ls0], Cs, Ls).
take_item(Ls, [], Ls).

undent2(L, S) :- ( blank(L) -> S = "" ; sub_string(L, 2, _, 0, S) ).

%% The first pass: anchors and glossary terms

guide_prepass(Blocks) :-
    nb_setval(guide_h2, ""),
    prepass(Blocks).

prepass([]).
prepass([B|Bs]) :- prepass_(B), prepass(Bs).

prepass_(h(N, T)) :- !,
    heading_id(T, Id), heading_modules(T, Mods), nb_getval(guide_doc, D),
    assertz(guide_heading(D, Id, N, T, Mods)),
    ( N =:= 2 -> nb_setval(guide_h2, T) ; true ).
prepass_(p(T)) :- nb_getval(guide_h2, "Glossary"), gloss_names(T, Names), !,
    Names = [First|_], gloss_id(First, Id), nb_getval(guide_doc, D),
    forall(member(N, Names), ( string_lower(N, K), assertz(guide_gloss(D, K, Id)) )).
prepass_(ul(Items)) :- !, maplist(prepass, Items).
prepass_(_).

%  gloss_names(+Text, -Names): Text is a glossary entry, **a / b**: ...
gloss_names(T, Names) :-
    string_concat("**", R, T), sub_string(R, B, _, _, "**:"), !,
    sub_string(R, 0, B, _, Head),
    split_string(Head, "/", " ", Names).

gloss_id(Name, Id) :- slug(Name, S), atom_concat('g-', S, Id).

%  heading_id(+Title, -Id): GitHub's anchor for a heading: lower case,
%  letters, digits, spaces, - and _ kept, spaces as -. A repeated anchor
%  gets -1, -2, ...
heading_id(T, Id) :-
    slug(T, Id0),
    (   retract(guide_slug(Id0, N0))
    ->  N is N0 + 1, assertz(guide_slug(Id0, N)), format(atom(Id), "~w-~w", [Id0, N])
    ;   assertz(guide_slug(Id0, 0)), Id = Id0
    ).

slug(T, Id) :-
    string_lower(T, L), string_codes(L, Cs0),
    include([C]>>( code_type(C, alnum) ; memberchk(C, `-_ `) ), Cs0, Cs1),
    maplist([C0, C]>>( C0 == 0'  -> C = 0'- ; C = C0 ), Cs1, Cs),
    atom_codes(Id, Cs).

heading_modules(T, Mods) :-
    split_string(T, " ,:()`", " ,:()`", Ws),
    findall(M, ( member(W, Ws), string_concat(M0, ".pl", W), atom_string(M, M0), guide_module(M) ), Mods).

%% The page

guide_page(Doc, Blocks) -->
    { findall(Id-T, guide_heading(Doc, Id, 1, T, _), [_-Title|_]), doc_label(Doc, Label) },
    shell(Title, ( el(a, crumb, [href="../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
                   el(a, crumb, [href="index.html"], "nanofil"), el(span, "crumb-sep", "›"),
                   el(span, "crumb current", esc(Doc)) ),
          ( rocq_style(Doc),
            el(nav, "toc dterm-nav guide-nav",
               ( el(div, "toc-title", esc(Label)), guide_toc(Doc) )),
            el(article, "dterm guide",
               el(div, "prose guide-prose", gblocks(Blocks))) )).

%  A document about Rocq sets its Rocq with dterm-rocq's stylesheet
%  (rocq/, beside the pages).
rocq_style(Doc) --> { guide_rocq(Doc) }, !, "<link rel=\"stylesheet\" href=\"rocq/dterm-rocq.css\">\n".
rocq_style(_) --> [].

guide_toc(Doc) -->
    { findall(N-(Id-T), ( guide_heading(Doc, Id, N, T, _), N >= 2, N =< 3 ), Hs) },
    el(ul, none, toc_items(Hs)).

toc_items([]) --> [].
toc_items([2-(Id-T)|Hs0]) -->
    { take_h3(Hs0, Subs, Hs), atom_concat('#', Id, Href) },
    el(li, "nav-section", ( el(a, none, [href=Href], toc_text(T)),
                            ( { Subs == [] } -> [] ; el(ul, none, seq(Subs, toc_sub)) ) )),
    toc_items(Hs).
toc_items([3-H|Hs]) --> toc_sub(H), toc_items(Hs).

take_h3([3-H|Hs0], [H|Hs1], Hs) :- !, take_h3(Hs0, Hs1, Hs).
take_h3(Hs, [], Hs).

toc_sub(Id-T) --> { atom_concat('#', Id, Href) }, el(li, "nav-pred", el(a, none, [href=Href], toc_text(T))).

toc_text(T) --> { string_codes(T, Cs0), exclude(==(0'`), Cs0, Cs) }, esc(Cs).

gblocks([]) --> [].
gblocks([B|Bs]) --> gblock(B), gblocks(Bs).

gblock(h(N, T)) -->
    { nb_getval(guide_doc, D), guide_heading(D, Id, N, T, Mods), !,
      ( N >= 2 -> nb_setval(guide_sec, sec(Id, T, Mods)) ; true ),
      ( N =:= 2 -> nb_setval(guide_h2, T) ; true ),
      format(atom(H), "h~d", [N]),
      ( N =:= 1 -> C = "source-title" ; C = "guide-h" ) },
    el(H, C, [id=Id], gtext(T)).
gblock(p(T)) -->
    { nb_getval(guide_h2, "Glossary"), gloss_names(T, [First|_]) }, !,
    { gloss_id(First, Id), nb_setval(guide_entry, Id), retractall(guide_entry_ref(_)),
      string_codes(T, Cs), phrase(gi(Cs), Body),
      ( guide_entry_ref(_) -> true ; broken("glossary entry ~w names no source", [First]) ),
      nb_setval(guide_entry, none) },
    el(p, "gloss-entry", [id=Id], raw(Body)).
gblock(p(T)) -->
    { string_concat("**[", R, T), sub_string(R, B, _, _, ".pl]"), sub_string(R, 0, B, _, M0),
      atom_string(M, M0), guide_module(M) }, !,
    { atom_concat('map-', M, Id),
      nb_getval(guide_sec, Sec), Sec = sec(SId, ST, Mods),
      nb_setval(guide_sec, sec(SId, ST, [M|Mods])),
      nb_getval(guide_doc, D), assertz(guide_mention(D, M, map, Id, "the module map")),
      string_codes(T, Cs), phrase(gi(Cs), Body),
      nb_setval(guide_sec, Sec) },
    el(p, "map-entry", [id=Id], raw(Body)).
gblock(p(T)) --> { string_codes(T, Cs) }, el(p, none, gi(Cs)).
gblock(ul(Items)) --> el(ul, none, seq(Items, gitem)).
gblock(table(Head, Rows)) -->
    el(table, "prose-table",
       ( el(thead, none, el(tr, none, seq(Head, gcell(th)))),
         el(tbody, none, seq(Rows, grow)) )).
gblock(fence("prolog", Lines)) -->
    { atomic_list_concat(Lines, '\n', T0), atom_string(T0, T),
      \+ sub_string(T, _, _, _, "%"), fence_terms(T, Ts), Ts \== [] }, !,
    el(div, "prose-terms", seq(Ts, gclause)).
gblock(fence("diagram", Lines)) --> !, diagram(Lines, guide).
gblock(fence(Lang, Lines)) --> { memberchk(Lang, ["rocq", "coq"]) }, !, rocq_fence(Lines).
gblock(fence(Lang, Lines)) --> gfence(Lang, Lines).
gblock(output(Name, _, _)) --> { guide_output(Name, Items) }, !,
    el(div, "prose-terms guide-output", ['data-output'=Name], seq(Items, out_item)).
gblock(output(Name, Lang, Lines)) -->
    { Lang == "prolog" -> broken("output ~w has no terms in docs/guide/outputs.pl", [Name]) ; true },
    gfence(Lang, Lines).

gfence(Lang, Lines) -->
    { atomic_list_concat(Lines, '\n', T),
      ( Lang == "" -> C = "fence" ; atom_concat('fence lang-', Lang, C) ) },
    el(pre, C, esc(T)).

gitem(Bs) --> el(li, none, seq(Bs, gblock)).
grow(Cells) --> el(tr, none, seq(Cells, gcell(td))).
gcell(Tag, Text) --> { string_codes(Text, Cs) }, el(Tag, none, gi(Cs)).

%  A clause in a prolog fence the guide writes itself: a rule as head
%  over its goals, anything else as a term.
gclause((H :- B)) --> !,
    el(div, "clause rule",
       ( el(div, head, ( term(H, _, 1199, ctx(guide, head)), "\u00A0",
                         el(span, neck, [title=":-"], "←") )),
         body(B, _, ctx(guide, goal)) )).
gclause(T) --> el(div, "clause item", term(T, _, 999, ctx(guide, data))).

out_item(term(T)) --> el(div, "clause item", term(T, _, 999, ctx(guide, data))).
out_item(comment(T)) -->
    el(div, "out-comment",
       ( "% ", ( { compound(T) } -> el(code, term, term(T, _, 999, ctx(guide, data))) ; esc(T) ) )).
out_item(text(S)) --> el(div, "out-text", esc(S)).
out_item(note(T, S)) -->
    el(div, "out-note-line",
       ( el(code, term, term(T, _, 999, ctx(guide, data))), " ", el(span, "out-note", esc(S)) )).

%% Inline text

%  gi(+Codes): a paragraph's text: `code`, **strong**, *emphasis*,
%  [links](url), predicate and module references, and plain text.
gi([]) --> [].
gi([0'`|Cs0]) --> { append(Code, [0'`|Cs], Cs0) }, !, gcode(Code), gi(Cs).
gi([0'*, 0'*|Cs0]) --> { append(In, [0'*, 0'*|Cs], Cs0), In \== [] }, !,
    el(strong, none, gi(In)), gi(Cs).
gi([0'*, C|Cs0]) -->
    { C \== 0'  , C \== 0'*, append(In, [0'*|Cs], [C|Cs0]), \+ memberchk(0'`, In),
      last(In, E), E \== 0'  , \+ ( Cs = [N|_], code_type(N, csym) ) }, !,
    gem(In), gi(Cs).
gi([0'[|Cs0]) -->
    { append(Txt, [0'], 0'(|Rest], Cs0), \+ memberchk(0'], Txt),
      append(Url, [0')|Cs], Rest), \+ memberchk(0' , Url) }, !,
    glink(Txt, Url), gi(Cs).
gi([0'/|Cs0]) --> { span(path_char, Cs0, P, Cs), P \== [] }, !, "/", esc(P), gi(Cs).
gi(Cs0) --> { word(Cs0, W, Cs1), W \== [] }, !, gword(W, Cs1).
gi([C|Cs]) --> esc_code(C), gi(Cs).

path_char(C) :- ( code_type(C, csym) ; memberchk(C, `.-/`) ), !.

%  gtext(+Text): text without links: a heading's or a link's.
gtext(T) --> { text_codes(T, Cs) }, gt(Cs).

gt([]) --> [].
gt([0'`|Cs0]) --> { append(Code, [0'`|Cs], Cs0) }, !,
    (   { code_term(Code, T) } -> el(code, term, term(T, _, 999, ctx(guide, data)))
    ;   el(code, none, esc(Code))
    ),
    gt(Cs).
gt([0'*, 0'*|Cs0]) --> { append(In, [0'*, 0'*|Cs], Cs0), In \== [] }, !, el(strong, none, gt(In)), gt(Cs).
gt([C|Cs]) --> esc_code(C), gt(Cs).

gword(W, [0':|Cs0]) -->
    { word(Cs0, W2, Cs1), W2 \== [], pred_ref(W2, Cs1, Ref0, PI, Cs), atom_codes(M, W) }, !,
    { append([W, `:`, Ref0], Ref) },
    gpred(M, PI, Ref), gi(Cs).
gword(W, Cs0) --> { pred_ref(W, Cs0, Ref, PI, Cs) }, !, gpred(_, PI, Ref), gi(Cs).
gword(W, [0'., 0'p, 0'l|Cs]) --> { \+ ( Cs = [C|_], code_type(C, csym) ) }, !,
    { append(W, `.pl`, Text) }, gmodule(W, esc(Text)), gi(Cs).
gword(W, Cs) --> esc(W), gi(Cs).

%  gcode(+Code): inline code: a predicate or module reference, a
%  glossary term, a term, or plain code.
gcode(Code) --> { code_pred(Code, M, PI) }, !, gpred(M, PI, Code).
gcode(Code) --> { append(W, `.pl`, Code), W \== [], maplist(word_char, W) }, !,
    gmodule(W, el(code, none, esc(Code))).
gcode(Code) --> { atom_codes(A, Code), gloss_link(A, Href) }, !,
    el(a, gloss, [href=Href], el(code, none, esc(Code))).
%  Rocq that only Rocq writes (Ret v, cap := None | Obj base, a Theorem)
%  is drawn as Rocq; a Prolog term as a term.
gcode(Code) --> { nb_getval(guide_doc, D), guide_rocq(D) }, rocq_inline(Code), !.
gcode(Code) --> { code_term(Code, T) }, !, el(code, term, term(T, _, 999, ctx(guide, data))).
gcode(Code) --> el(code, none, esc(Code)).

%  code_pred(+Code, ?Module, -PI): Code is name/N, name//N or
%  module:name/N.
code_pred(Code, M, PI) :-
    (   append(MW, [0':|Rest], Code), MW \== [], maplist(word_char, MW)
    ->  atom_codes(M, MW)
    ;   Rest = Code
    ),
    word(Rest, W, Cs1), W \== [], pred_ref(W, Cs1, _, PI, []).

gem(In) -->
    { atom_codes(A, In), gloss_link(A, Href) }, !,
    el(a, gloss, [href=Href], el(em, none, gt(In))).
gem(In) --> el(em, none, gi(In)).

%  mention(+Module, +What): the current section names Module's
%  predicate What, or Module itself (module).
mention(M, What) :-
    nb_getval(guide_doc, D), nb_getval(guide_sec, sec(SId, ST, _)),
    assertz(guide_mention(D, M, What, SId, ST)).

%  gloss_link(+Word, -Href): Word, or its singular, is a glossary term of
%  this document or another, outside that term's own entry.
gloss_link(A, Href) :-
    downcase_atom(A, L), atom_string(L, S),
    (   gloss_entry(S, D, Id) -> true
    ;   string_concat(S1, "s", S), gloss_entry(S1, D, Id)
    ),
    nb_getval(guide_doc, Here),
    (   D == Here -> \+ nb_getval(guide_entry, Id), atom_concat('#', Id, Href)
    ;   format(atom(Href), "~w.html#~w", [D, Id])
    ).

gloss_entry(S, D, Id) :-
    nb_getval(guide_doc, Here),
    (   guide_gloss(Here, S, Id) -> D = Here
    ;   guide_gloss(D, S, Id)
    ), !.

%  gpred(?Module, +PI, +Ref): a link to PI's definition with its
%  signature card; a library predicate is plain code.
gpred(M0, PI, Ref) --> { guide_resolve(M0, PI, M, Id) }, !,
    { mention(M, PI), assertz(guide_entry_ref(M)),
      uri_encoded(fragment, Id, Frag), format(atom(Href), "~w.html#~w", [M, Frag]) },
    el(span, pref, ( el(a, ref, [href=Href], el(code, none, esc(Ref))), card(M, PI) )).
gpred(M0, N/A, Ref) --> { var(M0), library_pred(N, A) }, !, el(code, none, esc(Ref)).
gpred(_, doc/3, Ref) --> !,
    % doc/3 is the documentation relation (docs/dterm.md), not a predicate.
    el(a, ref, [href="docs/dterm.html"], el(code, none, esc(Ref))).
gpred(_, _, Ref) --> { broken("~s does not name one predicate of nanofil/src", [Ref]) },
    el(code, broken, esc(Ref)).

%  guide_resolve(?Module, +PI, -Def, -Id): PI in Module, or the one
%  definition of PI, or the one in a module the section names.
guide_resolve(M, PI, M, Id) :- nonvar(M), !, defined(PI, M, Id).
guide_resolve(_, PI, M, Id) :-
    findall(F-I, defined(PI, F, I), Ds),
    (   Ds = [M-Id] -> true
    ;   nb_getval(guide_sec, sec(_, _, Mods)),
        include([F-_]>>memberchk(F, Mods), Ds, [M-Id])
    ).

library_pred(N, A) :-
    functor(H, N, A),
    (   predicate_property(system:H, defined) -> true
    ;   catch('$in_library'(N, A, _), _, fail)
    ).

gmodule(W, Text) -->
    { atom_codes(M, W) },
    (   { guide_module(M) }
    ->  { mention(M, module), assertz(guide_entry_ref(M)),
          atom_concat(M, '.html', Href) },
        el(a, "ref module", [href=Href], Text)
    ;   { broken("~w.pl is not a module of nanofil/src", [M]) },
        el(span, broken, Text)
    ).

%  glink(+Text, +Url): a Markdown link, its target as the site has it.
glink(Txt, Url0) -->
    { atom_codes(Url, Url0), link_target(Url, Href, Mod) }, !,
    (   { Mod == none } -> [] 
    ;   { mention(Mod, module), assertz(guide_entry_ref(Mod)) }
    ),
    el(a, none, [href=Href], gt(Txt)).
glink(Txt, Url0) --> { broken("link to ~s does not resolve", [Url0]) }, el(span, broken, gt(Txt)).

link_target(Url, Url, none) :- sub_atom(Url, B, _, _, ':'), B > 0, !.
link_target(Url, Url, none) :- atom_concat('#', Frag, Url), !,
    nb_getval(guide_doc, D),
    ( guide_heading(D, Frag, _, _, _) ; guide_gloss(D, _, Frag) ), !.
link_target(Url, Href, M) :-
    atom_concat('../src/', F, Url), file_name_extension(M, pl, F), guide_module(M), !,
    atom_concat(M, '.html', Href).
link_target(Url, Href, none) :-
    split_atom_fragment(Url, Path, Frag),
    nb_getval(guide_dir, Dir), directory_file_path(Dir, Path, Abs),
    linked_file(Dir, Path, Abs),
    (   \+ sub_atom(Path, _, _, _, '/'), file_name_extension(Name, md, Path)
    ->  (   nb_getval(guide_docs, Docs), memberchk(Name, Docs)
        ->  format(atom(Href), "~w.html~w", [Name, Frag])
        ;   format(atom(Href), "docs/~w.html~w", [Name, Frag])
        )
    ;   file_name_extension(_, nix, Path), nix_page(Path, Page)
    ->  format(atom(Href), "../nix/~w~w", [Page, Frag])
    ;   file_name_extension(_, v, Path), rocq_page(Path, Page)
    ->  rocq_anchor(Abs, Path, Frag),
        format(atom(Href), "rocq/~w~w", [Page, Frag])
    ;   github(G),
        (   atom_concat('../', Rel, Path) -> true ; atom_concat('docs/', Path, Rel) ),
        format(atom(Href), "~w~w~w", [G, Rel, Frag])
    ).

%  nix_page(+Path, -Page): the dterm-nix page of a .nix file a link from
%  nanofil/docs names: ../nix/check.nix is nanofil-nix-check.html.
nix_page(Path, Page) :-
    atomic_list_concat(Parts0, '/', Path),
    append([nanofil, docs], Parts0, Parts1),
    foldl(rel_part, Parts1, [], RevParts), reverse(RevParts, Parts),
    Parts \== [], Parts \= [experiments|_],
    atomic_list_concat(Parts, '-', B0),
    file_name_extension(B, nix, B0), file_name_extension(B, html, Page).

%  rocq_page(+Path, -Page): the dterm-rocq page of a .v file a link from
%  nanofil/docs names: ../rocq/theories/Values.v is
%  rocq-theories-Values.html, in the site's nanofil/rocq/.
rocq_page(Path, Page) :-
    atomic_list_concat(Parts0, '/', Path),
    append([nanofil, docs], Parts0, Parts1),
    foldl(rel_part, Parts1, [], RevParts), reverse(RevParts, [nanofil|Parts]),
    atomic_list_concat(Parts, '-', B0),
    file_name_extension(B, v, B0), file_name_extension(B, html, Page).

%  rocq_anchor(+Abs, +Path, +Frag): a link's #Name is a name the .v file
%  defines at its top level (dterm-rocq's anchor for it), so a renamed
%  definition breaks the link. Where the file is not in the sources (the
%  site has only some of nanofil), it is left to the Nix check.
rocq_anchor(_, _, '') :- !.
rocq_anchor(Abs, _, Frag) :- \+ exists_file(Abs), !, Frag \== ''.
rocq_anchor(Abs, _, Frag) :-
    atom_concat('#', Name, Frag),
    read_file_to_string(Abs, Text, [encoding(utf8)]),
    split_string(Text, "\n", "", Lines),
    member(L, Lines), split_string(L, " ", "", [W, N|_]),
    (   memberchk(W, ["Inductive", "Variant", "Record", "Structure", "Definition", "Fixpoint",
                      "Lemma", "Theorem", "Notation", "Module", "Class"])
    ->  atom_string(Name, N)
    ;   W == "|", atom_string(Name, N)
    ), !.
rocq_anchor(_, Path, Frag) :-
    broken("~w does not define ~w", [Path, Frag]).

rel_part('..', [_|Ps], Ps) :- !.
rel_part('.', Ps, Ps) :- !.
rel_part(P, Ps, [P|Ps]).

%  linked_file(+Dir, +Path, +Abs): the file a link names exists. The
%  site's sources hold only nanofil's docs, src and web (no bin/nanofil),
%  so there a link outside docs is left to the Nix check, which has the
%  whole tree.
linked_file(_, _, Abs) :- exists_file(Abs), !.
linked_file(Dir, Path, _) :-
    atom_concat('../', _, Path),
    directory_file_path(Dir, '../bin/nanofil', Bin), \+ exists_file(Bin).

split_atom_fragment(Url, Path, Frag) :-
    (   sub_atom(Url, B, _, _, '#') -> sub_atom(Url, 0, B, _, Path), sub_atom(Url, B, _, 0, Frag)
    ;   Path = Url, Frag = ''
    ).

%% Signature cards

%  card(+Module, +PI): PI's signature and the first paragraph of its
%  documentation, shown when the reference is hovered.
card(M, PI) --> { pred_doc(M, PI, Key, Doc), card_parts(Doc, Key, Sigs, Para) }, !,
    el(span, sigcard, ['aria-hidden'=true],
       ( el(span, "card-mod", ( esc(M), ".pl" )),
         seq(Sigs, card_sig),
         ( { Para == "" } -> [] ; el(span, "card-text", ctext(Para)) ) )).
card(M, N/A) -->
    el(span, sigcard, ['aria-hidden'=true],
       ( el(span, "card-mod", ( esc(M), ".pl" )), el(span, "card-sig", ( esc(N), "/", esc(A) )),
         el(span, "card-text", "not documented") )).

card_parts(doc(group(_, _, Texts)), _, Sigs, Para) :- !,
    partition([T]>>string_concat("%!", _, T), Texts, SigTexts, ProseTexts),
    maplist(sig_parse, SigTexts, Sigs),
    first_para(group(note, 0, ProseTexts), Para).
card_parts(dterm(H, Det, Ps, _, _), Key, [sig(H is Det, Dcg)], Para) :- !,
    ( Key = _//_ -> Dcg = true ; Dcg = false ),
    ( doc_paragraphs(Ps, [Para|_]) -> true ; Para = "" ).
card_parts(note(G), Key, Sigs, Para) :-
    group_text(G, Lines0), dedent(Lines0, Lines),
    atomic_list_concat(Lines, '\n', J0), atom_string(J0, J),
    key_name(Key, Name),
    (   sig_prefix(J, Name, SigText, Rest), sig_term(SigText, Sig), Sig = sig(_, _)
    ->  Sigs = [Sig], split_string(Rest, "\n", "", RLs), para_of(RLs, Para)
    ;   Sigs = [], para_of(Lines, Para)
    ).

first_para(G, Para) :- group_text(G, Lines0), dedent(Lines0, Lines), para_of(Lines, Para).

para_of(Lines0, Para) :-
    exclude_leading_blank(Lines0, Lines),
    (   append(P, [B|_], Lines), blank(B) -> true ; P = Lines ),
    maplist([S0, S]>>split_string(S0, "", " ", [S]), P, Ws),
    atomic_list_concat(Ws, ' ', A), atom_string(A, Para0),
    (   string_length(Para0, L), L > 360
    ->  sub_string(Para0, 0, 360, _, P1), string_concat(P1, "…", Para)
    ;   Para = Para0
    ).

card_sig(raw(S)) --> el(span, "card-sig", el(code, none, esc(S))).
card_sig(sig(T, Dcg)) -->
    { ( T = (H is Det) -> true ; H = T, Det = none ) },
    el(span, "card-sig",
       ( sig_head(H, guide),
         ( { Dcg == true } -> el(span, "kw dcg", "//") ; [] ),
         ( { Det == none } -> [] ; el(span, det, esc(Det)) ) )).

ctext(Text) --> { string_codes(Text, Cs) }, ct(Cs).
ct([]) --> [].
ct([0'`|Cs0]) --> { append(Code, [0'`|Cs], Cs0) }, !, el(code, none, esc(Code)), ct(Cs).
ct([C|Cs]) --> esc_code(C), ct(Cs).

%% Links from the module pages back to the guide

%  guide_backlinks(+Base): for each document, its sections that name
%  Base.pl in their heading and its module-map entry, or, in a document
%  without a module map, the sections that mention the module.
guide_backlinks(Base) -->
    { ( nb_current(guide_docs, Docs) -> true ; Docs = [] ) },
    seq(Docs, doc_backlinks(Base)).

doc_backlinks(Base, D) -->
    { findall(Id-T, ( guide_heading(D, Id, N, T, Mods), N >= 2, memberchk(Base, Mods) ), Hs0),
      ( guide_mention(D, Base, map, MapId, _) -> Map = [MapId] ; Map = [] ),
      (   \+ guide_mention(D, _, map, _, _)
      ->  findall(Id-T, guide_mention(D, Base, module, Id, T), Hs1), list_to_set(Hs1, Hs)
      ;   Hs = Hs0
      ),
      doc_label(D, Label) },
    (   { Hs == [], Map == [] } -> []
    ;   el(aside, "guide-links",
           ( el(span, label, ( "in ", esc(Label) )), seq(Hs, guide_section_link(D)),
             seq(Map, guide_map_link(D)) ))
    ).

guide_section_link(D, Id-T) -->
    { format(atom(Href), "~w.html#~w", [D, Id]) }, el(a, none, [href=Href], toc_text(T)).
guide_map_link(D, Id) -->
    { format(atom(Href), "~w.html#~w", [D, Id]) }, el(a, none, [href=Href], "the module map").

%  The sections of each document that mention predicate PI of File, as
%  Doc-Secs with Secs a list of Id-Title, in the order of the documents.
guide_pred_sections(File, PI, DocSecs) :-
    ( nb_current(guide_docs, Docs) -> true ; Docs = [] ),
    findall(D-Secs, ( member(D, Docs),
                      findall(Id-T, guide_mention(D, File, PI, Id, T), Secs0),
                      list_to_set(Secs0, Secs), Secs \== [] ), DocSecs).
