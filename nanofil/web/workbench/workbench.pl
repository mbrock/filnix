/*  The dterm workbench's samples: representative terms drawn by dterm.pl
    exactly as the pages draw them, for index.html to set side by side
    under different type.

    Usage: swipl workbench.pl OUT SRC-DIR. Writes OUT/samples.html: from
    SRC-DIR, predicates with nested conditionals, documentation and
    examples, and DCG clauses with lists and tails; from samples.pl, C
    syntax, IR and assembly drawn as the playground draws them
    (../play/play_view.pl). Each is drawn once per line length at which a
    term breaks (dterm.pl's long_term/1), so the page can switch between
    them. SWI-Prolog only, like dterm.
*/
:- module(workbench, []).
:- encoding(utf8).

:- use_module(library(lists)).
:- use_module(library(apply)).

% dterm's main would draw the whole wiki; play_view.pl loads it after.
:- asserta((user:term_expansion((:- initialization(main, main)), []) :-
               prolog_load_context(module, dterm))).
:- use_module('../dterm').
% play_view.pl declares no encoding, and the Nix build has no UTF-8 locale.
:- load_files('../play/play_view', [encoding(utf8)]).
:- consult(samples).

:- initialization(main, main).

%  sample(Title, Note, What): the samples, in order.
sample("A clause with nested conditionals",
       "c_lower.pl: an if-then-else whose branch holds another, drawn as a flow.",
       pred(c_lower, define_global/7)).
sample("Documentation, examples and cases",
       "c_types.pl: a doc/3 signature, argument table and checked examples, then numbered clauses with a disjunction and a cut.",
       pred(c_types, usual_arith_conversion/3)).
sample("Lists, tails and a DCG",
       "c_pp.pl: list patterns with tails, terminals, {} goals and operators.",
       pred(c_pp, located_splice/4)).
sample("", "", pred(c_pp, pp_tokens//3)).
sample("IR",
       "A function as the playground's IR tab draws it: its head over its blocks.",
       ir).
sample("Assembly",
       "asm.pl line terms beside the AT&T lines they print as.",
       asm).
sample("C syntax",
       "c_parse/2's terms for a struct and a function: long terms, broken one argument per row.",
       c).

%  The lengths at which a term is drawn broken; 0 for never.
long(48).
long(60).
long(72).
long(80).
long(90).
long(0).

main :-
    current_prolog_flag(argv, [Out, Dir]),
    findall(F, ( member(B, [c_lower, c_types, c_pp]),
                 file_name_extension(B, pl, N), directory_file_path(Dir, N, F) ), Files),
    maplist(dterm:read_source, Files, Sources),
    maplist(dterm:index_source, Sources),
    maplist(dterm:run_examples(Files), Sources),
    directory_file_path(Out, 'samples.html', Path),
    dterm:write_page(Path, workbench:page(Sources)).

page(Sources) -->
    "<!doctype html>\n<html lang=\"en\" data-long=\"80\">\n<head>\n<meta charset=\"utf-8\">\n",
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
    "<title>dterm samples</title>\n",
    "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=Public+Sans:ital,wght@0,100..900;1,100..900&amp;display=swap\">\n",
    "<link rel=\"stylesheet\" href=\"../../style.css\">\n",
    "<link rel=\"stylesheet\" href=\"../dterm.css\">\n",
    "<link rel=\"stylesheet\" href=\"../play/play.css\">\n",
    "<link rel=\"stylesheet\" href=\"samples.css\">\n",
    "</head>\n<body>\n",
    el(article, "dterm play wb", seq_samples(Sources)),
    "\n<script src=\"../dterm.js\"></script>\n<script src=\"samples.js\"></script>\n</body>\n</html>\n".

seq_samples(Sources) -->
    { findall(T-N-W, sample(T, N, W), Ss) },
    seq(Ss, sample_(Sources)).

sample_(Sources, Title-Note-What) -->
    ( { Title == "" } -> [] ; el(h2, none, dterm:esc(Title)) ),
    ( { Note == "" } -> [] ; el(p, "wb-note", dterm:esc(Note)) ),
    { findall(L, long(L), Ls) },
    seq(Ls, variant(Sources, What)).

variant(Sources, What, L) -->
    { ( L =:= 0 -> nb_setval(dterm_long, none) ; nb_setval(dterm_long, L) ) },
    el(div, "wb-v", ['data-long'=L], draw(What, Sources)).

draw(pred(Base, Key), Sources) -->
    { memberchk(src(Base, Text, Lines, Events), Sources),
      nb_setval(dterm_text, Text), nb_setval(dterm_lines, Lines),
      nb_setval(dterm_file, Base), nb_setval(dterm_notes, []),
      dterm:entries(Events, Entries),
      memberchk(pred(Key, Doc, Items), Entries) },
    dterm:pred_(Key, Doc, Items, Base).
draw(ir, _) -->
    { sample_ir(F) },
    el(div, "pane", ['data-slot'=ir], play_view:ir_item('sample.c', F)).
draw(asm, _) -->
    { findall(T-S, sample_asm(T, S), Ls) },
    el(div, "pane", ['data-slot'=asm], el(table, asm, seq(Ls, asm_row))).
draw(c, _) -->
    { findall(I, sample_c(I), Is) },
    el(div, "pane", ['data-slot'=c], seq(Is, play_view:item_)).

asm_row(T-S) -->
    { T = label(_) -> Class = label ; Class = none },
    el(tr, Class, ( el(td, term, dterm:term(T, _, 999, ctx(play, data))),
                    el(td, att, el(code, none, dterm:esc(S))) )).

% dterm's el//3 calls its body in module dterm, so the elements are
% built here, as in play_view.pl.
el(T, C, B) --> el(T, C, [], B).
el(T, C, As, B) -->
    "<", dterm:raw(T),
    (   { C == none } -> [] ; " class=\"", dterm:raw(C), "\"" ),
    attrs(As), ">", B, "</", dterm:raw(T), ">".

attrs([]) --> [].
attrs([K=V|As]) --> " ", dterm:raw(K), "=\"", dterm:esc(V), "\"", attrs(As).

seq([], _) --> [].
seq([X|Xs], G) --> call(G, X), seq(Xs, G).
