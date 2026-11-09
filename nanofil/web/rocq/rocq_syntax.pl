:- encoding(utf8).
/*  rocq_syntax: Rocq (Coq) source as Prolog terms, with positions and
    comments.

    A lexer and a DCG for the vernacular and Gallina that the formal
    campaign writes (docs/formal.md), so that dterm-rocq can draw Rocq the
    way dterm draws Prolog. Nothing is desugared: every node keeps the
    character span it came from, numbers and strings keep their spelling,
    and comments are returned beside the sentences, so the drawing can put
    each where it was written. Tactics keep their control structure and
    use Gallina terms for embedded expressions; unfamiliar atomic syntax
    keeps its tokens, rather than being guessed or dropped.

    Every node's first argument is its span From-To (character offsets,
    To exclusive). Terms:

    | Term | Gallina |
    |---|---|
    | `id(P, Name)`, `hole(P)` | a name, possibly qualified (`Z.add`), and `_` |
    | `num(P, Text)`, `str(P, Text)` | literals, in their spelling |
    | `app(P, F, Args)`, `explicit(P, Name)` | `F A B`, and `@f` |
    | `bin(P, Op, L, R)`, `pre(P, Op, E)` | infix and prefix notations, Op an atom |
    | `chain(P, Ops, Es)` | `a <= b < c`, Ops `['<=', <]` and Es `[a, b, c]` |
    | `paren(P, E)`, `cast(P, E, T)`, `tuple(P, Es)`, `orpat(P, Ps)` | `(E)`, `(E : T)`, `(A, B)`, `(A \| B)` |
    | `forall(P, Bs, B)`, `exists(P, Bs, B)`, `fun(P, Bs, B)` | binders over a body |
    | `let(P, Lhs, Ty, V, B)` | `let x := V in B`; Lhs `name(N, Bs)` or `tuple(Ns)` |
    | `letstar(P, N, V, B)`, `letpat(P, Pat, V, B)` | `let* x := V in B`, `let '(a, b) := V in B` |
    | `letfix(P, N, Bs, Ty, V, B)` | `let fix f Bs : Ty := V in B` |
    | `if(P, C, T, E)` | `if C then T else E` |
    | `match(P, Scrutinees, Return, Branches)` | `br(Alternatives, Rhs)`, each alternative a list of patterns |
    | `list(P, Es)`, `record(P, Fields)` | `[a; b]` and `{\| f := e \|}`, fields `fld(P, Name, E)` |
    | `scope(P, E, Key)`, `braces(P, E)`, `sig(P, N, T, Q)` | `E%Key`, `{E}`, `{ x : T \| Q }` |
    | `fix(P, N, Bs, Ty, B)`, `named(P, X, E)` | `fix f Bs : Ty := B`, an argument `(x:=E)` |
    | `aspat(P, Pat, N)`, `bits(P, E, Ds)` | `Pat as n` in a pattern, a positive's binary digits `p~0~1` (Ds `'01'`) |

    A binder is `b(P, Kind, Names, Type)`: Kind `paren`, `brace`, `bare`,
    `struct` (`{struct x}`) or `pattern(Pat)` (`'(a, b)`, Names `[]`),
    Names a list of `n(P, Name)`, Type `none` when there is none.

    Sentences are the vernacular, each `dir/2`, `ind/3`, `rec/7`, `def/6`,
    `thm/5`, `decl/3`, `notation/5`, `module/5`, `endm/2` or `raw/2` (one
    the grammar does not read), and the file is a tree of them (rocq_read_file/3):
    a module or section holds its sentences, and a theorem its proof,
    `pf(Steps, End)`, each step `step(P, Bullets, Toks)`.

    Comments are `cm(From, To, Text)`, Text with its markers.
*/
:- module(rocq_syntax, [rocq_read_file/3, rocq_parse_codes/3, rocq_fragment_codes/2, rocq_notations/1, rocq_set_notations/1,
                        rocq_tactic_tokens/2, rocq_focus_tokens/4, rocq_lex/3, node_pos/2, binop/3, notation_fold/3]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(readutil)).

%  rocq_read_file(+File, -Text, -Rocq): Rocq is rocq(Items, Comments).
%  The infix notations of the files beside it that it imports are its
%  operators too (SepListSum.v reads Sep.v's **).
rocq_read_file(File, Text, rocq(Items, Cms)) :-
    read_file_to_string(File, Text, [encoding(utf8)]),
    string_codes(Text, Cs),
    file_directory_name(File, Dir),
    (   rocq_parse_codes(Cs, Dir, Items, Cms) -> true
    ;   nb_getval(rocq_far, Far), offset_line_col(Cs, Far, L, C),
        format(user_error, "~w:~w:~w: Rocq lexical error~n", [File, L, C]),
        fail
    ).

%  rocq_parse_codes(+Codes, -Items, -Comments). A sentence the grammar
%  cannot read is raw(P, Keyword); the file parses all the same.
rocq_parse_codes(Cs, Items, Cms) :- rocq_parse_codes(Cs, none, Items, Cms).

rocq_parse_codes(Cs, Dir, Items, Cms) :-
    retractall(notation_op(_, _, _)), retractall(notation_fold(_, _, _)),
    rocq_lex(Cs, Toks, Cms),
    chunks(Toks, Chunks),
    ( Dir == none -> true ; import_notations(Dir, Chunks) ),
    events(Chunks, vernac, Events),
    phrase(top(Items), Events), !.

%  The notations a file declares (but not its Local ones), for each file
%  of Dir that a Require Import or Export of Chunks names.
import_notations(Dir, Chunks) :-
    forall(( member(c(Ts, _), Chunks), Ts = [t(id(K), _, _)|_], memberchk(K, ['From', 'Require', 'Import', 'Export']),
             append(_, [t(id(I), _, _)|Ms], Ts), memberchk(I, ['Import', 'Export']),
             member(t(id(M), _, _), Ms), file_name_extension(M, v, B), directory_file_path(Dir, B, F),
             exists_file(F) ),
           file_notations(F)).

file_notations(F) :-
    read_file_to_string(F, Text, [encoding(utf8)]), string_codes(Text, Cs),
    rocq_lex(Cs, Toks, _), chunks(Toks, Chunks),
    forall(( member(c(Ts, To), Chunks), Ts = [t(id(K), From, _)|_], memberchk(K, ['Notation', 'Infix']) ),
           ( sentence_(Ts, From-To, _) -> true ; true )).

%  rocq_notations(-Ns), rocq_set_notations(+Ns): the operators and folds
%  the last file read declared, to draw its page with after others were
%  read.
rocq_notations(Ns) :- findall(op(O, L, A), notation_op(O, L, A), Os), findall(fold(F, N, O), notation_fold(F, N, O), Fs),
    append(Os, Fs, Ns).
rocq_set_notations(Ns) :-
    retractall(notation_op(_, _, _)), retractall(notation_fold(_, _, _)),
    forall(member(op(O, L, A), Ns), assertz(notation_op(O, L, A))),
    forall(member(fold(F, N, O), Ns), assertz(notation_fold(F, N, O))).

%  An End that closes nothing stays a sentence of its own.
top([I|Is]) --> item(I), !, top(Is).
top([E|Is]) --> [sent(E)], !, top(Is).
top(Is) --> [_], !, top(Is).
top([]) --> [].

node_pos(N, P) :- arg(1, N, P).

offset_line_col(Cs, O, L, C) :-
    length(Pre, O), append(Pre, _, Cs), !,
    include(==(0'\n), Pre, NLs), length(NLs, L0), L is L0 + 1,
    (   append(_, [0'\n|Last], Pre), \+ memberchk(0'\n, Last) -> length(Last, C0) ; length(Pre, C0) ),
    C is C0 + 1.
offset_line_col(_, _, 0, 0).

%% Lexing

%  rocq_lex(+Codes, -Tokens, -Comments): tokens t(Kind, From, To), Kind
%  id(A), kw(A), num(A), str(S), sym(A), p(A) (punctuation) or dot, the
%  full stop that ends a sentence.
rocq_lex(Cs, Toks, Cms) :- nb_setval(rocq_far, 0), lex(Cs, 0, Toks, Cms).

lex(Cs0, O0, Toks, Cms) :-
    skip(Cs0, O0, Cs1, O1, Cms, Cms1),
    (   Cs1 == [] -> Toks = [], Cms1 = []
    ;   token(Cs1, O1, K, Cs2, O2) -> Toks = [t(K, O1, O2)|Toks1], lex(Cs2, O2, Toks1, Cms1)
    ;   nb_setval(rocq_far, O1), fail
    ).

skip([C|Cs0], O0, Cs, O, Cms0, Cms) :- white(C), !, O1 is O0 + 1, skip(Cs0, O1, Cs, O, Cms0, Cms).
skip([0'(, 0'*|Cs0], O0, Cs, O, [cm(O0, O1, Text)|Cms0], Cms) :- !,
    cbody(Cs0, 1, Body, Cs1), length(Body, N), O1 is O0 + 2 + N,
    string_codes(Text, [0'(, 0'*|Body]),
    skip(Cs1, O1, Cs, O, Cms0, Cms).
skip(Cs, O, Cs, O, Cms, Cms).

white(0' ). white(0'\t). white(0'\n). white(0'\r).

%  A comment's body through its closing *), nested comments and strings
%  inside it skipped as Rocq skips them.
cbody([0'*, 0')|Cs], 1, [0'*, 0')], Cs) :- !.
cbody([0'*, 0')|Cs0], D, [0'*, 0')|B], Cs) :- !, D1 is D - 1, cbody(Cs0, D1, B, Cs).
cbody([0'(, 0'*|Cs0], D, [0'(, 0'*|B], Cs) :- !, D1 is D + 1, cbody(Cs0, D1, B, Cs).
cbody([0'"|Cs0], D, [0'"|B], Cs) :- sbody(Cs0, S, Cs1), !,
    append(S, [0'"|B1], B), cbody(Cs1, D, B1, Cs).
cbody([C|Cs0], D, [C|B], Cs) :- cbody(Cs0, D, B, Cs).

%  A string's text as written ("" for a quote), up to its closing quote.
sbody([0'", 0'"|Cs0], [0'", 0'"|B], Cs) :- !, sbody(Cs0, B, Cs).
sbody([0'"|Cs], [], Cs) :- !.
sbody([C|Cs0], [C|B], Cs) :- sbody(Cs0, B, Cs).

token([0'"|Cs0], O0, str(S), Cs, O) :- !,
    sbody(Cs0, B, Cs), string_codes(S, B), length(B, N), O is O0 + N + 2.
token([0'.|Cs], O0, dot, Cs, O) :- ( Cs == [] ; Cs = [C|_], white(C) ), !, O is O0 + 1.
token([0'., 0'(|Cs], O0, sym('.('), Cs, O) :- !, O is O0 + 2.
%  stdpp's projections, written against their operand: lv.1, ps.*1.
token([0'., 0'*, D|Cs], O0, sym(A), Cs, O) :- memberchk(D, `12`), !, atom_codes(A, [0'., 0'*, D]), O is O0 + 3.
token([0'., D|Cs], O0, sym(A), Cs, O) :- memberchk(D, `12`), \+ ( Cs = [E|_], digit(E) ), !,
    atom_codes(A, [0'., D]), O is O0 + 2.
%  Iris's modalities, masks and pure brackets are a token each, so that
%  ⌜~ P⌝, ▷□ P or {⊤} do not run into the symbols beside them.
token([C|Cs], O0, sym(A), Cs, O) :- single_sym(C), !, char_code(A, C), O is O0 + 1.
%  Iris's function spaces of OFEs: A -d> B, A -n> B.
token([0'-, L, 0'>|Cs], O0, sym(A), Cs, O) :- memberchk(L, `dn`), !, atom_codes(A, [0'-, L, 0'>]), O is O0 + 3.
token([0'{, 0'||Cs], O0, p('{|'), Cs, O) :- !, O is O0 + 2.
token([0'|, 0'}|Cs], O0, p('|}'), Cs, O) :- !, O is O0 + 2.
token([C|Cs], O0, p(A), Cs, O) :- memberchk(C, `()[]{},;\``), !, char_code(A, C), O is O0 + 1.
token([0''|Cs], O0, p(''''), Cs, O) :- !, O is O0 + 1.
token(Cs0, O0, num(A), Cs, O) :- Cs0 = [C|_], digit(C), !,
    span(num_char, Cs0, D, Cs), atom_codes(A, D), length(D, N), O is O0 + N.
token(Cs0, O0, K, Cs, O) :- Cs0 = [C|_], id_start(C), !,
    ident(Cs0, I, Cs), atom_codes(A, I), length(I, N), O is O0 + N,
    ( keyword(A) -> K = kw(A) ; K = id(A) ).
token(Cs0, O0, sym(A), Cs, O) :-
    sym_run(Cs0, S, Cs), S \== [], atom_codes(A, S), length(S, N), O is O0 + N.
token([0'.|Cs], O0, sym('.'), Cs, O) :- O is O0 + 1.

%  A run of symbol characters, stopping before |}, and before ?x, an
%  existential variable, after its first character: <[l:=?Goal]>.
sym_run([0'|, 0'}|Cs], [], [0'|, 0'}|Cs]) :- !.
sym_run([C|Cs0], [C|S], Cs) :- sym_char(C), \+ single_sym(C), !, sym_more(Cs0, S, Cs).
sym_run(Cs, [], Cs).
sym_more([0'?, C|Cs], [], [0'?, C|Cs]) :- id_start(C), !.
sym_more(Cs0, S, Cs) :- sym_run(Cs0, S, Cs).

single_sym(C) :- memberchk(C, `⌜⌝▷□◇■⊤∅↑●◯£`).

keyword(A) :- memberchk(A, [forall, fun, exists, let, in, match, with, end, if, then, else,
                            as, return, fix, cofix]).

digit(C) :- between(0'0, 0'9, C).
num_char(C) :- digit(C) ; C == 0'_.
letter(C) :- between(0'a, 0'z, C) ; between(0'A, 0'Z, C) ; between(128, 0x1FFF, C), \+ latin_sym(C) ; C == 0'ℓ.
%  Latin-1's operators: ¬ P, A × B.
latin_sym(C) :- memberchk(C, `¬×÷±`).
id_start(C) :- letter(C) ; C == 0'_.
id_char(C) :- id_start(C) ; digit(C) ; C == 0'' ; between(0'₀, 0'₉, C).
sym_char(C) :- memberchk(C, `!#$%&*+-/:<=>?@\\^|~`) ; latin_sym(C) ; C >= 0x2000, \+ letter(C).

%  A name, and its qualification: Z.leb_le, R.alloc.
ident(Cs0, I, Cs) :-
    span(id_char, Cs0, I0, Cs1),
    (   Cs1 = [0'., C|_], id_start(C)
    ->  Cs1 = [_|Cs2], ident(Cs2, I1, Cs), append(I0, [0'.|I1], I)
    ;   I = I0, Cs = Cs1
    ).

span(P, [C|Cs0], [C|W], Cs) :- call(P, C), !, span(P, Cs0, W, Cs).
span(_, Cs, [], Cs).

%% Sentences

%  chunks(+Toks, -Chunks): the tokens between full stops, c(Toks, To)
%  with To the end of the stop (or of the last token, unterminated).
chunks([], []) :- !.
chunks(Toks, [c(S, To)|Cs]) :-
    (   append(S, [t(dot, _, To)|Rest], Toks) -> chunks(Rest, Cs)
    ;   S = Toks, last(Toks, t(_, _, To)), Cs = []
    ).

%  events(+Chunks, +Mode, -Events): sent(S) for each vernacular sentence,
%  and in a proof step(P, Bullets, Toks), proof(P) and qed(P, Kw).
events([], _, []).
events([c(Toks0, To)|Cs], Mode, Es) :-
    (   Mode == proof
    ->  bullets(Toks0, Bs, Toks),
        (   Toks = [t(id(Kw), F, _)|_], proof_end(Kw)
        ->  Es = [bullet_only(Bs), qed(F-To, Kw)|Es1], Mode1 = vernac
        ;   Toks = [t(id('Proof'), F, _)|_]
        ->  Es = [proof(F-To)|Es1], Mode1 = proof
        ;   Toks == []
        ->  Es = [bullet_only(Bs)|Es1], Mode1 = proof
        ;   Toks = [t(_, F, _)|_],
            Es = [step(F-To, Bs, Toks)|Es1], Mode1 = proof
        )
    ;   Toks0 = [t(_, F, _)|_],
        sentence_(Toks0, F-To, S),
        Es = [sent(S)|Es1],
        ( opens_proof(S) -> Mode1 = proof ; Mode1 = vernac )
    ),
    events(Cs, Mode1, Es1).

proof_end(Kw) :- memberchk(Kw, ['Qed', 'Defined', 'Admitted', 'Abort', 'Save']).

%  The bullets and braces that focus a tactic, and the closing braces of
%  the one before it.
bullets(Ts0, [B|Bs], Ts) :- rocq_focus_tokens(Ts0, B, _, Ts1), !, bullets(Ts1, Bs, Ts).
bullets(Ts, [], Ts).

%! rocq_focus_tokens(+Tokens, -Focus, -End, -Rest) is semidet.
%
% One standalone focus command, including a numeric selector's opening
% brace. Capture must send only this prefix to Rocq, not the tactic after it.
rocq_focus_tokens([t(num(N), _, _), t(sym(':'), _, _), t(p('{'), _, T)|Ts], focus(N), T, Ts).
rocq_focus_tokens([t(K, _, T)|Ts], B, T, Ts) :- bullet(K, B).

bullet(p('{'), '{').
bullet(p('}'), '}').
bullet(sym(S), S) :- atom_codes(S, Cs), Cs = [C|_], memberchk(C, `-+*`), forall(member(X, Cs), X == C).

opens_proof(thm(_, _, _, _, _)).
opens_proof(def(_, _, _, _, _, none)).
opens_proof(proof_start(_)).

sentence_(Toks, P, S) :-
    nb_setval(rocq_far, 0),
    (   phrase(sentence(P, S0), Toks) -> S = S0
    ;   Toks = [t(K, _, _)|_], tok_text(K, Kw), S = raw(P, Kw)
    ),
    record_notation(S), !.

tok_text(id(A), A) :- !.
tok_text(kw(A), A) :- !.
tok_text(sym(A), A) :- !.
tok_text(p(A), A) :- !.
tok_text(num(A), A) :- !.
tok_text(str(S), S) :- !.
tok_text(dot, '.').

%  tree(Items): sentences, a module or section with its own, and a
%  theorem with its proof.
tree([I|Is]) --> item(I), !, tree(Is).
tree([]) --> [].

item(I) --> [sent(S)], { S \= endm(_, _) }, !,
    (   { S = module(_, _, _, _, Open), Open \= defined(_) }
    ->  tree(Body), ( [sent(E)], { E = endm(_, _) } -> [] ; { E = none } ),
        { I = block(S, Body, E) }
    ;   { opens_proof(S) }
    ->  proof_steps(Steps), ( [qed(Q, Kw)] -> { End = qed(Q, Kw) } ; { End = none } ),
        { I = proved(S, pf(Steps, End)) }
    ;   { I = S }
    ).
item(proved(proof_start(P), pf(Steps, End))) --> [proof(P)], !,
    proof_steps(Steps), ( [qed(Q, Kw)] -> { End = qed(Q, Kw) } ; { End = none } ).

proof_steps(Ss) --> [proof(_)], !, proof_steps(Ss).
proof_steps([step(P, Bs, Ts)|Ss]) --> [step(P, Bs, Ts)], !, proof_steps(Ss).
proof_steps([bullets(Bs)|Ss]) --> [bullet_only(Bs)], { Bs \== [] }, !, proof_steps(Ss).
proof_steps(Ss) --> [bullet_only([])], !, proof_steps(Ss).
proof_steps([]) --> [].

%% Parsing

tk(K, F, T) --> [t(K, F, T)], { far(F) }.
tk(K) --> tk(K, _, _).

far(F) :- nb_getval(rocq_far, F0), ( F > F0 -> nb_setval(rocq_far, F) ; true ).

peek(K), [t(K, F, T)] --> [t(K, F, T)].

start(N, F) :- arg(1, N, F-_).
end(N, T) :- arg(1, N, _-T).

%% Vernacular

sentence(P, S) --> attributes, modifiers, vernac(P, S).

attributes --> [t(sym('#'), _, _), t(p('['), _, _)], !, skip_to(p(']')), attributes.
attributes --> [].

skip_to(K) --> [t(K, _, _)], !.
skip_to(K) --> [_], skip_to(K).

modifiers --> [t(id(M), _, _)], { memberchk(M, ['Local', 'Global', 'Program', 'Polymorphic', 'Monomorphic', 'Private', '#[local]']) },
    \+ peek(sym(_)), !, modifiers.
modifiers --> [].

vernac(P, dir(P, Words)) --> peek(id(K)), { directive(K) }, !, words(Words).
vernac(P, ind(P, Kw, Bodies)) --> tk(id(Kw)), { memberchk(Kw, ['Inductive', 'CoInductive', 'Variant']) }, !,
    ind_bodies(Bodies).
vernac(P, rec(P, Kw, N, Bs, Sort, Ctor, Fs)) -->
    tk(id(Kw)), { memberchk(Kw, ['Record', 'Structure', 'Class']) }, !,
    name(N), binders0(Bs), opt_type(Sort), tk(sym(':=')),
    ( name(Ctor) -> [] ; { Ctor = none } ),
    tk(p('{')), fields(Fs), tk(p('}')).
vernac(P, def(P, Kw, N, Bs, Ty, Body)) -->
    def_kw(Kw), !,
    name(N), binders0(Bs), opt_type(Ty),
    ( tk(sym(':=')) -> term(Body) ; { Body = none } ).
vernac(P, thm(P, Kw, N, Bs, Ty)) -->
    tk(id(Kw)), { memberchk(Kw, ['Theorem', 'Lemma', 'Corollary', 'Fact', 'Remark', 'Proposition', 'Property']) }, !,
    name(N), binders0(Bs), tk(sym(':')), term(Ty).
vernac(P, thm(P, 'Goal', none, [], Ty)) --> tk(id('Goal')), !, term(Ty).
vernac(P, tacdef(P, N, Args, Body)) -->
    tk(id('Ltac')), !, name(N), tactic_params(Args), tk(sym(':=')), tactic(Body).
vernac(P, decl(P, Kw, Gs)) -->
    tk(id(Kw)), { memberchk(Kw, ['Axiom', 'Axioms', 'Parameter', 'Parameters', 'Conjecture', 'Hypothesis',
                                 'Hypotheses', 'Variable', 'Variables', 'Context']) }, !,
    decl_groups(Gs).
vernac(P, notation(P, Kw, S, E, Mods)) -->
    tk(id(Kw)), { memberchk(Kw, ['Notation', 'Infix']) }, !,
    ( tk(str(S)) -> [] ; tk(id(A)), names0(Ps), { maplist([n(_, X), X]>>true, Ps, Xs), atomic_list_concat([A|Xs], ' ', S0), atom_string(S0, S) } ),
    tk(sym(':=')), atom(E), mods(Mods).
vernac(P, module(P, Kind, N, Bs, Open)) -->
    tk(id('Module')), !, ( tk(id('Type')) -> { Kind = module_type } ; { Kind = module } ),
    name(N), binders0(Bs),
    (   tk(sym(':=')) -> words(W), { Open = defined(W) }
    ;   tk(sym(':')), name(n(_, Sig)), \+ peek(_) -> { Open = open(Sig) }
    ;   { Open = open }
    ).
vernac(P, module(P, section, N, [], open)) --> tk(id('Section')), !, name(N).
vernac(P, endm(P, N)) --> tk(id('End')), !, name(N).
vernac(P, proof_start(P)) --> tk(id('Proof')), !, words(_).

def_kw(Kw) --> tk(id(Kw)), { memberchk(Kw, ['Definition', 'Fixpoint', 'CoFixpoint', 'Let', 'Example', 'Instance', 'Function']) }, !.
def_kw('Canonical Structure') --> tk(id('Canonical')), tk(id('Structure')).

directive(K) :- memberchk(K, ['From', 'Require', 'Import', 'Export', 'Open', 'Close', 'Set', 'Unset',
                              'Arguments', 'Hint', 'Declare', 'Delimit', 'Bind', 'Implicit',
                              'Generalizable', 'Create', 'Opaque', 'Transparent', 'Coercion']).

words([W|Ws]) --> [t(K, _, _)], !, { tok_text(K, W) }, words(Ws).
words([]) --> [].

name(n(F-T, X)) --> tk(id(X), F, T), { X \== '_' }.

opt_type(Ty) --> tk(sym(':')), !, term(Ty).
opt_type(none) --> [].

%  The modifiers of a notation, (at level 70) and the like, as words.
mods([W|Ws]) --> [t(K, _, _)], !, { tok_text(K, W) }, mods(Ws).
mods([]) --> [].

%  Inductive: ib(Name, Params, Type, Constructors), with ... for each
%  further type; a constructor is ctor(P, Name, Binders, Type).
ind_bodies([B|Bs]) --> ind_body(B), ( tk(kw(with)) -> ind_bodies(Bs) ; { Bs = [] } ).

ind_body(ib(N, Bs, Ty, Cs)) -->
    name(N), binders0(Bs), opt_type(Ty), tk(sym(':=')),
    ( tk(sym('|')) -> [] ; [] ),
    ( ctors(Cs) -> [] ; { Cs = [] } ).

ctors([C|Cs]) --> ctor(C), ( tk(sym('|')) -> ctors(Cs) ; { Cs = [] } ).

ctor(ctor(F-T, X, Bs, Ty)) -->
    tk(id(X), F, T0), binders0(Bs), opt_type(Ty),
    { Ty == none -> ( Bs == [] -> T = T0 ; last(Bs, B), end(B, T) ) ; end(Ty, T) }.

%  Record fields: fld(P, Name, Binders, Type, Default).
fields([F|Fs]) --> field(F), !, ( tk(p(;)) -> fields(Fs) ; { Fs = [] } ).
fields([]) --> [].

field(field(F-T, X, Bs, Ty, D)) -->
    tk(id(X), F, T0), binders0(Bs),
    ( tk(sym(':')) -> term(Ty) ; tk(sym(':>')) -> term(Ty) ; { Ty = none } ),
    ( tk(sym(':=')) -> term(D) ; { D = none } ),
    { D \== none -> end(D, T) ; Ty \== none -> end(Ty, T) ; T = T0 }.

%  Axiom a : T, Parameter a b : T, Variable (x : T) (y : U); binders of
%  other kinds, Context {Σ : gFunctors} `{!invGS Σ}, as they are: bs(Bs).
decl_groups([g(Ns, Ty)]) --> names(Ns), tk(sym(':')), !, term(Ty).
decl_groups(Gs) --> binders(Bs),
    { maplist([b(_, paren, Ns, Ty), g(Ns, Ty)]>>true, Bs, Gs0) -> Gs = Gs0 ; Gs = [bs(Bs)] }.

%% Terms

term(E) --> expr(200, E).

expr(Max, E) --> operand(Max, L0), as_pat(L0, L), op_rest(Max, L, E).

operand(_, E) --> binder_form(E), !.
operand(_, E) --> iris_operand(E), !.
%  ▷^n P: n laters.
operand(_, laterN(F-T, N, A)) --> [t(sym('▷'), F, _), t(sym('^'), _, _)], !, atom(N), expr(20, A), { end(A, T) }.
operand(_, pre(F-T, Op, A)) --> tk(sym(Op), F, _), { prefix_op(Op, Lv) }, !,
    ( { Lv < 10 } -> tight(A) ; expr(Lv, A) ), { end(A, T) }.
operand(_, E) --> app(E).

%  A prefix below application's level takes an atom: ! #ℓ, not ! (# ℓ x).
tight(pre(F-T, Op, A)) --> tk(sym(Op), F, _), { prefix_op(Op, Lv), Lv < 10 }, !, tight(A), { end(A, T) }.
tight(A) --> atom(A).

prefix_op('~', 75).
prefix_op('¬', 75).
prefix_op('-', 35).
%  Iris: the later, persistence, plus and basic modalities, the
%  authoritative and fragment of a camera, a namespace's mask, and
%  heap_lang's load. ⊢ P and |==> P take all that follows.
prefix_op(Op, 20) :- memberchk(Op, ['▷', '□', '◇', '■', '↑', '●', '◯']).
prefix_op('!', 9).
prefix_op('£', 1).
prefix_op('✓', 20).
prefix_op('⊢', 200).
prefix_op('|==>', 200).

%% Iris

%  Iris's notations (iris/bi/notation.v, program_logic/weakestpre.v):
%  |={E1,E2}=> P, <pers> P, WP e @ s; E {{ v, Q }}, the Texan triple
%  {{{ P }}} e {{{ x, RET v; Q }}}, and big separating conjunctions.
%  |={E}▷=>^n P: n steps, each an update, a later and an update.
iris_operand(U) --> tk(sym('|='), F, _), tk(p('{')), !, masks(Ms), tk(p('}')),
    (   tk(sym('▷')) -> step_arrow('=>', N), expr(200, A), { U = stepupd(F-T, Ms, N, A) }
    ;   tk(sym('=>')), expr(200, A), { U = fupd(F-T, Ms, A) }
    ),
    { end(A, T) }.
iris_operand(pre(F-T, Op, A)) --> tk(sym('<'), F, _), tk(id(K)), { iris_modality(K) }, tk(sym('>')), !,
    { atomic_list_concat(['<', K, '>'], Op) }, expr(20, A), { end(A, T) }.
%  ✓{n} x: valid at step-index n.
iris_operand(indexed(F-T, '✓', N, none, A)) --> [t(sym('✓'), F, _), t(p('{'), _, _)], !,
    term(N), tk(p('}')), expr(20, A), { end(A, T) }.
iris_operand(wp(F-T, E, At, Post)) --> tk(id('WP'), F, _), !, wp_expr(E), wp_at(At), wp_post(Post, T).
iris_operand(triple(F-T, Pre, E, At, Bs, Ret, Post)) -->
    tk(p('{'), F, _), tk(p('{')), tk(p('{')), !, term(Pre), tk(p('}')), tk(p('}')), tk(p('}')),
    wp_expr(E), wp_at(At), tk(p('{')), tk(p('{')), tk(p('{')),
    ( peek(id('RET')) -> { Bs = [] } ; binders(Bs), tk(p(',')) ),
    tk(id('RET')), term(Ret), tk(p(';')), term(Post), tk(p('}')), tk(p('}')), tk(p('}'), _, T).

iris_modality(K) :- memberchk(K, [pers, affine, absorb, subj, obj]).

masks([M|Ms]) --> term(M), ( tk(p(',')) -> term(M2), { Ms = [M2] } ; { Ms = [] } ).

%  The expression of a weakest precondition: its @ is the mask's, not an
%  explicit argument's.
wp_expr(E) --> { ( nb_current(rocq_no_at, O) -> true ; O = false ), b_setval(rocq_no_at, true) },
    term(E0), { b_setval(rocq_no_at, O) },
    %  Rocq prints a cast there bare: WP e : T {{ … }}.
    ( tk(sym(':')) -> term(Ty), { start(E0, F), end(Ty, T), E = cast(F-T, E0, Ty) } ; { E = E0 } ).

wp_at(at(S, M)) --> tk(sym('@')), !, term(X), ( tk(p(';')) -> term(M), { S = X } ; { S = none, M = X } ).
wp_at(none) --> [].

wp_post(post(N, Q), T) --> tk(p('{')), tk(p('{')),
    ( name_or_hole(N), tk(p(',')) -> [] ; { N = none } ), term(Q), tk(p('}')), tk(p('}'), _, T).

%  [∗ list] k ↦ x ∈ l, P and the like: the big operators of Iris's
%  bi/big_op.v; [∗] Ps.
binder_form(bigop(F-T, Op, Kind, Binds, Cs, B)) -->
    tk(p('['), F, _), tk(sym(Op)), { big_op(Op) }, tk(id(Kind)), tk(p(']')), !,
    big_binds(Binds), tk(sym('∈')), big_colls(Cs), tk(p(',')), term(B), { end(B, T) }.
binder_form(bigall(F-T, Op, E)) --> tk(p('['), F, _), tk(sym(Op)), { big_op(Op) }, tk(p(']')), !,
    expr(20, E), { end(E, T) }.
%  Eval red in t, as a definition's body.
binder_form(eval(F-T, Ws, E)) --> tk(id('Eval'), F, _), !, eval_words(Ws), tk(kw(in)), term(E), { end(E, T) }.
binder_form(forall(F-T, Bs, B)) --> forall_kw(F), !, binders_typed(Bs), tk(p(',')), term(B), { end(B, T) }.
binder_form(exists(F-T, Bs, B)) --> exists_kw(F), !, binders_typed(Bs), tk(p(',')), term(B), { end(B, T) }.
%  stdpp's λ x, e is fun x => e.
binder_form(fun(F-T, Bs, B)) --> fun_kw(F), !, binders_typed(Bs), ( arrow_kw -> [] ; tk(p(',')) ), term(B), { end(B, T) }.
%  let* x := e in b, the option monad's bind as a development defines it;
%  let fix, and let '(a, b) := e in b, which destructures.
binder_form(letstar(F-T, N, V, B)) --> tk(kw(let), F, _), tk(sym('*')), !,
    name_or_hole(N), tk(sym(':=')), term(V), tk(kw(in)), term(B), { end(B, T) }.
binder_form(letfix(F-T, N, Bs, Ty, V, B)) --> tk(kw(let), F, _), tk(kw(fix)), !,
    name(N), binders0(Bs), opt_type(Ty), tk(sym(':=')), term(V), tk(kw(in)), term(B), { end(B, T) }.
binder_form(letpat(F-T, Pat, V, B)) --> tk(kw(let), F, _), tk(p('''')), !,
    atom(Pat), tk(sym(':=')), term(V), tk(kw(in)), term(B), { end(B, T) }.
binder_form(let(F-T, Lhs, Ty, V, B)) --> tk(kw(let), F, _), !,
    let_lhs(Lhs), opt_type(Ty), tk(sym(':=')), term(V), tk(kw(in)), term(B), { end(B, T) }.
binder_form(If) --> tk(kw(if), F, _), !,
    { ( nb_current(rocq_if, O) -> true ; O = false ), b_setval(rocq_if, true) },
    term(C), { b_setval(rocq_if, O) },
    (   tk(id(is)) -> term(Pat), { If = ifis(F-T, C, Pat, Th, El) }
    ;   { If = if(F-T, C, Th, El) }
    ),
    tk(kw(then)), term(Th), tk(kw(else)), term(El), { end(El, T) }.
%  An anonymous fixpoint, as Rocq prints an unfolded Fixpoint.
binder_form(fix(F-T, N, Bs, Ty, B)) --> tk(kw(fix), F, _), !,
    name(N), binders0(Bs), opt_type(Ty), tk(sym(':=')), term(B), { end(B, T) }.

big_op(Op) :- memberchk(Op, ['∗', '∧', '∨', '+']).

%  k ↦ x, or x, or the pairs of big_sepL2: x1;x2.
big_binds(binds(K, Xs)) --> name_or_hole(N), ( tk(sym('↦')) -> { K = N }, big_names(Xs) ; { K = none }, big_rest(N, Xs) ).
big_names([N|Ns]) --> name_or_hole(N), ( tk(p(';')) -> big_names(Ns) ; { Ns = [] } ).
big_rest(N, [N|Ns]) --> ( tk(p(';')) -> big_names(Ns) ; { Ns = [] } ).
big_colls([C|Cs]) --> term(C), ( tk(p(';')) -> big_colls(Cs) ; { Cs = [] } ).

eval_words([]) --> peek(kw(in)), !.
eval_words([W|Ws]) --> [t(K, _, _)], { tok_text(K, W) }, eval_words(Ws).

forall_kw(F) --> tk(kw(forall), F, _), !.
forall_kw(F) --> tk(sym('∀'), F, _).
exists_kw(F) --> tk(kw(exists), F, _), !.
exists_kw(F) --> tk(sym('∃'), F, _).
fun_kw(F) --> tk(kw(fun), F, _), !.
fun_kw(F) --> tk(id('λ'), F, _).
arrow_kw --> tk(sym('=>')), !.
arrow_kw --> tk(sym('⇒')).

let_lhs(tuple(Ns)) --> tk(p('(')), !, names(Ns), tk(p(')')).
let_lhs(name(N, Bs)) --> name_or_hole(N), binders0(Bs).

%  names separated by spaces or (in a let pattern) commas.
names([N|Ns]) --> name_or_hole(N), ( tk(p(',')) -> names(Ns) ; names(Ns) -> [] ; { Ns = [] } ).
names0(Ns) --> names(Ns), !.
names0([]) --> [].

name_or_hole(n(F-T, X)) --> tk(id(X), F, T), { \+ op_word(X) }.

%  Binders before a , or => may share a type unbracketed: forall x y : T, B.
binders_typed(Bs) -->
    binders(Bs0),
    (   { forall(member(b(_, K, _, _), Bs0), K == bare) }, tk(sym(':'))
    ->  term(Ty), { maplist([b(_, _, [N], _), N]>>true, Bs0, Ns), Bs0 = [b(F-_, _, _, _)|_], end(Ty, T),
                    Bs = [b(F-T, bare, Ns, Ty)] }
    ;   { Bs = Bs0 }
    ).

binders([B|Bs]) --> binder(B), !, binders0(Bs).
binders0(Bs) --> binders(Bs), !.
binders0([]) --> [].

binder(b(F-T, paren, Ns, Ty)) --> tk(p('('), F, _), names(Ns), tk(sym(':')), term(Ty), tk(p(')'), _, T).
binder(b(F-T, struct, [N], none)) --> tk(p('{'), F, _), tk(id(struct)), name(N), tk(p('}'), _, T).
binder(b(F-T, brace, Ns, Ty)) --> tk(p('{'), F, _), names(Ns), ( tk(sym(':')) -> term(Ty) ; { Ty = none } ), tk(p('}'), _, T).
binder(b(P, bare, [n(P, X)], none)) --> tk(id(X), F, T), { \+ op_word(X), P = F-T }.
binder(b(F-T, pattern(Pat), [], none)) --> tk(p(''''), F, _), atom(Pat), { end(Pat, T) }.
%  `{!invGS Σ}, a generalizing binder: its classes, ! for no implicit
%  generalization of their own arguments.
binder(b(F-T, gen(Open, Items), [], none)) -->
    tk(p('`'), F, _), [t(p(Open), _, _)], { memberchk(Open, ['{', '(']), matching(Open, Close) },
    gen_items(Items), tk(p(Close), _, T).

gen_items([I|Is]) --> ( tk(sym('!')) -> term(E), { I = bang(E) } ; term(I) ),
    ( tk(p(',')) -> gen_items(Is) ; { Is = [] } ).

%  Operators by precedence: binop(Op, Level, Assoc), Rocq's levels (a
%  lower level binds tighter). The file's own infix notations are added
%  as they are read (notation_op/3).
:- dynamic notation_op/3, notation_fold/3.

binop(Op, Lv, As) :- notation_op(Op, Lv, As), !.
binop(Op, Lv, As) :- std_op(Op, Lv, As).

std_op('<->', 95, none). std_op('↔', 95, none).
%  Iris: entailment, the wands and the separating conjunction.
std_op('⊢', 99, right). std_op('-∗', 99, right). std_op('==∗', 99, right).
std_op('⊣⊢', 95, none). std_op('∗-∗', 95, none).
std_op('∗', 80, right).
std_op('<$>', 61, left).
std_op('$', 65, right).
std_op('∘', 40, left).
std_op('-d>', 99, right). std_op('-n>', 45, right).
std_op('⋅', 50, left).
std_op('∪', 50, left). std_op('∖', 40, left). std_op('∩', 40, left).
std_op('!!', 20, none).
std_op('->', 99, right). std_op('→', 99, right).
std_op('\\/', 85, right). std_op('∨', 85, right).
std_op('/\\', 80, right). std_op('∧', 80, right).
std_op(Op, 70, none) :- memberchk(Op, [=, '<>', '≠', <, '<=', >, >=, '≤', '≥', '=?', '<=?', '<?', '>=?', '>?', '==', '=?=', '≡', '∈', '∉', '⊆', '⊂', '⊈', '##', '≼', '~~>']).
std_op('::', 60, right). std_op('++', 60, right).
std_op(+, 50, left). std_op(-, 50, left). std_op('||', 50, left).
std_op(*, 40, left). std_op(/, 40, left). std_op(mod, 40, left). std_op('&&', 40, left). std_op('×', 40, left).
std_op(^, 30, right).

op_word(mod).

op_rest(Max, L, E) --> iris_op(Max, L, N), !, op_rest(Max, N, E).
op_rest(Max, L, E) -->
    (   peek(K), { op_token(K, Op), binop(Op, Lv, As), Lv =< Max }
    ->  [_],
        { As == right -> RMax = Lv ; RMax is Lv - 1 },
        expr(RMax, R), { start(L, F), end(R, T), combine(F-T, Op, L, R, N) },
        op_rest(Max, N, E)
    ;   { E = L }
    ).

%  P ={E}=∗ Q; l ↦ v with its fraction (l ↦{#q} v, l ↦□ v), and the
%  ghost map's k ↪[γ] v; x ≡{n}≡ y and x ≼{n} y, at step-index n.
iris_op(Max, L, U) --> { Max >= 99 }, [t(sym('='), _, _), t(p('{'), _, _)], !,
    masks(Ms), tk(p('}')),
    (   tk(sym('▷')) -> step_arrow('=∗', N), expr(200, R), { U = stepupdw(F-T, Ms, N, L, R) }
    ;   tk(sym('=∗')), expr(200, R), { U = fupdw(F-T, Ms, L, R) }
    ),
    { start(L, F), end(R, T) }.

%  The arrow after ▷, and its count: =>^n, lexed as one symbol.
step_arrow(Arrow, N) --> [t(sym(S), _, _)],
    (   { S == Arrow } -> { N = none }
    ;   { atom_concat(Arrow, '^', S) }, atom(N)
    ).
iris_op(Max, L, pointsto(F-T, Op, L, Ms, R)) --> { Max >= 20 }, tk(sym(Op)), { memberchk(Op, ['↦', '↪']) }, !,
    ( tk(p('[')) -> term(G), tk(p(']')), { Ms = [name(G)|Ms1] } ; { Ms = Ms1 } ), dfrac(Ms1),
    expr(19, R), { start(L, F), end(R, T) }.
iris_op(Max, L, indexed(F-T, Op, N, L, R)) --> { Max >= 70 }, [t(sym(Op), _, _), t(p('{'), _, _)],
    { memberchk(Op, ['≡', '≼']) }, !, term(N), tk(p('}')), ( { Op == '≡' } -> tk(sym('≡')) ; [] ),
    expr(69, R), { start(L, F), end(R, T) }.

%  {#q}, the fraction q of ownership; {dq}, any fraction; □, discarded.
dfrac([own(Q)]) --> tk(p('{')), tk(sym('#')), !, term(Q), tk(p('}')).
dfrac([dfrac(D)]) --> tk(p('{')), !, term(D), tk(p('}')).
dfrac([persistent]) --> tk(sym('□')), !.
dfrac([]) --> [].

%  a <= b < c is Rocq's chained comparison, one notation of three
%  operands, not (a <= b) < c.
combine(P, Op, bin(_, Op1, A, B), C, chain(P, [Op1, Op], [A, B, C])) :-
    chain_op(Op1), chain_op(Op), !.
combine(P, Op, L, R, bin(P, Op, L, R)).

chain_op(Op) :- memberchk(Op, [<, '<=', '≤']).

op_token(sym(Op), Op).
op_token(id(W), W) :- op_word(W).

app(E) --> atom(F), args(As), { As == [] -> E = F ; start(F, S), last(As, A), end(A, T), E = app(S-T, F, As) }.

args([A|As]) --> starts_atom, !, atom(A), args(As).
args([]) --> [].

%  In an if's condition, is begins ssreflect's pattern: if c is p then.
starts_atom --> peek(K), { atom_start(K), \+ ( K == sym('@'), nb_current(rocq_no_at, true) ),
                           \+ ( K == id(is), nb_current(rocq_if, true) ) }.

atom_start(id(X)) :- \+ op_word(X).
atom_start(num(_)). atom_start(str(_)).
atom_start(p('(')). atom_start(p('[')). atom_start(p('{|')).
atom_start(kw(match)). atom_start(sym('@')).
atom_start(sym('?')).
atom_start(sym(C)) :- memberchk(C, ['⌜', '⊤', '∅', '#']).

atom(E) --> atom0(E00), bits(E00, E01), projs(E01, E0),
    ( tk(sym('%')), tk(id(K), _, T) -> { start(E0, F), E = scope(F-T, E0, K) } ; { E = E0 } ).

%  stdpp's projections: lv.1, ps.*1 (fst <$> ps).
projs(E, E2) --> tk(sym(Op), _, T), { memberchk(Op, ['.1', '.2', '.*1', '.*2']) }, !,
    { start(E, F) }, projs(proj(F-T, E, Op), E2).
projs(E, E) --> [].

%  p~0~1, a positive's binary digits as Rocq prints them.
bits(E0, bits(F-T, E0, Ds)) --> bit(D, T0), !, bit_rest(D, T0, Cs, T), { start(E0, F), atom_codes(Ds, Cs) }.
bits(E, E) --> [].
bit_rest(D, _, [D|Ds], T) --> bit(D1, T1), !, bit_rest(D1, T1, Ds, T).
bit_rest(D, T, [D], T) --> [].
bit(D, T) --> tk(sym('~')), tk(num(N), _, T), { memberchk(N, ['0', '1']), atom_codes(N, [D]) }.

%  Pat as n, in a pattern, where it binds tighter than any operator:
%  Rocq prints Const c as a :: rest. Elsewhere as belongs to a match's
%  scrutinee or a tactic (destruct H as ...).
as_pat(E, aspat(F-T, E, N)) --> { nb_current(rocq_mode, pattern) }, tk(kw(as)), !, name(N), { start(E, F), N = n(_-T, _) }.
as_pat(E, E) --> [].

atom0(hole(F-T)) --> tk(id('_'), F, T), !.
atom0(pure(F-T, E)) --> tk(sym('⌜'), F, _), !, term(E), tk(sym('⌝'), _, T).
atom0(const(F-T, C)) --> tk(sym(C), F, T), { memberchk(C, ['⊤', '∅']) }, !.
atom0(unit(F-T)) --> tk(p('('), F, _), tk(p(')'), _, T), !.
%  <[k := v]> m, stdpp's insertion, is applied to the map.
atom0(insert(F-T, K, V)) --> tk(sym('<'), F, _), tk(p('[')), !,
    term(K), tk(sym(':=')), term(V), tk(p(']')), tk(sym('>'), _, T).
%  #[invΣ; gen_heapΣ l v], a list of functors; #ℓ, a heap_lang literal.
atom0(gfunctors(F-T, Es)) --> [t(sym('#'), F, F1), t(p('['), F1, _)], !, list_elems(Es), tk(p(']'), _, T).
atom0(pre(F-T, '#', E)) --> tk(sym('#'), F, _), !, atom(E), { end(E, T) }.
atom0(meta(F-T, X)) --> tk(sym('?'), F, _), tk(id(X), _, T), !.
atom0(ltac(F-T, Tac)) --> tk(id(ltac), F, _), tk(sym(':')), tk(p('(')), !,
    tactic(Tac), tk(p(')'), _, T).
atom0(id(F-T, X)) --> tk(id(X), F, T), { \+ op_word(X) }, !.
atom0(num(F-T, N)) --> tk(num(N), F, T), !.
atom0(str(F-T, S)) --> tk(str(S), F, T), !.
atom0(explicit(F-T, X)) --> tk(sym('@'), F, _), !, tk(id(X), _, T).
atom0(named(F-T, X, E)) --> tk(p('('), F, _), tk(id(X)), tk(sym(':=')), !, term(E), tk(p(')'), _, T).
atom0(E) --> tk(p('('), F, _), !, term(E0),
    (   tk(p(')'), _, T) -> { E = paren(F-T, E0) }
    ;   tk(sym(':')) -> term(Ty), tk(p(')'), _, T), { E = cast(F-T, E0, Ty) }
    ;   tk(p(',')), tuple_rest(Es), tk(p(')'), _, T), { E = tuple(F-T, [E0|Es]) }
    ;   tk(sym('|')), or_rest(Es), tk(p(')'), _, T), { E = orpat(F-T, [E0|Es]) }
    ).
atom0(list(F-T, Es)) --> tk(p('['), F, _), !, ( tk(p(']'), _, T) -> { Es = [] } ; list_elems(Es), tk(p(']'), _, T) ).
atom0(record(F-T, Fs)) --> tk(p('{|'), F, _), !, rec_fields(Fs), tk(p('|}'), _, T).
atom0(E) --> tk(p('{'), F, _), !,
    (   name(N), tk(sym(':')), term(Ty), tk(sym('|')) -> term(Q), tk(p('}'), _, T), { E = sig(F-T, N, Ty, Q) }
    ;   term(E0), tk(p('}'), _, T), { E = braces(F-T, E0) }
    ).
atom0(match(F-T, Ss, Ret, Brs)) --> tk(kw(match), F, _), !,
    scrutinees(Ss), ( tk(kw(return)) -> expr(100, Ret) ; { Ret = none } ),
    tk(kw(with)), ( tk(sym('|')) -> [] ; [] ),
    branches(Brs), tk(kw(end), _, T).

%  (W | L), an or-pattern.
or_rest([E|Es]) --> term(E), ( tk(sym('|')) -> or_rest(Es) ; { Es = [] } ).

tuple_rest([E|Es]) --> term(E), ( tk(p(',')) -> tuple_rest(Es) ; { Es = [] } ).
list_elems([E|Es]) --> term(E), ( tk(p(;)) -> list_elems(Es) ; { Es = [] } ).

rec_fields([Fld|Fs]) --> tk(id(X), F, _), !, binders0(Bs), tk(sym(':=')), term(E), { end(E, T) },
    { Bs == [] -> Fld = fld(F-T, X, E) ; Fld = fldb(F-T, X, Bs, E) },
    ( tk(p(;)) -> rec_fields(Fs) ; { Fs = [] } ).
rec_fields([]) --> [].

scrutinees([S|Ss]) --> expr(100, S0),
    ( tk(kw(as)) -> name(N), { S = as(S0, N) } ; { S = S0 } ),
    ( tk(p(',')) -> scrutinees(Ss) ; { Ss = [] } ).

branches([br(Alts, R)|Bs]) -->
    { ( nb_current(rocq_mode, M) -> true ; M = term ), b_setval(rocq_mode, pattern) },
    alternatives(Alts), { b_setval(rocq_mode, M) },
    arrow_kw, !, term(R),
    ( tk(sym('|')) -> branches(Bs) ; { Bs = [] } ).
branches([]) --> [].

alternatives([Ps|As]) --> patterns(Ps), ( tk(sym('|')) -> alternatives(As) ; { As = [] } ).
patterns([P|Ps]) --> expr(99, P), ( tk(p(',')) -> patterns(Ps) ; { Ps = [] } ).

%% Ltac

% rocq_tactic_tokens(+Tokens, -Tactic): control structure of a tactic
% sentence (without its full stop). Atomic arguments are Gallina where
% unambiguous, otherwise balanced token groups. No source tokens vanish.
rocq_tactic_tokens(Ts, T) :- phrase(tactic(T), Ts), !.

tactic_params([N|Ns]) --> name(N), !, tactic_params(Ns).
tactic_params([]) --> [].

% Choice binds more tightly than sequencing; prefixes bind more tightly
% than either. Parentheses and dispatch brackets retain that scope.
tactic(T) --> tactic_choice(L), tactic_then(L, T).
tactic_choice(T) --> tactic_unit(L),
    ( tk(sym('||')) -> tactic_choice(R), { T = tbin('||', L, R) } ; { T = L } ).
tactic_then(L, T) --> tk(p(';')), !,
    ( tk(p('[')) -> tactic_choices(Ts), tk(p(']')), { Next = dispatch(L, Ts) }
    ; tactic_choice(R), { Next = tbin(';', L, R) } ),
    tactic_then(Next, T).
tactic_then(T, T) --> [].

%  let x := v in t: the body is the rest of the sequence.
tactic_unit(tlet(N, V, B)) --> tk(kw(let)), !, name_or_hole(N), tk(sym(':=')),
    upto_in(Ts), { phrase(tactic(V), Ts) }, tk(kw(in)), tactic(B).
tactic_unit(select(S, T)) --> [t(K, _, _)], { K = num(S) ; K = id(S), S == all }, tk(sym(':')), !, tactic(T).
tactic_unit(do(N, T)) --> tk(id(do)), !,
    [t(K, _, _)], { K = num(N) ; K = id(N) }, tactic_unit(T).
tactic_unit(prefix(K, T)) --> tk(id(K)), { memberchk(K, [try, repeat, progress, now, once, timeout, by]) },
    !, tactic_unit(T).
tactic_unit(choices(K, Ts)) --> tk(id(K)), { memberchk(K, [first, solve]) }, tk(p('[')), !,
    tactic_choices(Ts), tk(p(']')).
tactic_unit(tmatch(K, Subject, Bs)) -->
    [t(Tok, _, _)], { Tok = kw(match), K = match ; Tok = id(K), memberchk(K, [lazymatch, multimatch]) },
    !, tactic_subject(Subject), tk(kw(with)),
    ( tk(sym('|')) -> [] ; [] ), tactic_branches(Bs), tk(kw(end)).
tactic_unit(tgroup(T)) --> tk(p('(')), !, tactic(T), tk(p(')')).
%  The proof mode's introduction: Rocq patterns in parentheses, its own
%  in strings: iIntros (x [a b]) "H [H1 H2]".
tactic_unit(call(iIntros, [ipm_intros(Is)])) --> tk(id(iIntros)), ipm_intro_items(Is), { Is \== [] }, !.
%  exists a, b and iExists a, b: the witnesses.
tactic_unit(call(N, [terms([E|Es])])) --> tactic_name(N), { memberchk(N, [exists, eexists, iExists]) },
    term(E), witnesses(Es), \+ starts_atom, !.
tactic_unit(call(N, [intro(Ps)|Rest])) --> tactic_name(N), { memberchk(N, [intro, intros]) },
    intro_patterns(Ps), { Ps \== [] }, tactic_parts(Rest), !.
tactic_unit(call(N, Ps)) --> tactic_name(N), !, tactic_parts(Ps).

upto_in([]) --> peek(kw(in)), !.
upto_in([T|Ts]) --> [T], upto_in(Ts).

witnesses([E|Es]) --> tk(p(',')), !, term(E), witnesses(Es).
witnesses([]) --> [].

ipm_intro_items([coq(Ps)|Is]) --> tk(p('(')), intro_patterns(Ps), tk(p(')')), !, ipm_intro_items(Is).
ipm_intro_items([str(S)|Is]) --> tk(str(S)), !, ipm_intro_items(Is).
ipm_intro_items([]) --> [].

tactic_name(N) --> tk(id(N)).
tactic_name(exists) --> tk(kw(exists)).
tactic_name(fix) --> tk(kw(fix)).
tactic_name(cofix) --> tk(kw(cofix)).

tactic_subject(goal) --> tk(id(goal)), !.
tactic_subject(type(E)) --> tk(id(type)), tk(id(of)), !, term(E).
tactic_subject(term(E)) --> term(E).

tactic_choices([T|Ts]) -->
    ( tactic(T) -> [] ; { T = empty } ),
    ( tk(sym('|')) -> tactic_choices(Ts) ; { Ts = [] } ).
tactic_branches([tbr(Ps, T)|Bs]) --> tactic_match_pattern(Ps), tk(sym('=>')), tactic(T),
    ( tk(sym('|')) -> tactic_branches(Bs) ; { Bs = [] } ).

tactic_match_pattern([group('[', Ps, ']')]) --> tk(p('[')), tactic_match_pattern(Ps), tk(p(']')), !.
tactic_match_pattern([context(E)]) --> tk(id(context)), tk(p('[')), term(E), tk(p(']')), !.
tactic_match_pattern([hyp(N, E)|Ps]) --> name(N), tk(sym(':')), tactic_match_type(E), !,
    ( tk(p(',')) -> tactic_match_pattern(Rest), { Ps = [token(p(','))|Rest] }
    ; tk(sym('|-')), tactic_goal_pattern(G), { Ps = [token(sym('|-')), G] } ).
tactic_match_pattern([token(sym('|-')), G]) --> tk(sym('|-')), !, tactic_goal_pattern(G).
tactic_match_pattern([term(E)]) --> term(E).

tactic_goal_pattern(context(E)) --> tk(id(context)), tk(p('[')), term(E), tk(p(']')), !.
tactic_goal_pattern(term(E)) --> term(E).

tactic_match_type(context(E)) --> tk(id(context)), tk(p('[')), term(E), tk(p(']')), !.
tactic_match_type(E) --> term(E).

tactic_parts([P|Ps]) --> tactic_part(P), !, tactic_parts(Ps).
tactic_parts([]) --> [].

% Parenthesized expressions and named assertions go through the very
% same term grammar as definitions and goals. Intro/destruct patterns do
% not: [a | b] is not a Gallina list, nor (a & b) a Gallina application.
%  The proof mode's as: Rocq patterns for the witnesses, then its own
%  pattern in a string, or % and a Rocq pattern for a pure fact.
tactic_part(clause(as, [ipm_as(Ps, Pat)])) --> tk(kw(as)),
    ( tk(p('(')), intro_patterns(Ps), tk(p(')')) -> [] ; { Ps = [] } ), ipm_pat(Pat), !.
tactic_part(clause(as, [intro(Ps)])) --> tk(kw(as)), intro_patterns(Ps), { Ps \== [] }, !.
tactic_part(clause(by, [tactic(T)])) --> tk(id(by)), tactic_unit(T), !.
tactic_part(clause(K, Ps)) --> tactic_clause(K), tactic_arguments(Ps), { Ps \== [] }, !.
tactic_part(P) --> tactic_argument(P).

tactic_clause(in) --> tk(kw(in)).
tactic_clause(with) --> tk(kw(with)).
tactic_clause(using) --> tk(id(using)).
tactic_clause(eqn) --> tk(id(eqn)), tk(sym(':')).

tactic_arguments([P|Ps]) -->
    \+ tactic_clause(_), \+ tk(kw(as)), \+ tk(id(by)),
    tactic_argument(P), !, tactic_arguments(Ps).
tactic_arguments([]) --> [].

%  A proof mode term: (H $! x y with "[$H1] H2"), H a lemma or "H".
tactic_argument(ipm(H, Args, Spat)) --> tk(p('(')), ipm_head(H),
    ( tk(sym('$!')) -> ipm_args(Args) ; { Args = [] } ),
    ( tk(kw(with)) -> tk(str(Spat)) ; { Spat = none } ), tk(p(')')),
    { H = hyp(_) ; Args \== [] ; Spat \== none }, !.
tactic_argument(binding(N, Op, E)) --> tk(p('(')), name(N), tk(sym(Op)), { memberchk(Op, [':=', ':']) },
    term(E), tk(p(')')), !.
tactic_argument(term(E)) --> peek(p('(')), atom(E), !.
%  ?H and 0%nat are terms, as written: no space may come between.
tactic_argument(term(meta(F-T, X))) --> [t(sym('?'), F, T0), t(id(X), T0, T)], !.
tactic_argument(term(E)) --> scoped_ahead, atom(E), !.
tactic_argument(context(E)) --> tk(id(context)), tk(p('[')), term(E), tk(p(']')), !.
tactic_argument(group(Open, Ps, Close)) -->
    [t(p(Open), _, _)], { matching(Open, Close) }, tactic_pattern(Ps), tk(p(Close)), !.
tactic_argument(tactic(T)) --> tk(p('(')), tactic(T), tk(p(')')), !.
tactic_argument(token(K)) --> [t(K, _, _)], { tactic_token(K) }.

scoped_ahead, [t(K, F, T0), t(sym('%'), T0, T1)] --> [t(K, F, T0), t(sym('%'), T0, T1)], { memberchk(K, [num(_), id(_)]) }.

ipm_head(hyp(S)) --> tk(str(S)), !.
ipm_head(E) --> term(E).
ipm_args([A|As]) --> starts_atom, !, atom(A), ipm_args(As).
ipm_args([]) --> [].

ipm_pat(str(S)) --> tk(str(S)).
ipm_pat(pure(P)) --> tk(sym('%')), intro_pattern(P).
ipm_pat(pure(ip_rewrite(Op))) --> tk(sym(S)), { memberchk(S-Op, ['%->'-'->', '%<-'-'<-']) }.

% Intro patterns bind names, branch, pair, discard or rewrite. In
% particular [a b | (c & ->)] is a sum of sequences, not a token list.
intro_patterns([P|Ps]) --> intro_pattern(P), !, intro_patterns(Ps).
intro_patterns([]) --> [].
intro_pattern(ip_inj(Ps)) --> tk(p('[')), tk(sym('=')), intro_patterns(Ps), tk(p(']')), !.
intro_pattern(ip_or(Arms)) --> tk(p('[')), intro_arms(Arms), tk(p(']')), !.
intro_pattern(ip_and([P|Ps])) --> tk(p('(')), intro_pattern(P), intro_pairs(Ps), tk(p(')')), !.
%  ?x, a fresh name based on x, is one token for Rocq.
intro_pattern(ip_fresh(N)) --> [t(sym('?'), _, T), t(id(X), T, T1)], !, { N = n(T-T1, X) }.
intro_pattern(ip_name(N)) --> name_or_hole(N), { N = n(_, X), \+ memberchk(X, [eqn, using, by, until]) }, !.
intro_pattern(ip_rewrite(Op)) --> tk(sym(Op)), { memberchk(Op, ['->', '<-']) }, !.
intro_pattern(ip_auto(K)) --> tk(sym(K)), { memberchk(K, ['?', '*', '**']) }.

intro_arms([Ps|Arms]) --> intro_patterns(Ps),
    ( tk(sym('|')) -> intro_arms(Arms) ; { Arms = [] } ).
intro_pairs([P|Ps]) --> tk(sym('&')), intro_pattern(P), !, intro_pairs(Ps).
intro_pairs([]) --> [].

tactic_token(K) :- \+ memberchk(K, [p(';'), p('('), p(')'), p('['), p(']'),
                                    sym('|'), sym('=>'), sym('||'), kw(end)]).
matching('(', ')').
matching('[', ']').
matching('{', '}').

tactic_pattern([P|Ps]) -->
    ( tactic_part(P) -> [] ; tk(sym('|')), { P = token(sym('|')) } ), !, tactic_pattern(Ps).
tactic_pattern([]) --> [].

%% Notations

%  A notation "x OP y" := (f x y) (at level N) makes OP an infix operator
%  of the file, and folds f x y back into x OP y when it is drawn.
record_notation(notation(_, _, S, E, Mods)) :-
    split_string(S, " ", "", [X, Op0, Y]), X \== "", Y \== "",
    atom_string(Op, Op0), \+ std_op(Op, _, _),
    (   append(_, [level, N|_], Mods), atom_number(N, Lv) -> true ; Lv = 70 ),
    (   append(_, [right, associativity|_], Mods) -> As = right
    ;   append(_, [left, associativity|_], Mods) -> As = left
    ;   As = none
    ), !,
    retractall(notation_op(Op, _, _)), assertz(notation_op(Op, Lv, As)),
    (   unparen(E, app(_, id(_, F), [id(_, X1), id(_, Y1)])),
        atom_string(X1, X), atom_string(Y1, Y)
    ->  retractall(notation_fold(F, _, _)), assertz(notation_fold(F, 2, Op))
    ;   true
    ).
record_notation(notation(_, 'Infix', S, E, Mods)) :-
    atom_string(Op, S), \+ std_op(Op, _, _), unparen(E, id(_, F)),
    (   append(_, [level, N|_], Mods), atom_number(N, Lv) -> true ; Lv = 70 ),
    (   append(_, [right, associativity|_], Mods) -> As = right
    ;   append(_, [left, associativity|_], Mods) -> As = left
    ;   As = none
    ), !,
    retractall(notation_op(Op, _, _)), assertz(notation_op(Op, Lv, As)),
    retractall(notation_fold(F, _, _)), assertz(notation_fold(F, 2, Op)).
record_notation(_).

unparen(paren(_, E0), E) :- !, unparen(E0, E).
unparen(E, E).

%% Fragments

%  rocq_fragment_codes(+Codes, -Fragment): Rocq written inline in prose:
%  a sentence without its full stop (sentence(S)), a type's constructors
%  (cap := None | Obj base, alts(Name, Terms)), a record's fields
%  (ptr := { addr : Z; cap : cap }, fields(Name, Fields)), a typed name
%  (step : config -> outcome, typed(Name, Type)), or a term (term(E)).
rocq_fragment_codes(Cs, Frag) :-
    catch(rocq_lex(Cs, Toks, []), _, fail), Toks \== [],
    \+ memberchk(t(dot, _, _), Toks),
    Toks = [t(_, F, _)|_], last(Toks, t(_, _, T)),
    phrase(fragment(F-T, Frag), Toks), !.

fragment(P, sentence(S)) --> peek(id(K)), { vernac_keyword(K) }, sentence(P, S).
fragment(_, alts(N, [C|Cs])) --> name(N), tk(sym(':=')), expr(99, C), tk(sym('|')), alt_terms(Cs).
fragment(_, fields(N, Fs)) --> name(N), tk(sym(':=')), tk(p('{')), fields(Fs), tk(p('}')).
fragment(_, typed(N, Ty)) --> name(N), tk(sym(':')), term(Ty).
% Rocq's printed local context, including grouped names and definitions.
fragment(_, context(Ns, Body, Ty)) -->
    names(Ns), ( tk(sym(':=')) -> term(Body) ; { Body = none } ),
    tk(sym(':')), term(Ty).
fragment(_, term(E)) --> term(E).

alt_terms([C|Cs]) --> expr(99, C), ( tk(sym('|')) -> alt_terms(Cs) ; { Cs = [] } ).

vernac_keyword(K) :- memberchk(K, ['Inductive', 'Record', 'Definition', 'Fixpoint', 'Theorem', 'Lemma',
                                   'Axiom', 'Parameter', 'Module', 'Notation', 'Corollary']).
