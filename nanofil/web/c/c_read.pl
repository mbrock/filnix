/*  c_read: a C file as nanofil's frontend reads it, for drawing.

    The parse is the compiler's own: c_lex's c_tokens/3 lexes the file and
    c_parse's grammar reads one external declaration at a time
    (external_decl//4, block_item//3 in a function body). The file is not
    preprocessed, so macros stay as written: a macro used as a function
    is a call, an object macro a name, and the page shows the source,
    not its expansion. What the grammar needs from headers is which names
    are typedefs; c_read starts from the standard library's and learns
    the file's own as the parser does.

    The lexer skips comments and preprocessor lines, so c_read scans the
    text for them itself, with their lines, and blanks each directive
    (with its continuation lines) before lexing, since c_lex reads only
    one line of a directive. It also records how each integer constant
    was spelled (0x1F, 10UL), which the tokens no longer say.

    Where the grammar refuses something (a macro used as a statement or
    declaration, an attribute the compiler does not take, K&R
    parameters), only that part is kept as its tokens: a statement in a
    function body, or the whole external declaration. Nothing is dropped.

    c_read_text(+Text, +Name, -Unit) gives
    `unit(Items, Comments, Directives, Spellings, Lines)`:

    | Part | Is |
    |---|---|
    | Items | `item(From, To, Item)`, Item a c_parse item; `fun(From, To, Specs, Dcl, Body)`, a function whose body was read statement by statement; `raw(From, To, Tokens, Why)` |
    | Comments | `cm(From, To, Text, Trail)`: Text without its delimiters, Trail `yes` when code precedes it on line From |
    | Directives | `dir(From, To, Text)`, Text with continuations joined |
    | Spellings | `V-S-Spelling` for each integer constant `num(V, S)` |
    | Lines | the text's lines, as strings |

    In a recovered body a statement the grammar refused is
    `raw(From, To, Tokens, Why)`.

    Loading: c_read_load(+SrcDir) loads src/swi/compat.pl and the lexer,
    types and parser from nanofil's src directory, as bin/nanofil does.
    It is called before the first read, after the drawing modules are
    compiled, because compat.pl changes how later modules read strings.
*/
:- module(c_read, [c_read_load/1, c_read_text/3, c_read_file/3, c_unit_lines/2, c_unit_spelling/3]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(assoc)).
:- use_module(library(readutil)).

%! c_read_load(+SrcDir) is det.
c_read_load(Dir) :-
    directory_file_path(Dir, 'swi/compat.pl', Compat),
    load_files(user:Compat, [if(not_loaded), silent(true)]),
    forall(member(M, [c_lex, c_types, c_parse]),
           ( file_name_extension(M, pl, F), directory_file_path(Dir, F, P),
             load_files(user:P, [if(not_loaded), silent(true)]) )).

%! c_read_file(+Path, -Text, -Unit) is det.
c_read_file(Path, Text, Unit) :-
    read_file_to_string(Path, Text, [encoding(utf8)]),
    file_base_name(Path, Name),
    c_read_text(Text, Name, Unit).

c_unit_lines(unit(_, _, _, _, Lines), Lines).

%! c_unit_spelling(+Unit, +Num, -Spelling) is semidet.
%  Spelling is how the file wrote the constant num(V, S).
c_unit_spelling(unit(_, _, _, Sp, _), num(V, S), Spelling) :- memberchk(V-S-Spelling, Sp).

%! c_read_text(+Text, +Name, -Unit) is det.
c_read_text(Text, Name, unit(Items, Cms, Dirs, Spellings, Lines)) :-
    split_string(Text, "\n", "", Lines),
    string_codes(Text, Cs),
    phrase(scan(Ev, 1, bol), Cs),
    partition([E]>>(E = cm(_, _, _, _)), Ev, Cms, Ev1),
    partition([E]>>(E = dir(_, _, _)), Ev1, Dirs, Nums),
    blank_directives(Lines, Dirs, Blanked),
    atomic_list_concat(Blanked, '\n', B), atom_chars(B, Chars),
    (   catch(c_lex:c_tokens(Chars, Name, Tokens0), _, fail) -> true
    ;   lex_lines(Blanked, Name, 1, Tokens0)
    ),
    rename_builtins(Tokens0, Tokens),
    spellings(Nums, Tokens, Spellings),
    seed_env(Env),
    phrase(items(Env, Items), Tokens).

%% Scanning: comments, directives and integer spellings

% scan(-Events, +Line, +State)//: State is bol at a line's start (only
% blanks so far), code after code, mid within a line without code yet.
scan(Ev, L, _) --> "\n", !, { L1 is L + 1 }, scan(Ev, L1, bol).
scan(Ev, L, S) --> [C], { memberchk(C, ` \t\r\f\v`) }, !, scan(Ev, L, S).
scan([dir(L, L1, Text)|Ev], L, bol) --> "#", !,
    directive(Cs, L, L1), { string_codes(Text0, [0'#|Cs]), split_string(Text0, "", " \t\r", [Text]) },
    scan(Ev, L1, bol).
scan([cm(L, L1, Text, Trail)|Ev], L, S) --> "/*", !,
    block_comment(Cs, L, L1), { string_codes(Text, Cs), trail(S, Trail) },
    scan(Ev, L1, S).
scan([cm(L, L, Text, Trail)|Ev], L, S) --> "//", !,
    line_rest(Cs), { string_codes(Text, Cs), trail(S, Trail) },
    scan(Ev, L, S).
scan(Ev, L, _) --> "\"", !, quoted(0'", L, L1), scan(Ev, L1, code).
scan(Ev, L, _) --> "'", !, quoted(0'', L, L1), scan(Ev, L1, code).
scan([num(L, Sp)|Ev], L, _) --> [C], { digit(C) }, !,
    ppnum(Cs), { atom_codes(Sp, [C|Cs]) }, scan(Ev, L, code).
scan(Ev, L, _) --> [C], { ident(C) }, !, ident_rest, scan(Ev, L, code).
scan(Ev, L, _) --> "\\\n", !, { L1 is L + 1 }, scan(Ev, L1, code).
scan(Ev, L, _) --> [_], !, scan(Ev, L, code).
scan([], _, _) --> [].

trail(code, yes) :- !.
trail(_, no).

directive(Cs, L, L1) --> "\\\n", !, { L2 is L + 1 }, directive(Cs0, L2, L1), { Cs = [0' |Cs0] }.
directive([], L, L), "\n" --> "\n", !.
directive(Cs, L, L1) --> "/*", !, block_comment(_, L, L2), directive(Cs0, L2, L1), { Cs = [0' |Cs0] }.
directive([], L, L) --> "//", !, line_rest(_).
directive([C|Cs], L, L1) --> [C], !, directive(Cs, L, L1).
directive([], L, L) --> [].

block_comment([], L, L) --> "*/", !.
block_comment([0'\n|Cs], L, L1) --> "\n", !, { L2 is L + 1 }, block_comment(Cs, L2, L1).
block_comment([C|Cs], L, L1) --> [C], !, block_comment(Cs, L, L1).
block_comment([], L, L) --> [].

line_rest([]), "\n" --> "\n", !.
line_rest([C|Cs]) --> [C], !, line_rest(Cs).
line_rest([]) --> [].

quoted(Q, L, L) --> [Q], !.
quoted(_, L, L), "\n" --> "\n", !.
quoted(Q, L, L1) --> "\\\n", !, { L2 is L + 1 }, quoted(Q, L2, L1).
quoted(Q, L, L1) --> "\\", [_], !, quoted(Q, L, L1).
quoted(Q, L, L1) --> [_], !, quoted(Q, L, L1).
quoted(_, L, L) --> [].

% A pp-number (C11 6.4.8): digits, letters, _, ., and e+ e- p+ p-.
ppnum([E, S|Cs]) --> [E, S], { memberchk(E, `eEpP`), memberchk(S, `+-`) }, !, ppnum(Cs).
ppnum([C|Cs]) --> [C], { ident(C) ; digit(C) ; C == 0'. ; C == 0'' }, !, ppnum(Cs).
ppnum([]) --> [].

ident_rest --> [C], { ident(C) ; digit(C) }, !, ident_rest.
ident_rest --> [].

digit(C) :- between(0'0, 0'9, C).
ident(C) :- ( between(0'a, 0'z, C) ; between(0'A, 0'Z, C) ; C == 0'_ ; C == 0'$ ), !.

% blank_directives(+Lines, +Dirs, -Blanked): Lines with each directive's
% lines empty, so c_lex sees no directive and every line keeps its number.
blank_directives(Lines, Dirs, Blanked) :-
    findall(N, ( member(dir(F, T, _), Dirs), between(F, T, N) ), Ns0), sort(Ns0, Ns),
    blank_lines(Lines, 1, Ns, Blanked).

blank_lines([], _, _, []).
blank_lines([L|Ls], N, Ns, [B|Bs]) :-
    ( Ns = [N|Ns1] -> B = "" ; Ns1 = Ns, B = L ),
    N1 is N + 1, blank_lines(Ls, N1, Ns1, Bs).

% lex_lines(+Lines, +Name, +N, -Tokens): a line at a time, when the whole
% text does not lex; a line that does not lex is left out.
lex_lines([], _, _, []).
lex_lines([L|Ls], Name, N, Ts) :-
    string_chars(L, Cs),
    (   catch(c_lex:c_tokens(Cs, Name, Ts0), _, fail)
    ->  maplist([tok(T, F:_), tok(T, F:N)]>>true, Ts0, Ts1)
    ;   Ts1 = []
    ),
    append(Ts1, Ts2, Ts), N1 is N + 1, lex_lines(Ls, Name, N1, Ts2).

% offsetof and va_arg are the standard headers' macros for the
% builtins the grammar reads; read them as those, and draw them by
% their usual names.
rename_builtins([], []).
rename_builtins([tok(id(N), L)|Ts0], [tok(id(B), L)|Ts]) :- builtin_macro(N, B), !, rename_builtins(Ts0, Ts).
rename_builtins([T|Ts0], [T|Ts]) :- rename_builtins(Ts0, Ts).

builtin_macro(offsetof, '__builtin_offsetof').
builtin_macro(va_arg, '__builtin_va_arg').

% spellings(+Nums, +Tokens, -Spellings): each integer token with the
% spelling the scan found in the same place. The scan and c_lex skip the
% same text, so the Kth integer of one is the Kth of the other; where
% their counts differ nothing is paired.
spellings(Nums, Tokens, Spellings) :-
    include([num(_, Sp)]>>integer_spelling(Sp), Nums, INums),
    include([tok(T, _)]>>(T = int(_, _)), Tokens, ITs),
    (   same_length(INums, ITs)
    ->  findall(V-S-Sp, ( nth1(K, ITs, tok(int(V, S), _)), nth1(K, INums, num(_, Sp)) ), Ps0),
        sort(1, @<, Ps0, Spellings)
    ;   Spellings = []
    ).

integer_spelling(Sp) :-
    atom_codes(Sp, Cs), \+ memberchk(0'., Cs),
    (   hex_spelling(Cs) -> \+ ( member(P, Cs), memberchk(P, `pP`) )
    ;   \+ ( member(E, Cs), memberchk(E, `eE`) )
    ).

hex_spelling([0'0, X|_]) :- memberchk(X, `xX`).

%% Typedef names

% The typedefs of the standard headers and POSIX that C files use
% without defining; the grammar needs them to tell a declaration from an
% expression. A file's own typedefs are learnt as it is read.
std_typedef(N) :- member(N, [
    size_t, ssize_t, ptrdiff_t, intptr_t, uintptr_t, intmax_t, uintmax_t, max_align_t,
    int8_t, int16_t, int32_t, int64_t, uint8_t, uint16_t, uint32_t, uint64_t,
    int_least8_t, int_least16_t, int_least32_t, int_least64_t,
    uint_least8_t, uint_least16_t, uint_least32_t, uint_least64_t,
    int_fast8_t, int_fast16_t, int_fast32_t, int_fast64_t,
    uint_fast8_t, uint_fast16_t, uint_fast32_t, uint_fast64_t,
    wchar_t, wint_t, char16_t, char32_t, char8_t, mbstate_t, wctype_t, wctrans_t,
    bool, 'FILE', fpos_t, va_list, jmp_buf, sigjmp_buf, sig_atomic_t, sigset_t,
    off_t, off64_t, pid_t, uid_t, gid_t, mode_t, dev_t, ino_t, nlink_t, blksize_t, blkcnt_t,
    time_t, clock_t, clockid_t, timer_t, suseconds_t, useconds_t, socklen_t,
    float_t, double_t, fenv_t, fexcept_t, div_t, ldiv_t, lldiv_t, imaxdiv_t, locale_t,
    pthread_t, pthread_attr_t, pthread_mutex_t, pthread_mutexattr_t, pthread_cond_t,
    pthread_condattr_t, pthread_key_t, pthread_once_t, pthread_rwlock_t, pthread_spinlock_t,
    pthread_barrier_t, sem_t, thrd_t, mtx_t, cnd_t, tss_t, once_flag, ucontext_t, 'DIR',
    atomic_bool, atomic_char, atomic_schar, atomic_uchar, atomic_short, atomic_ushort,
    atomic_int, atomic_uint, atomic_long, atomic_ulong, atomic_llong, atomic_ullong,
    atomic_intptr_t, atomic_uintptr_t, atomic_size_t, atomic_ptrdiff_t, atomic_flag,
    '__builtin_va_list', '__int128_t', '__uint128_t', '__m128', '__m128i', '__m128d',
    '__m256', '__m256i', '__m256d'
]).

seed_env(Env) :- findall(N-t, std_typedef(N), Ps), list_to_assoc(Ps, Env).

%% Items

% items(+Env, -Items)//: the external declarations of the tokens, each
% with its lines. One the grammar refuses is read again with the names
% that stand where a type would as typedefs, then as a function whose
% body is read a statement at a time, and otherwise kept as tokens.
items(_, []) --> eos, !.
items(Env0, Items) --> first_line(F), item(Env0, Env, Items, Items1, F), items(Env, Items1).

item(Env0, Env, Items, Items1, F, S0, S) :-
    (   decl_at(Env0, Env, Is, S0, S)
    ->  last_line(S0, S, T), wrap(Is, F, T, Items, Items1)
    ;   item_extent(S0, Toks, _), typedef_guesses(Toks, Env0, Guesses), Guesses \== [],
        foldl(c_parse:typedef_declared, Guesses, Env0, EnvG),
        decl_at(EnvG, Env, Is, S0, S)
    ->  last_line(S0, S, T), wrap(Is, F, T, Items, Items1)
    ;   recovered_function(Env0, Env1, Specs, Dcl, Body, S0, S1)
    ->  S = S1, Env = Env1, last_line(S0, S, T), Items = [fun(F, T, Specs, Dcl, Body)|Items1]
    ;   ( item_extent(S0, _, S1) -> true ; S1 = [] ),
        decl_error(Env0, S0, Why), item_tokens(S0, S1, Toks1), last_line(S0, S1, T),
        S = S1, Env = Env0, Items = [raw(F, T, Toks1, Why)|Items1]
    ).

wrap([], _, _, Items, Items).
wrap([I], F, T, [item(F, T, I)|Items], Items).

decl_at(Env0, Env, Is, S0, S) :-
    catch(phrase(c_parse:external_decl(Env0, Env, Is, []), S0, S), _, fail).

decl_error(Env, S0, Why) :-
    catch(( phrase(c_parse:external_decl(Env, _, _, []), S0, _), Why = "" ), E, error_text(E, Why)), !.
decl_error(_, _, "").

error_text(nanofil_error(M), Why) :- !, strip_location(M, Why).
error_text(E, Why) :- format(string(Why), "~q", [E]).

% The parser's messages start with File:Line; the page says where.
strip_location(M, Why) :-
    atom_string(M, S),
    (   sub_string(S, B, _, A, ": "), sub_string(S, 0, B, _, Loc), sub_string(Loc, _, _, 0, D),
        string_code(1, D, C), digit(C)
    ->  sub_string(S, _, A, 0, Why)
    ;   Why = S
    ).

% A function definition whose declarator reads but whose body does not:
% the body is read a statement at a time, each refused one kept as its
% tokens.
recovered_function(Env0, Env, Specs, Dcl, Body, S0, S) :-
    catch(phrase(( c_parse:decl_specs(Env0, Specs0), c_parse:full_declarator(Env0, Dcl, Attrs) ), S0, S1), _, fail),
    Dcl = dcl(some(Name), func(_, Params), _), Params \= knr(_),
    S1 = [tok(p('{'), _)|_],
    c_parse:typedefs_hidden([Name], Env0, Env),
    ( Params = params(_, _) -> c_parse:params_env(Params, Env, BodyEnv) ; BodyEnv = Env ),
    phrase(rblock(BodyEnv, Body), S1, S),
    append(Specs0, Attrs, Specs).

% rblock(+Env, -Block)//: a block whose items are read one at a time.
rblock(Env, at(Loc, block(Items))) --> [tok(p('{'), Loc)], ritems(Env, Items).

ritems(_, []) --> [tok(p('}'), _)], !.
ritems(_, []) --> eos, !.
ritems(Env0, [I|Is]) --> ritem(Env0, Env, I), ritems(Env, Is).

ritem(Env0, Env, I, S0, S) :-
    (   catch(phrase(c_parse:block_item(Env0, Env, I), S0, S), _, fail) -> true
    ;   S0 = [tok(p('{'), _)|_] -> Env = Env0, phrase(rblock(Env0, I), S0, S)
    ;   S0 = [tok(kw(case), Loc)|S1],
        catch(phrase(( c_parse:conditional(Env0, E), [tok(p(':'), _)] ), S1, S2), _, fail)
    ->  ritem(Env0, Env, Body, S2, S), I = at(Loc, case(E, Body))
    ;   S0 = [tok(kw(default), Loc), tok(p(':'), _)|S1]
    ->  ritem(Env0, Env, Body, S1, S), I = at(Loc, default(Body))
    ;   S0 = [tok(id(L), Loc), tok(p(':'), _)|S1]
    ->  ritem(Env0, Env, Body, S1, S), I = at(Loc, label(L, Body))
    ;   S0 = [tok(kw(K), Loc)|S1], memberchk(K, [if, while, switch]),
        catch(phrase(paren_expr(Env0, E), S1, S2), _, fail)
    ->  Env = Env0, ritem(Env0, _, Body, S2, S3),
        (   K == if
        ->  (   S3 = [tok(kw(else), _)|S4] -> ritem(Env0, _, Else, S4, S) ; Else = none, S = S3 ),
            I = at(Loc, if(E, Body, Else))
        ;   S = S3, I0 =.. [K, E, Body], I = at(Loc, I0)
        )
    ;   S0 = [tok(kw(do), Loc)|S1], ritem(Env0, _, Body, S1, S2), S2 = [tok(kw(while), _)|S3],
        catch(phrase(( paren_expr(Env0, E), [tok(p(';'), _)] ), S3, S4), _, fail)
    ->  Env = Env0, S = S4, I = at(Loc, do(Body, E))
    ;   Env = Env0,
        (   catch(( phrase(c_parse:block_item(Env0, _, _), S0, _), Why = "" ), Err, error_text(Err, Why)) -> true
        ;   Why = ""
        ),
        stmt_extent(S0, S), item_tokens(S0, S, Toks), S0 = [tok(_, _:F)|_], last_line(S0, S, T),
        I = raw(F, T, Toks, Why)
    ).

paren_expr(Env, E) --> [tok(p('('), _)], c_parse:expr(Env, E), [tok(p(')'), _)].

% item_extent(+S0, -Toks, -S): an external declaration's tokens: through
% a ';' outside brackets, or a '}' that closes them unless ';', ',', '='
% or a declarator follows it on the same line.
item_extent(S0, Toks, S) :- extent(S0, 0, item, S), S0 \== S, item_tokens(S0, S, Toks).

% stmt_extent(+S0, -S): a statement's tokens: through a ';' outside
% brackets, or a '}' that closes them unless else or while follows.
stmt_extent(S0, S) :- extent(S0, 0, stmt, S1), ( S1 == S0 -> S0 = [_|S] ; S = S1 ).

extent([], _, _, []).
extent([tok(p(P), _)|S0], 0, _, S0) :- P == ';', !.
extent([tok(p(P), _)|S0], D0, K, S) :- memberchk(P, ['{', '(', '[']), !, D is D0 + 1, extent(S0, D, K, S).
extent([tok(p(P), L)|S0], D0, K, S) :- memberchk(P, ['}', ')', ']']), !, D is max(0, D0 - 1),
    (   D == 0, P == '}', closes(K, S0, L) -> S = S0 ; extent(S0, D, K, S) ).
extent([_|S0], D, K, S) :- extent(S0, D, K, S).

closes(stmt, [tok(kw(W), _)|_], _) :- memberchk(W, [else, while]), !, fail.
closes(stmt, _, _) :- !.
closes(item, [tok(T, _:L1)|_], _:L) :- L1 == L, ( T = p(P), memberchk(P, [';', ',', '=', '*']) ; T = id(_) ), !, fail.
closes(item, _, _).

item_tokens(S0, S, Toks) :- append(Toks, S, S0), !.

% typedef_guesses(+Toks, +Env, -Names): identifiers where a type would
% stand, not yet typedefs: at the start of a declaration or parameter
% (after nothing, ';', '{', '}', '(' or ',', or a qualifier or storage
% class) and followed by an identifier or '*'.
typedef_guesses(Toks, Env, Names) :-
    findall(N, ( append(Pre, [tok(id(N), _), tok(Next, _)|_], Toks),
                 ( Next = id(_) ; Next == p('*') ),
                 \+ get_assoc(N, Env, _),
                 ( Pre == [] -> true ; last(Pre, tok(P, _)), guess_before(P) ) ), Ns),
    sort(Ns, Names).

guess_before(p(P)) :- memberchk(P, [';', '{', '}', '(', ',']).
guess_before(kw(K)) :- memberchk(K, [const, volatile, static, extern, register, inline, typedef, restrict]).

%% Lines

first_line(F), [tok(T, File:F)] --> [tok(T, File:F)].

eos([], []).

% last_line(+S0, +S, -T): the line of the last token of S0 before S.
last_line(S0, S, T) :- item_tokens(S0, S, Toks), ( last(Toks, tok(_, _:T)) -> true ; S0 = [tok(_, _:T)|_] ).
