/*  C preprocessor (milestone 4e).

    Preprocessing tokens are t(Spelling, File:Line, Space, Hide): the
    spelling as an atom, the location, whether whitespace precedes the
    token (yes or no; # and #define need it) and the hide set, the sorted
    macro names that must not expand this token again. A newline is the
    token nl until the input is split into lines.

    The environment is env(Macros, IncludeDirs, Features, Once, File):
    an assoc from names to obj(Body) or fun(Params, Body) (and from
    saved(Name) to #pragma push_macro stacks), the include search path,
    the target's feature answers, the files seen by #pragma once, and the
    file whose directives are being processed.

    Only the file and target-profile adapters do I/O. No C source or
    header is sent to clang.
*/
:- module(c_pp, [pp_file/3, pp_profile/2]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(pio)).
:- use_module(library(assoc)).
:- use_module(library(process)).
:- use_module(library(charsio)).
:- use_module(c_lex).

% pp_file(+File, +Profile, -Tokens): File preprocessed into c_lex tokens.
% Profile is profile(Macros, IncludeDirs, FeatureAnswers) from pp_profile/2.
pp_file(File, profile(Macros, Paths, Features), Tokens) :-
    preprocess(File, env(Macros, Paths, Features, [], File), _, PpTokens),
    phrase(lex_tokens(PpTokens), Tokens).

% Each preprocessing token is lexed on its own and keeps its location.
lex_tokens([]) --> [].
lex_tokens([t(A, Loc, _, _)|PpTokens]) -->
    {   atom_chars(A, Cs),
        c_tokens(Cs, '<preprocessing token>', Lexed),
        maplist(relocate(Loc), Lexed, Tokens)
    },
    seq(Tokens),
    lex_tokens(PpTokens).

relocate(Loc, tok(T, _), tok(T, Loc)).

% preprocess(+File, +Env0, -Env, -Tokens): File's expanded tokens. Env
% carries the macros and the #pragma once set back to the includer.
preprocess(File, Env0, Env, Tokens) :-
    Env0 = env(Macros0, Paths, Features, Once0, Includer),
    absolute_file_name(File, Identity),
    (   memberchk(Identity, Once0)
    ->  Env = Env0,
        Tokens = []
    ;   read_source(File, PpTokens),
        token_lines(PpTokens, Lines),
        process_lines(Lines, File, [], [],
                      env(Macros0, Paths, Features, Once0, File), End,
                      Tokens, []),
        End = env(Macros, Paths, Features, Once, _),
        Env = env(Macros, Paths, Features, Once, Includer)
    ).

% Impure file adapter. Keep the input buffer local so it can be reclaimed
% before processing nested includes; the macro environment stays explicit.
read_source(File, PpTokens) :-
    phrase_from_file(seq(Cs), File),
    once(source_tokens(Cs, File:1, PpTokens)).

%% Translation phases 2 and 3

% A comment is one whitespace character, even across physical newlines.
% A parallel location vector survives splicing even inside identifiers and
% literals. In particular __LINE__ after a continuation is the physical
% source line, not the number of newlines in the spliced buffer.
source_tokens(Cs, Loc, PpTokens) :-
    located_splice(Cs, Loc, Spliced, Locs),
    phrase(scan(PpTokens, Locs, yes), Spliced).

% located_splice(+Chars, +Loc, -Spliced, -Locs): remove backslash-newline
% and give each remaining character its physical location.
located_splice(['\\', '\r', '\n'|Cs], File:N, Spliced, Locs) :- !,
    N1 is N + 1,
    located_splice(Cs, File:N1, Spliced, Locs).
located_splice(['\\', '\n'|Cs], File:N, Spliced, Locs) :- !,
    N1 is N + 1,
    located_splice(Cs, File:N1, Spliced, Locs).
% Share one location term per physical line, not one per character.
located_splice([C|Cs], Loc, [C|Spliced], [Loc|Locs]) :- !,
    (   C == '\n'
    ->  Loc = File:N,
        N1 is N + 1,
        Loc1 = File:N1
    ;   Loc1 = Loc
    ),
    located_splice(Cs, Loc1, Spliced, Locs).
located_splice([], _, [], []).

% scan(PpTokens, Locs, Space): Locs runs in step with the input
% characters; Space says whether whitespace precedes the next token.
scan([nl|Ts], [_|Locs], _) --> ['\n'], !, scan(Ts, Locs, yes).
scan(Ts, [_|Locs], _) --> [C], { space(C) }, !, scan(Ts, Locs, yes).
scan(Ts, [_, _|Locs], _) -->
    ['/', '/'], !,
    line_comment(Locs, Rest),
    scan(Ts, Rest, yes).
scan(Ts, [_, _|Locs], _) -->
    ['/', '*'], !,
    block_comment(Locs, Rest),
    scan(Ts, Rest, yes).
scan([t(A, Loc, Space, [])|Ts], [Loc|Locs], Space) -->
    spelling(Cs), !,
    {   atom_chars(A, Cs),
        length(Cs, N),
        N1 is N - 1,
        drop(N1, Locs, Rest)
    },
    scan(Ts, Rest, no).
scan([], [], _) --> [].

drop(0, Xs, Xs) :- !.
drop(N, [_|Xs], Rest) :- N1 is N - 1, drop(N1, Xs, Rest).

space(' ').
space('\t').
space('\r').
space('\f').
space('\v').

% The comment's characters and their locations, leaving the newline.
line_comment(Locs, Locs), ['\n'] --> ['\n'], !.
line_comment([_|Locs], Rest) --> [_], !, line_comment(Locs, Rest).
line_comment([], []) --> [].

block_comment([_, _|Locs], Locs) --> ['*', '/'], !.
block_comment([_|Locs], Rest) --> [_], !, block_comment(Locs, Rest).
block_comment(_, _) -->
    { throw(nanofil_error('unterminated preprocessing comment')) }.

% spelling(Chars): one preprocessing token.
spelling([P, Q|Cs]) -->
    [P, Q], { memberchk(P, ['L', u, 'U']), memberchk(Q, ['"', '\'']) }, !,
    quoted(Q, Cs).
spelling([Q|Cs]) --> [Q], { memberchk(Q, ['"', '\'']) }, !, quoted(Q, Cs).
spelling([C|Cs]) --> [C], { ident_start(C) }, !, ident_rest(Cs).
spelling([C|Cs]) --> [C], { digit(C) }, !, number_rest(Cs).
spelling(['.', C|Cs]) --> ['.', C], { digit(C) }, !, number_rest(Cs).
spelling(Cs) -->
    [A, B, C],
    {   Cs = [A, B, C],
        atom_chars(P, Cs),
        memberchk(P, ['...', '<<=', '>>='])
    }, !.
spelling(Cs) -->
    [A, B],
    {   Cs = [A, B],
        atom_chars(P, Cs),
        memberchk(P, ['##', '->', '++', '--', '<<', '>>', '<=', '>=', '==',
                      '!=', '&&', '||', '*=', '/=', '%=', '+=', '-=', '&=',
                      '^=', '|=', '<:', ':>', '<%', '%>', '%:'])
    }, !.
spelling([C]) --> [C].

quoted(Q, ['\\', C|Cs]) --> ['\\', C], !, quoted(Q, Cs).
quoted(Q, [Q]) --> [Q], !.
quoted(Q, [C|Cs]) --> [C], { C \== '\n' }, !, quoted(Q, Cs).
quoted(_, _) -->
    { throw(nanofil_error('unterminated preprocessing literal')) }.

ident_start(C) :- ( C @>= a, C @=< z ; C @>= 'A', C @=< 'Z' ), !.
ident_start('_').
ident_start('$').

digit(C) :- C @>= '0', C @=< '9'.

ident_char(C) :- ident_start(C), !.
ident_char(C) :- digit(C).

ident_rest([C|Cs]) --> [C], { ident_char(C) }, !, ident_rest(Cs).
ident_rest([]) --> [].

number_rest([E, S|Cs]) -->
    [E, S],
    { memberchk(E, [e, 'E', p, 'P']), memberchk(S, ['+', '-']) }, !,
    number_rest(Cs).
number_rest([C|Cs]) --> [C], { ident_char(C) ; C == '.' }, !, number_rest(Cs).
number_rest([]) --> [].

%% Lines and directives

token_lines([], []).
token_lines(Ts, [Line|Lines]) :-
    Ts \= [],
    take_line(Ts, Line, Rest),
    token_lines(Rest, Lines).

take_line([], [], []).
take_line([nl|Ts], [], Ts) :- !.
take_line([T|Ts], [T|Line], Rest) :- take_line(Ts, Line, Rest).

% process_lines(+Lines, +File, +Stack, +Pending, +Env0, -Env, -Ts, ?End):
% Ordinary lines are collected in Pending (reversed) and expanded
% together, so a function invocation can span newlines. Directives are
% barriers; inactive groups never expand tokens.
process_lines([], File, Stack, Pending, Env, Env, Ts, End) :-
    ( Stack = [] -> true ; pp_error(File:1, 'unterminated #if') ),
    expand_pending(Pending, Env, Expanded),
    append(Expanded, End, Ts).
process_lines([Line|Lines], File, Stack, Pending, Env0, Env, Ts, End) :-
    (   Line = [t('#', HashLoc, _, _)|Directive]
    ->  expand_pending(Pending, Env0, Expanded),
        append(Expanded, Rest, Ts),
        (   Directive = [t(line, _, _, _)|Args], active(Stack)
        ->  expand(Args, Env0, Marker),
            line_target(Marker, HashLoc, Target),
            remap_lines(Lines, HashLoc, Target, More),
            Stack1 = Stack,
            Env1 = Env0,
            Rest = Next
        ;   directive(Directive, File, Stack, Stack1, Env0, Env1, Rest, Next),
            More = Lines
        ),
        process_lines(More, File, Stack1, [], Env1, Env, Next, End)
    ;   active(Stack)
    ->  process_lines(Lines, File, Stack, [Line|Pending], Env0, Env, Ts, End)
    ;   process_lines(Lines, File, Stack, Pending, Env0, Env, Ts, End)
    ).

% #line N ["file"]: the line after the directive is line N (of file).
line_target([t(A, _, _, _)|Ts], File:_, NewFile:N) :-
    atom_number(A, N),
    integer(N),
    N > 0,
    ( Ts = [] -> NewFile = File ; include_name(Ts, NewFile, quote) ).

remap_lines([], _, _, []).
remap_lines([Ts|Lines], Old, New, [Rs|Rest]) :-
    maplist(remap_token(Old, New), Ts, Rs),
    remap_lines(Lines, Old, New, Rest).

remap_token(Old, New, t(A, Loc, Space, Hide), t(A, Loc1, Space, Hide)) :-
    remap_location(Old, New, Loc, Loc1).

remap_location(_:Old, File:New, _:N, File:M) :- M is N-Old-1+New.

expand_pending(Pending, Env, Ts) :-
    reverse(Pending, Lines),
    append(Lines, Flat),
    expand(Flat, Env, Ts).

% The conditional stack has one cond(Taken, Seen, Parent) per open #if:
% Taken says whether the current group is active, Seen whether an earlier
% group was taken (yes, no, or else after #else), Parent whether the
% enclosing group is active.
active([]).
active([cond(yes, _, _)|_]).

condition_truth(V, yes) :- V =\= 0, !.
condition_truth(_, no).

% directive(+Tokens, +File, +Stack0, -Stack, +Env0, -Env, -Ts, ?Rest): one
% directive line after its '#'. Conditionals are tracked even in inactive
% groups; other directives only run in active ones. Ts is Rest with an
% included file's tokens in front.
directive([], _, Stack, Stack, Env, Env, Ts, Ts) :- !.
directive([t(Name, Loc, _, _)|Args], File, Stack0, Stack, Env0, Env,
          Ts, Rest) :-
    (   conditional_directive(Name)
    ->  conditional(Name, Loc, Args, Env0, Stack0, Stack),
        Env = Env0,
        Ts = Rest
    ;   active(Stack0)
    ->  Stack = Stack0,
        active_directive(Name, Loc, Args, File, Env0, Env, Ts, Rest)
    ;   Stack = Stack0,
        Env = Env0,
        Ts = Rest
    ).

conditional_directive(if).
conditional_directive(ifdef).
conditional_directive(ifndef).
conditional_directive(elif).
conditional_directive(else).
conditional_directive(endif).

conditional(elif, Loc, Args, Env, Stack0, [cond(Taken, Seen1, Parent)|Tail]) :-
    !,
    (   Stack0 = [cond(_, Seen, Parent)|Tail], Seen \== else
    ->  true
    ;   pp_error(Loc, 'unexpected #elif')
    ),
    (   Parent == yes, Seen == no
    ->  condition(if, Args, Env, V),
        condition_truth(V, Taken)
    ;   Taken = no
    ),
    ( Taken == yes -> Seen1 = yes ; Seen1 = Seen ).
conditional(else, Loc, _, _, Stack0, [cond(Taken, else, Parent)|Tail]) :- !,
    (   Stack0 = [cond(_, Seen, Parent)|Tail], Seen \== else
    ->  true
    ;   pp_error(Loc, 'unexpected #else')
    ),
    ( Seen == no -> Taken = Parent ; Taken = no ).
conditional(endif, Loc, _, _, Stack0, Stack) :- !,
    ( Stack0 = [_|Stack] -> true ; pp_error(Loc, 'unexpected #endif') ).
conditional(Kind, _, Args, Env, Stack0, [cond(Taken, Taken, Parent)|Stack0]) :-
    (   active(Stack0)
    ->  Parent = yes,
        condition(Kind, Args, Env, V),
        condition_truth(V, Taken)
    ;   Parent = no,
        Taken = no
    ).

active_directive(define, _, Args, _, Env0, Env, Ts, Ts) :- !,
    Env0 = env(Macros0, Paths, Features, Once, File),
    define(Args, Macros0, Macros),
    Env = env(Macros, Paths, Features, Once, File).
active_directive(undef, _, Args, _, Env0, Env, Ts, Ts) :- !,
    Args = [t(Name, _, _, _)],
    Env0 = env(Macros0, Paths, Features, Once, File),
    remove_macro(Name, Macros0, Macros),
    Env = env(Macros, Paths, Features, Once, File).
active_directive(Kind, Loc, Args, File, Env0, Env, Ts, Rest) :-
    memberchk(Kind, [include, include_next]), !,
    Env0 = env(_, Paths, _, _, _),
    header_operand(Args, Env0, Name, Form),
    search_paths(Kind, File, Paths, Search),
    (   include_path(Name, Form, File, Search, Path)
    ->  true
    ;   pp_error(Loc, include_not_found(Name))
    ),
    preprocess(Path, Env0, Env, Included),
    append(Included, Rest, Ts).
active_directive(pragma, _, Args, File, Env0, Env, Ts, Ts) :- !,
    pragma(Args, File, Env0, Env).
active_directive(error, Loc, Args, _, _, _, _, _) :- !,
    pp_error(Loc, error_directive(Args)).
active_directive(ident, _, _, _, Env, Env, Ts, Ts) :- !.
active_directive(Name, Loc, _, _, _, _, _, _) :-
    pp_error(Loc, unsupported_directive(Name)).

% #pragma once, push_macro and pop_macro; other pragmas are ignored.
% Macro save stacks use compound assoc keys, which cannot collide with C
% identifier atoms. Pragma operands are deliberately not macro-expanded.
pragma([t(once, _, _, _)], File,
       env(Macros, Paths, Features, Once, Current),
       env(Macros, Paths, Features, [Identity|Once], Current)) :- !,
    absolute_file_name(File, Identity).
pragma([t(Op, _, _, _), t('(', _, _, _), Str, t(')', _, _, _)], _,
       env(Macros0, Paths, Features, Once, Current),
       env(Macros, Paths, Features, Once, Current)) :-
    memberchk(Op, [push_macro, pop_macro]),
    include_name([Str], Name, quote), !,
    (   Op == push_macro
    ->  ( get_assoc(Name, Macros0, Def) -> Saved = some(Def) ; Saved = none ),
        ( get_assoc(saved(Name), Macros0, Stack) -> true ; Stack = [] ),
        put_assoc(saved(Name), Macros0, [Saved|Stack], Macros)
    ;   get_assoc(saved(Name), Macros0, [Saved|Stack])
    ->  put_assoc(saved(Name), Macros0, Stack, Macros1),
        (   Saved = some(Def)
        ->  put_assoc(Name, Macros1, Def, Macros)
        ;   remove_macro(Name, Macros1, Macros)
        )
    ;   Macros = Macros0
    ).
pragma(_, _, Env, Env).

remove_macro(Name, Macros0, Macros) :-
    (   del_assoc(Name, Macros0, _, Macros1)
    ->  Macros = Macros1
    ;   Macros = Macros0
    ).

% A macro is function-like if '(' follows its name without a space.
define([t(Name, _, _, _)|Ts], Macros0, Macros) :-
    (   Ts = [t('(', _, no, _)|Rest]
    ->  macro_params(Rest, Params, Body),
        Def = fun(Params, Body)
    ;   Def = obj(Ts)
    ),
    put_assoc(Name, Macros0, Def, Macros).

% macro_params(+Ts, -Params, -Body): the names up to ')'; a final ...
% (or P...) is variadic(Name).
macro_params([t(')', _, _, _)|Ts], [], Ts) :- !.
macro_params([t('...', _, _, _), t(')', _, _, _)|Ts],
             [variadic('__VA_ARGS__')], Ts) :- !.
macro_params([t(P, _, _, _), t('...', _, _, _), t(')', _, _, _)|Ts],
             [variadic(P)], Ts) :- !.
macro_params([t(P, _, _, _), t(',', _, _, _)|Ts], [P|Ps], Body) :- !,
    macro_params(Ts, Ps, Body).
macro_params([t(P, _, _, _), t(')', _, _, _)|Ts], [P], Ts).

%% Includes

% include_name(+Tokens, -Name, -Form): "name" (quote) or <name> (angle).
include_name([t(A, _, _, _)], Name, quote) :-
    atom_chars(A, ['"'|Cs]),
    append(Chars, ['"'], Cs),
    atom_chars(Name, Chars), !.
include_name([t('<', _, _, _)|Ts], Name, angle) :-
    append(Mid, [t('>', _, _, _)], Ts),
    maplist(token_spelling, Mid, As),
    atomic_list_concat(As, Name).

token_spelling(t(A, _, _, _), A).

% The operand is expanded only if it is not already a header name.
header_operand(Ts, Env, Name, Form) :-
    (   include_name(Ts, Name, Form)
    ->  true
    ;   expand(Ts, Env, Expanded),
        include_name(Expanded, Name, Form)
    ).

include_path(Name, _, _, _, Name) :-
    sub_atom(Name, 0, 1, _, '/'),
    exists_file(Name), !.
include_path(Name, quote, File, _, Path) :-
    file_directory(File, Dir),
    path_join(Dir, Name, Path),
    exists_file(Path), !.
include_path(Name, _, _, Dirs, Path) :-
    member(Dir, Dirs),
    path_join(Dir, Name, Path),
    exists_file(Path), !.

file_directory(File, Dir) :-
    atom_chars(File, Cs),
    reverse(Cs, Rev),
    append(_, ['/'|Tail], Rev), !,
    reverse(Tail, Ds),
    atom_chars(Dir, Ds).
file_directory(_, '.').

path_join(Dir, Name, Path) :- atomic_list_concat([Dir, '/', Name], Path).

% search_paths(+Kind, +File, +Dirs, -Search): #include_next and
% __has_include_next search the directories after the one File is in.
search_paths(include, _, Dirs, Dirs).
search_paths('__has_include', _, Dirs, Dirs).
search_paths(_, File, Dirs, Rest) :-
    (   append(_, [Dir|Rest0], Dirs),
        atom_concat(Dir, '/', Prefix),
        atom_concat(Prefix, _, File)
    ->  Rest = Rest0
    ;   Rest = Dirs
    ).

%% Macro expansion

% Macro replacement uses token hide sets rather than a global recursion
% stack: an unexpandable token stays unexpandable after argument prescan,
% and a replacement may consume a function-call '(' from the input tail.
% A function-like replacement's hide set is the intersection of the hide
% sets of the macro name and of the closing ')', plus the name.
expand([], _, []).
expand([T|Ts], Env, Out) :-
    T = t(A, Loc, Space, Hide),
    Env = env(Macros, _, _, _, _),
    (   \+ memberchk(A, Hide),
        get_assoc(A, Macros, Def),
        replacement(Def, Ts, Rest, Env, Loc, Repl, EndHide)
    ->  (   EndHide = none
        ->  BaseHide = Hide
        ;   hide_intersection(Hide, EndHide, BaseHide)
        ),
        maplist(mark_replaced([A|BaseHide], Loc), Repl, Marked),
        set_first_space(Marked, Space, Replaced),
        append(Replaced, Rest, Next),
        expand(Next, Env, Out)
    ;   builtin(T, Ts, Rest, Env, Repl)
    ->  append(Repl, Rest, Next),
        expand(Next, Env, Out)
    ;   Out = [T|Out1],
        expand(Ts, Env, Out1)
    ).

hide_intersection([], _, []).
hide_intersection([A|As], Bs, Cs) :-
    ( memberchk(A, Bs) -> Cs = [A|Cs1] ; Cs = Cs1 ),
    hide_intersection(As, Bs, Cs1).

% A replacement token moves to the invocation and gains its hide set.
mark_replaced(Hide, Loc, t(A, _, Space, Hide0), t(A, Loc, Space, Hide1)) :-
    append(Hide, Hide0, Hides),
    sort(Hides, Hide1).

set_first_space([], _, []).
set_first_space([t(A, Loc, _, Hide)|Ts], Space, [t(A, Loc, Space, Hide)|Ts]).

% replacement(+Def, +Ts, -Rest, +Env, +Loc, -Repl, -EndHide): EndHide is
% the hide set of a function-like invocation's ')', or none.
replacement(obj(Body), Ts, Ts, _, Loc, Repl, none) :- paste(Body, Repl, Loc).
replacement(fun(Params, Body), [t('(', _, _, _)|Ts], Rest, Env, Loc, Repl,
            EndHide) :-
    macro_arguments(Ts, 0, [], [], Args0, Rest, EndHide),
    ( Args0 = [[]], Params = [] -> Args = [] ; Args = Args0 ),
    bind_params(Params, Args, Env, Bindings, Loc),
    substitute(Body, Bindings, Repl0),
    paste(Repl0, Repl, Loc).

% macro_arguments(+Ts, +Depth, +ArgRev, +ArgsRev, -Args, -Rest, -EndHide):
% the tokens after '(' split at top-level commas, up to the matching ')'
% whose hide set is EndHide.
macro_arguments([t(')', _, _, Hide)|Ts], 0, Rev, Acc, Args, Ts, Hide) :- !,
    reverse(Rev, Arg),
    reverse([Arg|Acc], Args).
macro_arguments([t(',', _, _, _)|Ts], 0, Rev, Acc, Args, Rest, Hide) :- !,
    reverse(Rev, Arg),
    macro_arguments(Ts, 0, [], [Arg|Acc], Args, Rest, Hide).
macro_arguments([T|Ts], Depth, Rev, Acc, Args, Rest, Hide) :-
    T = t(A, _, _, _),
    (   A == '(' -> Depth1 is Depth + 1
    ;   A == ')' -> Depth1 is Depth - 1
    ;   Depth1 = Depth
    ),
    macro_arguments(Ts, Depth1, [T|Rev], Acc, Args, Rest, Hide).

% bind_params(+Params, +Args, +Env, -Bindings, +Loc): bind(P, Raw, Env)
% for each parameter; a variadic one takes the remaining arguments.
bind_params([], [], _, [], _).
bind_params([variadic(P)], Args, Env, [bind(P, Raw, Env)], _) :- !,
    comma_join(Args, Raw).
bind_params([P|Ps], [A|As], Env, [bind(P, A, Env)|Bindings], Loc) :- !,
    bind_params(Ps, As, Env, Bindings, Loc).
bind_params(_, _, _, _, Loc) :- pp_error(Loc, 'wrong macro argument count').

comma_join([], []).
comma_join([A], A) :- !.
comma_join([A|As], Ts) :-
    comma_join(As, Rest),
    append(A, [t(',', '<macro>':0, no, [])|Rest], Ts).

substitute(Ts, Bindings, Rs) :- substitute_tokens(Ts, Bindings, no, Rs).

% substitute_tokens(+Body, +Bindings, +AfterPaste, -Rs): AfterPaste is yes
% right after ##. # P stringifies the raw argument, an operand of ## is
% the raw argument, and any other use is the fully expanded argument; an
% empty argument becomes the placemarker ''.
substitute_tokens([], _, _, []).
substitute_tokens([t('#', Loc, Space, Hide), t(P, _, _, _)|Ts], Bindings, _,
                  [t(Str, Loc, Space, Hide)|Rs]) :-
    memberchk(bind(P, Raw, _), Bindings), !,
    stringify(Raw, Str),
    substitute_tokens(Ts, Bindings, no, Rs).
substitute_tokens([t(P, Loc, Space, Hide)|Ts], Bindings, AfterPaste, Rs) :-
    (   memberchk(bind(P, Raw, Env), Bindings)
    ->  (   ( AfterPaste == yes ; Ts = [t('##', _, _, _)|_] )
        ->  Use = Raw
        ;   expand(Raw, Env, Use)
        ),
        (   Use = []
        ->  R = [t('', Loc, Space, Hide)]
        ;   set_first_space(Use, Space, R)
        )
    ;   R = [t(P, Loc, Space, Hide)]
    ),
    ( P == '##' -> Next = yes ; Next = no ),
    append(R, Tail, Rs),
    substitute_tokens(Ts, Bindings, Next, Tail).

stringify(Ts, A) :-
    phrase(stringify_chars(Ts, first), Cs),
    phrase(escape_string(Cs), Escaped),
    append(['"'|Escaped], ['"'], All),
    atom_chars(A, All).

stringify_chars([], _) --> [].
stringify_chars([t(A, _, Space, _)|Ts], Which) -->
    ( { Space == yes, Which \== first } -> [' '] ; [] ),
    { atom_chars(A, Cs) },
    seq(Cs),
    stringify_chars(Ts, next).

escape_string([]) --> [].
escape_string([C|Cs]) -->
    ( { memberchk(C, ['"', '\\']) } -> ['\\', C] ; [C] ),
    escape_string(Cs).

% paste(+Ts, -Rs, +Loc): apply ## and drop placemarkers. A pasted
% spelling must be exactly one preprocessing token.
paste([t(A, Loc, Space, Hide), t('##', _, _, _), t(B, _, _, Hide1)|Ts], Rs,
      MacroLoc) :- !,
    atom_concat(A, B, C),
    (   C == ''
    ->  true
    ;   atom_chars(C, Cs),
        phrase(spelling(Cs), Cs)
    ->  true
    ;   pp_error(MacroLoc, invalid_token_paste(A, B))
    ),
    hide_intersection(Hide, Hide1, Hide2),
    paste([t(C, Loc, Space, Hide2)|Ts], Rs, MacroLoc).
paste([t('', _, _, _)|Ts], Rs, Loc) :- !, paste(Ts, Rs, Loc).
paste([T|Ts], [T|Rs], Loc) :- paste(Ts, Rs, Loc).
paste([], [], _).

% Builtin operators are not macros in clang's -dM output. Feature answers
% are discovered once with the target profile, not guessed from __GNUC__.
builtin(t('__LINE__', Loc, Space, Hide), Ts, Ts, _, [t(A, Loc, Space, Hide)]) :-
    Loc = _:Line,
    atom_number(A, Line).
builtin(t('__FILE__', Loc, Space, Hide), Ts, Ts, _, [t(A, Loc, Space, Hide)]) :-
    Loc = File:_,
    stringify([t(File, Loc, no, [])], A).
builtin(t(Op, Loc, Space, Hide), [t('(', _, _, _)|Ts], Rest, Env,
        [t(A, Loc, Space, Hide)]) :-
    memberchk(Op, ['__has_include', '__has_include_next']),
    macro_arguments(Ts, 0, [], [], [Arg], Rest, _),
    header_operand(Arg, Env, Name, Form),
    Env = env(_, Paths, _, _, File),
    search_paths(Op, File, Paths, Search),
    ( include_path(Name, Form, File, Search, _) -> A = '1' ; A = '0' ).
builtin(t(Op, Loc, Space, Hide),
        [t('(', _, _, _), t(Name, _, _, _), t(')', _, _, _)|Ts], Ts,
        env(_, _, Features, _, _), [t(A, Loc, Space, Hide)]) :-
    feature_operator(Op),
    feature_value(Features, Op, Name, A).

feature_operator('__has_attribute').
feature_operator('__has_builtin').
feature_operator('__has_extension').
feature_operator('__has_feature').
feature_operator('__has_c_attribute').
feature_operator('__building_module').

is_defined(A, env(Macros, _, _, _, _)) :- get_assoc(A, Macros, _), !.
is_defined('__has_include', _).
is_defined('__has_include_next', _).
is_defined('__LINE__', _).
is_defined('__FILE__', _).
is_defined(A, _) :- feature_operator(A).

%% Conditions

% condition(+Kind, +Args, +Env, -Value) for #if, #ifdef and #ifndef.
condition(ifdef, [t(A, _, _, _)], Env, V) :-
    ( is_defined(A, Env) -> V = 1 ; V = 0 ).
condition(ifndef, Args, Env, V) :-
    condition(ifdef, Args, Env, Defined),
    V is 1 - Defined.
condition(if, Args, Env, V) :-
    defined_tokens(Args, Env, Replaced),
    expand(Replaced, Env, Expanded),
    maplist(expr_token, Expanded, ExprTokens),
    (   phrase(expression(Tree), ExprTokens)
    ->  eval(Tree, V)
    ;   pp_error('<condition>':0, bad_if_expression(ExprTokens))
    ).

% defined X and defined(X) become 1 or 0 before macro expansion.
defined_tokens([], _, []).
defined_tokens([t(defined, Loc, Space, Hide), t('(', _, _, _), t(A, _, _, _),
                t(')', _, _, _)|Ts], Env, [t(V, Loc, Space, Hide)|Rs]) :- !,
    ( is_defined(A, Env) -> V = '1' ; V = '0' ),
    defined_tokens(Ts, Env, Rs).
defined_tokens([t(defined, Loc, Space, Hide), t(A, _, _, _)|Ts], Env,
               [t(V, Loc, Space, Hide)|Rs]) :- !,
    ( is_defined(A, Env) -> V = '1' ; V = '0' ),
    defined_tokens(Ts, Env, Rs).
defined_tokens([T|Ts], Env, [T|Rs]) :- defined_tokens(Ts, Env, Rs).

% expr_token(+PpToken, -T): num(N) for a character constant or an
% identifier left after expansion (which is 0), num(N, Suffix) for an
% integer, and the spelling for anything else.
expr_token(t(A, _, _, _), T) :-
    atom_chars(A, Cs),
    (   Cs = [P, '\''|Rest], memberchk(P, ['L', u, 'U'])
    ->  c_tokens(['\''|Rest], '<condition>', [tok(chr(N), _)]),
        T = num(N)
    ;   Cs = [C|_], ident_start(C)
    ->  T = num(0)
    ;   c_tokens(Cs, '<condition>', Lexed),
        (   Lexed = [tok(int(N, Suffix-_), _)] -> T = num(N, Suffix)
        ;   Lexed = [tok(chr(N), _)] -> T = num(N)
        ;   T = A
        )
    ).

% Pratt-style precedence DCG builds an expression before evaluating it:
% inactive &&/||/?: arms must not divide by zero.
expression(T) --> binary(1, A), conditional_rest(A, T).

conditional_rest(C, T) -->
    ['?'], !,
    expression(A),
    [':'],
    expression(B),
    { T = tern(C, A, B) }.
conditional_rest(T, T) --> [].

binary(Min, T) --> unary(A), binary_rest(Min, A, T).

binary_rest(Min, A, T) -->
    [Op], { precedence(Op, P), P >= Min }, !,
    { Next is P + 1 },
    binary(Next, B),
    binary_rest(Min, bin(Op, A, B), T).
binary_rest(_, T, T) --> [].

unary(un(Op, A)) --> [Op], { memberchk(Op, ['+', '-', '!', '~']) }, !, unary(A).
unary(A) --> ['('], !, expression(A), [')'].
unary(num(N)) --> [num(N)].
unary(num(N, S)) --> [num(N, S)].

precedence('||', 1).
precedence('&&', 2).
precedence('|', 3).
precedence('^', 4).
precedence('&', 5).
precedence('==', 6).
precedence('!=', 6).
precedence('<', 7).
precedence('>', 7).
precedence('<=', 7).
precedence('>=', 7).
precedence('<<', 8).
precedence('>>', 8).
precedence('+', 9).
precedence('-', 9).
precedence('*', 10).
precedence('/', 10).
precedence('%', 10).

% Preprocessor arithmetic uses intmax_t/uintmax_t (64 bits at this pin),
% not the host Prolog's unbounded integers or floating-point division.
eval(num(N), N).
eval(num(N, _), N).
eval(un(Op, A), V) :-
    eval(A, X),
    unary_value(Op, X, R),
    expr_unsigned(un(Op, A), U),
    wrap(R, U, V).
eval(tern(C, A, B), V) :-
    eval(C, X),
    ( X =\= 0 -> eval(A, R) ; eval(B, R) ),
    expr_unsigned(tern(C, A, B), U),
    wrap(R, U, V).
eval(bin('&&', A, B), V) :- !,
    eval(A, X),
    ( X =:= 0 -> V = 0 ; eval(B, Y), boolean(Y, V) ).
eval(bin('||', A, B), V) :- !,
    eval(A, X),
    ( X =\= 0 -> V = 1 ; eval(B, Y), boolean(Y, V) ).
eval(bin(Op, A, B), V) :-
    eval(A, X0),
    eval(B, Y0),
    (   memberchk(Op, ['<<', '>>'])
    ->  X = X0,
        Y = Y0
    ;   usual_unsigned(A, B, U),
        wrap(X0, U, X),
        wrap(Y0, U, Y)
    ),
    binary_value(Op, X, Y, R),
    expr_unsigned(bin(Op, A, B), ResultU),
    wrap(R, ResultU, V).

% expr_unsigned(+Tree, -U): U is yes if Tree has type uintmax_t.
expr_unsigned(num(_), no).
expr_unsigned(num(N, S), U) :-
    (   ( memberchk(S, [u, ul, ull]) ; N > 9223372036854775807 )
    ->  U = yes
    ;   U = no
    ).
expr_unsigned(un('!', _), no) :- !.
expr_unsigned(un(_, A), U) :- expr_unsigned(A, U).
expr_unsigned(tern(_, A, B), U) :- usual_unsigned(A, B, U).
expr_unsigned(bin(Op, A, B), U) :-
    (   memberchk(Op, ['<', '>', '<=', '>=', '==', '!=', '&&', '||'])
    ->  U = no
    ;   memberchk(Op, ['<<', '>>'])
    ->  expr_unsigned(A, U)
    ;   usual_unsigned(A, B, U)
    ).

usual_unsigned(A, B, U) :-
    expr_unsigned(A, UA),
    expr_unsigned(B, UB),
    ( ( UA == yes ; UB == yes ) -> U = yes ; U = no ).

% wrap(+N, +Unsigned, -V): N reduced to 64 bits, signed unless Unsigned.
wrap(N, U, V) :-
    Bits is N mod 18446744073709551616,
    (   U == no, Bits >= 9223372036854775808
    ->  V is Bits - 18446744073709551616
    ;   V = Bits
    ).

boolean(X, 1) :- X =\= 0, !.
boolean(_, 0).

unary_value('+', X, X).
unary_value('-', X, V) :- V is -X.
unary_value('~', X, V) :- V is \X.
unary_value('!', X, V) :- ( X =:= 0 -> V = 1 ; V = 0 ).

binary_value('+', X, Y, V) :- V is X+Y.
binary_value('-', X, Y, V) :- V is X-Y.
binary_value('*', X, Y, V) :- V is X*Y.
binary_value('/', X, Y, V) :- V is X//Y.
binary_value('%', X, Y, V) :- V is X rem Y.
binary_value('<<', X, Y, V) :- V is X<<Y.
binary_value('>>', X, Y, V) :- V is X>>Y.
binary_value('&', X, Y, V) :- V is X /\ Y.
binary_value('|', X, Y, V) :- V is X \/ Y.
binary_value('^', X, Y, V) :- V is xor(X, Y).
binary_value('<', X, Y, V) :- ( X < Y -> V = 1 ; V = 0 ).
binary_value('>', X, Y, V) :- ( X > Y -> V = 1 ; V = 0 ).
binary_value('<=', X, Y, V) :- ( X =< Y -> V = 1 ; V = 0 ).
binary_value('>=', X, Y, V) :- ( X >= Y -> V = 1 ; V = 0 ).
binary_value('==', X, Y, V) :- ( X =:= Y -> V = 1 ; V = 0 ).
binary_value('!=', X, Y, V) :- ( X =\= Y -> V = 1 ; V = 0 ).

pp_error(Loc, Why) :-
    format(atom(Msg), '~w: ~w', [Loc, Why]),
    throw(nanofil_error(Msg)).

%% Target profile

% Impure adapter: discover the selected target, never preprocess the input.
% This avoids embedding Nix store paths or a second, stale copy of the pin's
% 400+ predefined macros. Pipes are drained before waiting for the child.
pp_profile(Clang, profile(Macros, Paths, Features)) :-
    clang_output(Clang, ['-dM', '-E', '-x', c, '/dev/null'], Defs),
    source_tokens(Defs, '<built-in>':1, PpTokens),
    token_lines(PpTokens, Lines),
    empty_assoc(Macros0),
    foldl(profile_define, Lines, Macros0, Macros),
    process_create(Clang, ['-E', '-v', '-x', c, '/dev/null'],
                   [stdout(null), stderr(pipe(Err)), process(Pid)]),
    read_chars(Err, Verbose),
    close(Err),
    process_wait(Pid, exit(0)),
    phrase(text_lines(VerboseLines), Verbose),
    include_directories(VerboseLines, Paths),
    feature_profile(Clang, Features).

profile_define([t('#', _, _, _), t(define, _, _, _)|Ts], Macros0, Macros) :- !,
    define(Ts, Macros0, Macros).
profile_define(_, Macros, Macros).

clang_output(Command, Args, Cs) :-
    process_create(Command, Args, [stdout(pipe(Out)), process(Pid)]),
    read_chars(Out, Cs),
    close(Out),
    process_wait(Pid, exit(0)).

read_chars(Stream, Cs) :-
    get_char(Stream, C),
    (   C == end_of_file
    ->  Cs = []
    ;   Cs = [C|Rest],
        read_chars(Stream, Rest)
    ).

text_lines([Line|Lines]) --> text_line(Line), !, text_lines(Lines).
text_lines([]) --> [].

% A line needs at least a newline or one character.
text_line([]) --> ['\n'], !.
text_line([C|Cs]) --> [C], !, text_rest(Cs).

text_rest([]) --> ['\n'], !.
text_rest([C|Cs]) --> [C], !, text_rest(Cs).
text_rest([]) --> [].

include_directories([Line|Lines], Paths) :-
    (   Line = "#include <...> search starts here:"
    ->  path_lines(Lines, Paths)
    ;   include_directories(Lines, Paths)
    ).

path_lines([[' '|Cs]|Lines], [Path|Paths]) :- !,
    atom_chars(Path, Cs),
    path_lines(Lines, Paths).
path_lines(_, []).

% Batch the feature names used by glibc. The adapter uses a shell pipeline
% because this Trealla revision leaves the child's own stdin writer open
% with stdin(pipe(...)); closing the parent stream cannot deliver EOF.
feature_names('__has_attribute',
              ['__nothrow__', '__cold__', '__malloc__', '__alloc_align__',
               '__pure__', '__const__', '__unused__', '__used__',
               '__deprecated__', '__format_arg__', '__format__',
               '__nonnull__', '__returns_nonnull__', '__warn_unused_result__',
               '__always_inline__', '__artificial__', '__indirect_return__']).
feature_names('__has_builtin',
              ['__builtin_expect', '__builtin_FILE', '__builtin_fclose']).
feature_names('__has_extension',
              ['__attribute_deprecated_with_message__', c_generic_selections]).
feature_names('__has_feature', [modules]).
feature_names('__has_c_attribute', []).
feature_names('__building_module', ['_Builtin_stddef']).

feature_profile(Clang, features(Clang, Answers)) :-
    findall(Op-Name, ( feature_names(Op, Names), member(Name, Names) ), Pairs),
    query_features(Clang, Pairs, Answers).

% This is target introspection only: pass an operator and a single name,
% never a source expression, file, declaration or include to clang.
feature_value(features(Clang, Answers), Op, Name, A) :-
    (   memberchk(answer(Op, Name, A), Answers)
    ->  true
    ;   atom_chars(Name, [C|Cs]),
        ident_start(C),
        maplist(ident_char, Cs),
        query_features(Clang, [Op-Name], [answer(Op, Name, A)])
    ).

query_features(Clang, Pairs, Answers) :-
    findall(Quoted,
            (   member(Op-Name, Pairs),
                format(atom(Query), '~w(~w)', [Op, Name]),
                shell_quote(Query, Quoted)
            ),
            Queries),
    atomic_list_concat(Queries, ' ', Args),
    shell_quote(Clang, ClangQuoted),
    format(atom(Cmd), "printf '%s\\n' ~w | ~w -E -P -x c -",
           [Args, ClangQuoted]),
    clang_output('/bin/sh', ['-c', Cmd], Cs),
    source_tokens(Cs, '<features>':1, PpTokens),
    exclude(=(nl), PpTokens, Values),
    maplist(feature_answer, Pairs, Values, Answers).

feature_answer(Op-Name, t(A, _, _, _), answer(Op, Name, A)).

shell_quote(A, Quoted) :-
    atom_chars(A, Cs),
    phrase(shell_chars(Cs), Escaped),
    append(['\''|Escaped], ['\''], All),
    atom_chars(Quoted, All).

shell_chars([]) --> [].
shell_chars(['\''|Cs]) --> "'\\''", !, shell_chars(Cs).
shell_chars([C|Cs]) --> [C], shell_chars(Cs).
