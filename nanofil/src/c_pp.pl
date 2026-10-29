/*  The C preprocessor (milestone 4e): it expands a C file's macros,
    includes and conditionals and hands the result to c_lex as tokens.

    ## Preprocessing tokens

    A preprocessing token is `t(Spelling, File:Line, Space, Hide)`:

    | Part | Is |
    |---|---|
    | Spelling | the token's text, as an atom |
    | `File:Line` | its location |
    | Space | `yes` if whitespace precedes the token, else `no`; `#` and `#define` need it |
    | Hide | the hide set: the sorted macro names that must not expand this token again |

    A newline is the token `nl` until the input is split into lines.

    ## The environment

    The environment is `env(Macros, IncludeDirs, Features, Once, File)`:

    | Part | Is |
    |---|---|
    | Macros | an assoc from macro names to `obj(Body)` or `fun(Params, Body)`, and from `saved(Name)` to the `#pragma push_macro` stack of Name |
    | IncludeDirs | the include search path |
    | Features | the target's answers to feature operators |
    | Once | the files seen by `#pragma once` |
    | File | the file whose directives are being processed |

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
:- use_module(c_parse, [c_constant_expression/2]).
:- use_module(c_types, [pp_value/2]).

%! pp_file(+File, +Profile, -Tokens)
%
%  Tokens are the c_lex tokens of File after preprocessing, each at the
%  location of the preprocessing token it came from. Profile is
%  profile(Macros, IncludeDirs, FeatureAnswers) from pp_profile/2.
%  Throws nanofil_error/1 on a preprocessing or lexical error.
pp_file(File, profile(Macros, Paths, Features), Tokens) :-
    retractall(source_cache(_, _)),
    % once/1: a choicepoint left in expansion would keep the file's
    % preprocessing tokens alive through lexing (33 MB of 77 MB live at
    % the end for a 256 KB GLib resource blob).
    once(file_tokens(File, env(Macros, Paths, Features, [], File), _, PpTokens)),
    phrase(lex_tokens(PpTokens), Tokens).

% lex_tokens(+PpTokens)//: the c_lex tokens of PpTokens. Each
% preprocessing token is lexed on its own and keeps its location.
lex_tokens([]) --> [].
lex_tokens([t(pragma_weak(N, T), Loc, _, _)|PpTokens]) --> !,
    [tok(pragma_weak(N, T), Loc)],
    lex_tokens(PpTokens).
lex_tokens([t(A, Loc, _, _)|PpTokens]) -->
    {   atom_chars(A, Cs),
        c_tokens(Cs, '<preprocessing token>', Lexed),
        maplist(token_relocated(Loc), Lexed, Tokens)
    },
    seq(Tokens),
    lex_tokens(PpTokens).

token_relocated(Loc, tok(T, _), tok(T, Loc)).

% file_tokens(+File, +Env0, -Env, -Tokens): File's expanded tokens. Env
% carries the macros and the #pragma once set back to the includer.
file_tokens(File, Env0, Env, Tokens) :-
    Env0 = env(Macros0, Paths, Features, Once0, Includer),
    absolute_file_name(File, Identity),
    (   memberchk(Identity, Once0)
    ->  Env = Env0,
        Tokens = []
    ;   read_source(File, PpTokens),
        token_lines(PpTokens, Lines),
        lines_tokens(Lines, File, [], [],
                      env(Macros0, Paths, Features, Once0, File), End,
                      Tokens, []),
        End = env(Macros, Paths, Features, Once, _),
        Env = env(Macros, Paths, Features, Once, Includer)
    ).

% read_source(+File, -PpTokens): PpTokens are File's preprocessing
% tokens, before line splitting. Impure file adapter. Keep the input
% buffer local so it can be reclaimed before processing nested includes;
% the macro environment stays explicit. A file's tokens do not depend on
% the macros, so each file is read once per pp_file/3: headers are
% included again and again (lvm.c reads 124 files 272 times), and
% reading was most of the preprocessor's time.
read_source(File, PpTokens) :-
    (   source_cache(File, PpTokens0)
    ->  PpTokens = PpTokens0
    ;   once(phrase_from_file(seq(Cs), File, [type(binary)])),
        once(source_tokens(Cs, File:1, PpTokens)),
        assertz(source_cache(File, PpTokens))
    ).

% source_cache(?File, ?PpTokens): read_source/2's tokens of File, for
% the pp_file/3 call in progress.
:- dynamic(source_cache/2).

%% Translation phases 2 and 3

% source_tokens(+Chars, +Loc, -PpTokens): PpTokens are the preprocessing
% tokens of Chars, which start at Loc.
% A comment is one whitespace character, even across physical newlines.
% A parallel location vector survives splicing even inside identifiers and
% literals. In particular __LINE__ after a continuation is the physical
% source line, not the number of newlines in the spliced buffer.
source_tokens(Cs, Loc, PpTokens) :-
    (   has_splice(Cs)
    ->  located_splice(Cs, Loc, Spliced, Locs),
        At = locs(Locs)
    ;   % Without a splice the characters are their own spliced copy and
        % a token's line is the newlines before it: two lists fewer of
        % the file's length (GLib's resource blobs are 10 MB of octal
        % constants).
        Spliced = Cs, At = line(Loc)
    ),
    phrase(pp_tokens(PpTokens, At, yes), Spliced).

has_splice(['\\'|Cs]) :- ( Cs = ['\n'|_] ; Cs = ['\r', '\n'|_] ), !.
has_splice([_|Cs]) :- has_splice(Cs).

% at_loc(+At, -Loc), at_skip(+Char, +At0, -At): the location of the
% next character, and the state after Char. At is locs(Locs), the
% locations of the remaining characters (located_splice/4), or line(Loc)
% when the input has no splice, Loc shared by the characters of a line.
at_loc(locs([Loc|_]), Loc).
at_loc(line(Loc), Loc).

at_skip(_, locs([_|Locs]), locs(Locs)).
at_skip(C, line(Loc), At) :-
    (   C == '\n'
    ->  Loc = File:N, N1 is N + 1, At = line(File:N1)
    ;   At = line(Loc)
    ).

at_skips([], At, At).
at_skips([C|Cs], At0, At) :- at_skip(C, At0, At1), at_skips(Cs, At1, At).

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

% pp_tokens(PpTokens, At, Space): At is the location state of the
% input (at_loc/2); Space says whether whitespace precedes the next
% token.
pp_tokens([nl|Ts], At0, _) -->
    ['\n'], !,
    { at_skip('\n', At0, At) },
    pp_tokens(Ts, At, yes).
pp_tokens(Ts, At0, _) -->
    [C], { space(C) }, !,
    { at_skip(C, At0, At) },
    pp_tokens(Ts, At, yes).
pp_tokens(Ts, At0, _) -->
    ['/', '/'], !,
    { at_skips(['/', '/'], At0, At1) },
    line_comment(At1, At),
    pp_tokens(Ts, At, yes).
pp_tokens(Ts, At0, _) -->
    ['/', '*'], !,
    { at_skips(['/', '*'], At0, At1) },
    block_comment(At1, At),
    pp_tokens(Ts, At, yes).
pp_tokens([t(A, Loc, Space, [])|Ts], At0, Space) -->
    spelling(Cs), !,
    {   at_loc(At0, Loc),
        atom_chars(A, Cs),
        at_skips(Cs, At0, At)
    },
    pp_tokens(Ts, At, no).
pp_tokens([], _, _) --> [].

space(' ').
space('\t').
space('\r').
space('\f').
space('\v').

% line_comment(+At0, -At)//: the comment's characters, leaving the
% newline; At is At0 past them.
line_comment(At, At), ['\n'] --> ['\n'], !.
line_comment(At0, At) -->
    [C], !,
    { at_skip(C, At0, At1) },
    line_comment(At1, At).
line_comment(At, At) --> [].

% block_comment(+At0, -At)//: like line_comment//2, through the */.
block_comment(At0, At) --> ['*', '/'], !, { at_skips(['*', '/'], At0, At) }.
block_comment(At0, At) -->
    [C], !,
    { at_skip(C, At0, At1) },
    block_comment(At1, At).
block_comment(_, _) -->
    { throw(nanofil_error('unterminated preprocessing comment')) }.

% spelling(-Chars)//: Chars is the spelling of one preprocessing token,
% the longest that matches.
spelling([u, '8', '"'|Cs]) -->              % C11 6.4.5: u8"..."
    [u, '8', '"'], !,
    quoted('"', Cs).
spelling([P, Q|Cs]) -->
    [P, Q], { memberchk(P, ['L', u, 'U']), memberchk(Q, ['"', '\'']) }, !,
    quoted(Q, Cs).
spelling([Q|Cs]) -->
    [Q], { memberchk(Q, ['"', '\'']) }, !,
    quoted(Q, Cs).
spelling([C|Cs]) -->
    [C], { ident_start(C) }, !,
    ident_rest(Cs).
spelling([C|Cs]) -->
    [C], { decimal(C) }, !,
    number_rest(Cs).
spelling(['.', C|Cs]) -->
    ['.', C], { decimal(C) }, !,
    number_rest(Cs).
spelling(Cs) -->
    [A, B, C],
    { Cs = [A, B, C], atom_chars(P, Cs), punctuator(P) }, !.
spelling(Cs) -->
    [A, B],
    { Cs = [A, B], atom_chars(P, Cs), ( punctuator(P) ; digraph(P) ) }, !.
spelling([C]) --> [C].

% quoted(+Quote, -Chars)//: Chars is the rest of a literal through its
% closing Quote, escapes kept as written.
quoted(Q, ['\\', C|Cs]) -->
    ['\\', C], !,
    quoted(Q, Cs).
quoted(Q, [Q]) --> [Q], !.
quoted(Q, [C|Cs]) -->
    [C], { C \== '\n' }, !,
    quoted(Q, Cs).
quoted(_, _) -->
    { throw(nanofil_error('unterminated preprocessing literal')) }.

number_rest([E, S|Cs]) -->
    [E, S],
    { memberchk(E, [e, 'E', p, 'P']), memberchk(S, ['+', '-']) }, !,
    number_rest(Cs).
number_rest([C|Cs]) -->
    [C], { ident_char(C) ; C == '.' }, !,
    number_rest(Cs).
number_rest([]) --> [].

%% Lines and directives

% token_lines(+PpTokens, -Lines): Lines are PpTokens split at each nl,
% the nl tokens dropped.
token_lines([], []).
token_lines([T|Ts], [Line|Lines]) :-
    tokens_line_rest([T|Ts], Line, Rest),
    token_lines(Rest, Lines).

% tokens_line_rest(+PpTokens, -Line, -Rest): Line is PpTokens up to the
% first nl, and Rest follows it.
tokens_line_rest([], [], []).
tokens_line_rest([T|Ts], Line, Rest) :- token_line_rest(T, Ts, Line, Rest).

% token_line_rest(+T, +Ts, -Line, -Rest): like tokens_line_rest/3 for
% [T|Ts]; T is nl or a t/4 token.
token_line_rest(nl, Ts, [], Ts).
token_line_rest(t(A, Loc, Space, Hide), Ts, [t(A, Loc, Space, Hide)|Line],
                Rest) :-
    tokens_line_rest(Ts, Line, Rest).

% lines_tokens(+Lines, +File, +Stack, +Pending, +Env0, -Env, -Ts, ?End):
% Ordinary lines are collected in Pending (reversed) and expanded
% together, so a function invocation can span newlines. Directives are
% barriers; inactive groups never expand tokens.
lines_tokens([], File, Stack, Pending, Env, Env, Ts, End) :-
    ( Stack = [] -> true ; pp_error(File:1, 'unterminated #if') ),
    pending_expansion(Pending, Env, Expanded),
    append(Expanded, End, Ts).
lines_tokens([[t('#', HashLoc, _, _)|Directive]|Lines], File, Stack,
              Pending, Env0, Env, Ts, End) :-
    !,
    pending_expansion(Pending, Env0, Expanded),
    append(Expanded, Rest, Ts),
    (   Directive = [t(line, _, _, _)|Args], active(Stack)
    ->  tokens_expansion(Args, Env0, Marker),
        line_target(Marker, HashLoc, Target),
        lines_remapped(Lines, HashLoc, Target, More),
        Stack1 = Stack,
        Env1 = Env0,
        Rest = Next
    ;   directive(Directive, File, Stack, Stack1, Env0, Env1, Rest, Next),
        More = Lines
    ),
    lines_tokens(More, File, Stack1, [], Env1, Env, Next, End).
lines_tokens([Line|Lines], File, Stack, Pending, Env0, Env, Ts, End) :-
    (   active(Stack)
    ->  lines_tokens(Lines, File, Stack, [Line|Pending], Env0, Env, Ts, End)
    ;   lines_tokens(Lines, File, Stack, Pending, Env0, Env, Ts, End)
    ).

% line_target(+Marker, +HashLoc, -Target): for #line N ["file"] at
% HashLoc, the line after the directive is line N (of file), Target.
line_target([t(A, _, _, _)|Ts], File:_, NewFile:N) :-
    atom_number(A, N),
    integer(N),
    N > 0,
    marker_file(Ts, File, NewFile).

% marker_file(+Tokens, +File0, -File): File is named by the optional
% "file" operand Tokens of #line, else File0.
marker_file([], File, File).
marker_file([T|Ts], _, File) :- include_name([T|Ts], File, quote).

% lines_remapped(+Lines, +Old, +New, -Remapped): the tokens of Lines, which
% follow the directive at Old, renumbered so that the first is at New.
lines_remapped([], _, _, []).
lines_remapped([Ts|Lines], Old, New, [Rs|Rest]) :-
    maplist(token_remapped(Old, New), Ts, Rs),
    lines_remapped(Lines, Old, New, Rest).

token_remapped(Old, New, t(A, Loc, Space, Hide), t(A, Loc1, Space, Hide)) :-
    location_remapped(Old, New, Loc, Loc1).

location_remapped(_:Old, File:New, _:N, File:M) :- M is N-Old-1+New.

% pending_expansion(+Pending, +Env, -Ts): Ts are the expanded tokens of the
% reversed list of lines Pending.
pending_expansion(Pending, Env, Ts) :-
    reverse(Pending, Lines),
    append(Lines, Flat),
    tokens_expansion(Flat, Env, Ts).

% The conditional stack has one cond(Taken, Seen, Parent) per open #if:
% Taken says whether the current group is active, Seen whether an earlier
% group was taken (yes, no, or else after #else), Parent whether the
% enclosing group is active.
active([]).
active([cond(yes, _, _)|_]).

% seen_after(+Taken, +Seen0, -Seen): Seen says whether a group was taken
% once the current one is decided.
seen_after(yes, _, yes).
seen_after(no, Seen, Seen).

% condition_truth(+Value, -Taken): Taken is yes if Value is nonzero.
condition_truth(V, yes) :- V =\= 0, !.
condition_truth(_, no).

% directive(+Tokens, +File, +Stack0, -Stack, +Env0, -Env, -Ts, ?Rest): one
% directive line after its '#'. Conditionals are tracked even in inactive
% groups; other directives only run in active ones. Ts is Rest with an
% included file's tokens in front.
directive([], _, Stack, Stack, Env, Env, Ts, Ts).
directive([t(Name, Loc, _, _)|Args], File, Stack0, Stack, Env0, Env,
          Ts, Rest) :-
    (   conditional_directive(Name)
    ->  conditional_stack(Name, Loc, Args, Env0, Stack0, Stack),
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

% conditional_stack(+Name, +Loc, +Args, +Env, +Stack0, -Stack): Stack is
% the conditional stack after the directive #Name Args.
conditional_stack(elif, Loc, Args, Env, Stack0,
                  [cond(Taken, Seen1, Parent)|Tail]) :-
    (   Stack0 = [cond(_, Seen, Parent)|Tail], Seen \== else
    ->  true
    ;   pp_error(Loc, 'unexpected #elif')
    ),
    elif_taken(Parent, Seen, Args, Env, Taken),
    seen_after(Taken, Seen, Seen1).
conditional_stack(else, Loc, _, _, Stack0, [cond(Taken, else, Parent)|Tail]) :-
    (   Stack0 = [cond(_, Seen, Parent)|Tail], Seen \== else
    ->  true
    ;   pp_error(Loc, 'unexpected #else')
    ),
    else_taken(Seen, Parent, Taken).
conditional_stack(endif, Loc, _, _, Stack0, Stack) :-
    (   Stack0 = [_|Stack]
    ->  true
    ;   pp_error(Loc, 'unexpected #endif')
    ).
conditional_stack(if, _, Args, Env, Stack0, Stack) :-
    opened_stack(if, Args, Env, Stack0, Stack).
conditional_stack(ifdef, _, Args, Env, Stack0, Stack) :-
    opened_stack(ifdef, Args, Env, Stack0, Stack).
conditional_stack(ifndef, _, Args, Env, Stack0, Stack) :-
    opened_stack(ifndef, Args, Env, Stack0, Stack).

% opened_stack(+Kind, +Args, +Env, +Stack0, -Stack): Stack is Stack0 with
% the group that #Kind Args opens.
opened_stack(Kind, Args, Env, Stack0, [cond(Taken, Taken, Parent)|Stack0]) :-
    (   active(Stack0)
    ->  Parent = yes,
        condition(Kind, Args, Env, V),
        condition_truth(V, Taken)
    ;   Parent = no,
        Taken = no
    ).

% elif_taken(+Parent, +Seen, +Args, +Env, -Taken): Taken says whether the
% group of #elif Args is active.
elif_taken(no, _, _, _, no).
elif_taken(yes, Seen, Args, Env, Taken) :- elif_open(Seen, Args, Env, Taken).

% elif_open(+Seen, +Args, +Env, -Taken): in an active parent, #elif Args
% is taken if no earlier group was and its condition holds.
elif_open(no, Args, Env, Taken) :-
    condition(if, Args, Env, V),
    condition_truth(V, Taken).
elif_open(yes, _, _, no).

% else_taken(+Seen, +Parent, -Taken): #else is taken if no earlier group
% was and the parent is active.
else_taken(no, Parent, Parent).
else_taken(yes, _, no).

% active_directive(+Name, +Loc, +Args, +File, +Env0, -Env, -Ts, ?Rest):
% run #Name Args in an active group; Ts is Rest with an included file's
% tokens in front. Name is any identifier in the source, so the last
% clause is a real default case: the cuts commit to a known directive.
active_directive(define, _, Args, _, Env0, Env, Ts, Ts) :- !,
    Env0 = env(Macros0, Paths, Features, Once, File),
    definition_macros(Args, Macros0, Macros),
    Env = env(Macros, Paths, Features, Once, File).
active_directive(undef, _, Args, _, Env0, Env, Ts, Ts) :- !,
    Args = [t(Name, _, _, _)],
    Env0 = env(Macros0, Paths, Features, Once, File),
    macro_removed(Name, Macros0, Macros),
    Env = env(Macros, Paths, Features, Once, File).
active_directive(Kind, Loc, Args, File, Env0, Env, Ts, Rest) :-
    memberchk(Kind, [include, include_next]),
    !,
    Env0 = env(_, Paths, _, _, _),
    header_operand(Args, Env0, Name, Form),
    search_paths(Kind, File, Paths, Search),
    (   include_path(Name, Form, File, Search, Path)
    ->  true
    ;   pp_error(Loc, include_not_found(Name))
    ),
    file_tokens(Path, Env0, Env, Included),
    append(Included, Rest, Ts).
active_directive(pragma, Loc, Args, _, Env, Env, [t(pragma_weak(Name, Target), Loc, yes, [])|Ts], Ts) :-
    pragma_weak(Args, Name, Target), !.
active_directive(pragma, _, Args, File, Env0, Env, Ts, Ts) :- !,
    pragma(Args, File, Env0, Env).
active_directive(error, Loc, Args, _, _, _, _, _) :- !,
    pp_error(Loc, error_directive(Args)).
active_directive(ident, _, _, _, Env, Env, Ts, Ts) :- !.
active_directive(Name, Loc, _, _, _, _, _, _) :-
    pp_error(Loc, unsupported_directive(Name)).

% #pragma weak Name [= Target] is the c_lex token pragma_weak(Name, Target).
pragma_weak([t(weak, _, _, _), t(Name, _, _, _)|Rest], Name, Target) :-
    atom_chars(Name, [C|_]), ident_start(C),
    (   Rest == [] -> Target = none
    ;   Rest = [t('=', _, _, _), t(Target, _, _, _)], atom_chars(Target, [D|_]), ident_start(D)
    ).

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
    include_name([Str], Name, quote),
    !,
    macro_stack_op(Op, Name, Macros0, Macros).
pragma(_, _, Env, Env).

% macro_stack_op(+Op, +Name, +Macros0, -Macros): Macros is Macros0 after
% #pragma Op("Name"). A saved entry is some(Def) or none (undefined); a
% pop with nothing saved changes nothing.
macro_stack_op(push_macro, Name, Macros0, Macros) :-
    ( get_assoc(Name, Macros0, Def) -> Saved = some(Def) ; Saved = none ),
    ( get_assoc(saved(Name), Macros0, Stack) -> true ; Stack = [] ),
    put_assoc(saved(Name), Macros0, [Saved|Stack], Macros).
macro_stack_op(pop_macro, Name, Macros0, Macros) :-
    (   get_assoc(saved(Name), Macros0, [Saved|Stack])
    ->  put_assoc(saved(Name), Macros0, Stack, Macros1),
        restored_macro(Saved, Name, Macros1, Macros)
    ;   Macros = Macros0
    ).

% restored_macro(+Saved, +Name, +Macros0, -Macros): Macros is Macros0
% with Name as #pragma push_macro saved it, some(Def) or none.
restored_macro(some(Def), Name, Macros0, Macros) :-
    put_assoc(Name, Macros0, Def, Macros).
restored_macro(none, Name, Macros0, Macros) :-
    macro_removed(Name, Macros0, Macros).

% macro_removed(+Name, +Macros0, -Macros): Macros is Macros0 without
% Name, which need not be defined.
macro_removed(Name, Macros0, Macros) :-
    (   del_assoc(Name, Macros0, _, Macros1)
    ->  Macros = Macros1
    ;   Macros = Macros0
    ).

% definition_macros(+Tokens, +Macros0, -Macros): Macros is Macros0 with the
% definition Tokens of #define. A macro is function-like if '(' follows
% its name without a space.
definition_macros([t(Name, _, _, _)|Ts], Macros0, Macros) :-
    (   Ts = [t('(', _, no, _)|Rest]
    ->  macro_params(Rest, Params, Body),
        Def = fun(Params, Body)
    ;   Def = obj(Ts)
    ),
    put_assoc(Name, Macros0, Def, Macros).

% macro_params(+Ts, -Params, -Body): named(Name) for each name up to
% ')'; a final ... (or P...) is variadic(Name).
macro_params([t(')', _, _, _)|Ts], [], Ts) :- !.
macro_params([t('...', _, _, _), t(')', _, _, _)|Ts],
             [variadic('__VA_ARGS__')], Ts) :- !.
macro_params([t(P, _, _, _), t('...', _, _, _), t(')', _, _, _)|Ts],
             [variadic(P)], Ts) :- !.
macro_params([t(P, _, _, _), t(',', _, _, _)|Ts], [named(P)|Ps], Body) :-
    !,
    macro_params(Ts, Ps, Body).
macro_params([t(P, _, _, _), t(')', _, _, _)|Ts], [named(P)], Ts).

%% Includes

% include_name(+Tokens, -Name, -Form): "name" (quote) or <name> (angle).
include_name([t(A, _, _, _)], Name, quote) :-
    atom_chars(A, ['"'|Cs]),
    append(Chars, ['"'], Cs),
    atom_chars(Name, Chars),
    !.
include_name([t('<', _, _, _)|Ts], Name, angle) :-
    append(Mid, [t('>', _, _, _)], Ts),
    maplist(token_spelling, Mid, As),
    atomic_list_concat(As, Name).

token_spelling(t(A, _, _, _), A).

% header_operand(+Tokens, +Env, -Name, -Form): the header name of an
% #include or __has_include operand. The operand is expanded only if it
% is not already a header name.
header_operand(Ts, Env, Name, Form) :-
    (   include_name(Ts, Name, Form)
    ->  true
    ;   tokens_expansion(Ts, Env, Expanded),
        include_name(Expanded, Name, Form)
    ).

% include_path(+Name, +Form, +File, +Dirs, -Path): Path is the first
% existing file for header Name included from File: an absolute Name,
% then (for quote) File's directory, then Dirs in order. Each cut
% commits to the first existing file, so at most one Path is found.
include_path(Name, _, _, _, Name) :-
    sub_atom(Name, 0, 1, _, '/'),
    exists_file(Name),
    !.
include_path(Name, quote, File, _, Path) :-
    file_directory(File, Dir),
    path_join(Dir, Name, Path),
    exists_file(Path),
    !.
include_path(Name, _, _, Dirs, Path) :-
    member(Dir, Dirs),
    path_join(Dir, Name, Path),
    exists_file(Path),
    !.

% file_directory(+File, -Dir): Dir is File up to its last '/', or '.'.
file_directory(File, Dir) :-
    atom_chars(File, Cs),
    reverse(Cs, Rev),
    append(_, ['/'|Tail], Rev),
    !,
    reverse(Tail, Ds),
    atom_chars(Dir, Ds).
file_directory(_, '.').

path_join(Dir, Name, Path) :- atomic_list_concat([Dir, '/', Name], Path).

% search_paths(+Kind, +File, +Dirs, -Search): #include_next and
% __has_include_next search the directories after the one File is in.
% Kinds include and __has_include also match the last clause, so a
% retry yields a second Search (the directories after File's, if any).
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
% tokens_expansion(+Ts, +Env, -Out): Out is Ts fully macro-expanded.
tokens_expansion([], _, []).
tokens_expansion([T|Ts], Env, Out) :-
    T = t(A, Loc, Space, Hide),
    Env = env(Macros, _, _, _, _),
    (   \+ memberchk(A, Hide),
        get_assoc(A, Macros, Def),
        replacement(Def, Ts, Rest, Env, Loc, Repl, EndHide)
    ->  invocation_hide(EndHide, Hide, BaseHide),
        maplist(replaced_token([A|BaseHide], Loc), Repl, Marked),
        first_spaced(Marked, Space, Replaced),
        append(Replaced, Rest, Next),
        tokens_expansion(Next, Env, Out)
    ;   builtin(T, Ts, Rest, Env, Repl)
    ->  append(Repl, Rest, Next),
        tokens_expansion(Next, Env, Out)
    ;   Out = [T|Out1],
        tokens_expansion(Ts, Env, Out1)
    ).

% invocation_hide(+EndHide, +Hide, -BaseHide): BaseHide is the hide set
% Hide of a macro name, intersected with that of a function-like
% invocation's ')' if EndHide is some(Set).
invocation_hide(none, Hide, Hide).
invocation_hide(some(EndHide), Hide, BaseHide) :-
    hide_intersection(Hide, EndHide, BaseHide).

% hide_intersection(+As, +Bs, -Cs): Cs are the elements of As in Bs.
hide_intersection([], _, []).
hide_intersection([A|As], Bs, Cs) :-
    ( memberchk(A, Bs) -> Cs = [A|Cs1] ; Cs = Cs1 ),
    hide_intersection(As, Bs, Cs1).

% A replacement token moves to the invocation and gains its hide set.
replaced_token(Hide, Loc, t(A, _, Space, Hide0), t(A, Loc, Space, Hide1)) :-
    append(Hide, Hide0, Hides),
    sort(Hides, Hide1).

first_spaced([], _, []).
first_spaced([t(A, Loc, _, Hide)|Ts], Space, [t(A, Loc, Space, Hide)|Ts]).

% replacement(+Def, +Ts, -Rest, +Env, +Loc, -Repl, -EndHide): EndHide is
% some(Set), Set the hide set of a function-like invocation's ')', or
% none for an object-like macro.
replacement(obj(Body), Ts, Ts, _, Loc, Repl, none) :- tokens_pasted(Body, Repl, Loc).
replacement(fun(Params, Body), [t('(', _, _, _)|Ts], Rest, Env, Loc, Repl,
            some(EndHide)) :-
    macro_arguments(Ts, 0, [], [], Args0, Rest, EndHide),
    ( Args0 = [[]], Params = [] -> Args = [] ; Args = Args0 ),
    params_bindings(Params, Args, Env, Bindings, Loc),
    body_substitution(Body, Bindings, Repl0),
    tokens_pasted(Repl0, Repl, Loc).

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

% params_bindings(+Params, +Args, +Env, -Bindings, +Loc): bind(P, Raw,
% Env) for each parameter; a variadic one takes the remaining arguments.
params_bindings([], Args, _, [], Loc) :- no_arguments(Args, Loc).
params_bindings([Param|Params], Args, Env, Bindings, Loc) :-
    param_bindings(Param, Params, Args, Env, Bindings, Loc).

% no_arguments(+Args, +Loc): Args is empty, as no parameters are left.
no_arguments([], _).
no_arguments([_|_], Loc) :- argument_count_error(Loc).

% param_bindings(+Param, +Params, +Args, +Env, -Bindings, +Loc): like
% params_bindings/5 for [Param|Params]. Only the last can be variadic.
param_bindings(variadic(P), [], Args, Env, [bind(P, Raw, Env)], _) :-
    args_joined(Args, Raw).
param_bindings(named(P), Params, Args, Env, Bindings, Loc) :-
    named_bindings(Args, P, Params, Env, Bindings, Loc).

named_bindings([], _, _, _, _, Loc) :- argument_count_error(Loc).
named_bindings([A|As], P, Params, Env, [bind(P, A, Env)|Bindings], Loc) :-
    params_bindings(Params, As, Env, Bindings, Loc).

argument_count_error(Loc) :- pp_error(Loc, 'wrong macro argument count').

% args_joined(+Args, -Ts): Ts are the token lists Args joined by commas.
args_joined([], []).
args_joined([A|As], Ts) :- args_joined(As, A, Ts).

% args_joined(+Args, +A, -Ts): Ts is A, then each of Args after a comma.
args_joined([], A, A).
args_joined([A|As], A0, Ts) :-
    args_joined(As, A, Rest),
    append(A0, [t(',', '<macro>':0, no, [])|Rest], Ts).

body_substitution(Ts, Bindings, Rs) :- body_substitution(Ts, Bindings, no, Rs).

% body_substitution(+Body, +Bindings, +AfterPaste, -Rs): AfterPaste is yes
% right after ##. # P stringifies the raw argument, an operand of ## is
% the raw argument, and any other use is the fully expanded argument; an
% empty argument becomes the placemarker ''.
body_substitution([], _, _, []).
body_substitution([t('#', Loc, Space, Hide), t(P, _, _, _)|Ts], Bindings, _,
                  [t(Str, Loc, Space, Hide)|Rs]) :-
    memberchk(bind(P, Raw, _), Bindings), !,
    tokens_string(Raw, Str),
    body_substitution(Ts, Bindings, no, Rs).
body_substitution([t(P, Loc, Space, Hide)|Ts], Bindings, AfterPaste, Rs) :-
    (   memberchk(bind(P, Raw, Env), Bindings)
    ->  (   ( AfterPaste == yes ; Ts = [t('##', _, _, _)|_] )
        ->  Use = Raw
        ;   tokens_expansion(Raw, Env, Use)
        ),
        (   Use = []
        ->  R = [t('', Loc, Space, Hide)]
        ;   first_spaced(Use, Space, R)
        )
    ;   R = [t(P, Loc, Space, Hide)]
    ),
    ( P == '##' -> Next = yes ; Next = no ),
    append(R, Tail, Rs),
    body_substitution(Ts, Bindings, Next, Tail).

% tokens_string(+Ts, -A): A is the string literal spelling of Ts, as #
% makes it.
tokens_string(Ts, A) :-
    phrase(tokens_text(Ts, first), Cs),
    phrase(escaped_chars(Cs), Escaped),
    append(['"'|Escaped], ['"'], All),
    atom_chars(A, All).

tokens_text([], _) --> [].
tokens_text([t(A, _, Space, _)|Ts], Which) -->
    ( { Space == yes, Which \== first } -> [' '] ; [] ),
    { atom_chars(A, Cs) },
    seq(Cs),
    tokens_text(Ts, next).

escaped_chars([]) --> [].
escaped_chars([C|Cs]) -->
    ( { memberchk(C, ['"', '\\']) } -> ['\\', C] ; [C] ),
    escaped_chars(Cs).

% tokens_pasted(+Ts, -Rs, +Loc): apply ## and drop placemarkers. A pasted
% spelling must be exactly one preprocessing token.
tokens_pasted([t(A, Loc, Space, Hide), t('##', _, _, _), t(B, _, _, Hide1)|Ts], Rs,
      MacroLoc) :-
    !,
    atom_concat(A, B, C),
    (   C == ''
    ->  true
    ;   atom_chars(C, Cs),
        phrase(spelling(Cs), Cs)
    ->  true
    ;   pp_error(MacroLoc, invalid_token_paste(A, B))
    ),
    hide_intersection(Hide, Hide1, Hide2),
    tokens_pasted([t(C, Loc, Space, Hide2)|Ts], Rs, MacroLoc).
tokens_pasted([t('', _, _, _)|Ts], Rs, Loc) :-
    !,
    tokens_pasted(Ts, Rs, Loc).
tokens_pasted([T|Ts], [T|Rs], Loc) :- tokens_pasted(Ts, Rs, Loc).
tokens_pasted([], [], _).

% builtin(+T, +Ts, -Rest, +Env, -Repl): T, applied to a prefix of Ts
% that leaves Rest, is a builtin operator replaced by Repl.
% Builtin operators are not macros in clang's -dM output. Feature answers
% are discovered once with the target profile, not guessed from __GNUC__.
builtin(t('__LINE__', Loc, Space, Hide), Ts, Ts, _, [t(A, Loc, Space, Hide)]) :-
    Loc = _:Line,
    atom_number(A, Line).
builtin(t('__FILE__', Loc, Space, Hide), Ts, Ts, _, [t(A, Loc, Space, Hide)]) :-
    Loc = File:_,
    tokens_string([t(File, Loc, no, [])], A).
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

% is_defined(+Name, +Env): Name is a macro or builtin operator, as
% defined and #ifdef see it.
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
    tokens_expansion(Replaced, Env, Expanded),
    maplist(expr_token, Expanded, Tokens),
    c_constant_expression(Tokens, Expr),
    (   pp_value(Expr, V) -> true
    ;   ( Tokens = [tok(_, Loc)|_] -> true ; Loc = '<condition>':0 ),
        pp_error(Loc, not_constant(Expr))
    ).

% defined X and defined(X) become 1 or 0 before macro expansion.
defined_tokens([], _, []).
defined_tokens([t(defined, Loc, Space, Hide), t('(', _, _, _), t(A, _, _, _),
                t(')', _, _, _)|Ts], Env, [t(V, Loc, Space, Hide)|Rs]) :-
    !,
    ( is_defined(A, Env) -> V = '1' ; V = '0' ),
    defined_tokens(Ts, Env, Rs).
defined_tokens([t(defined, Loc, Space, Hide), t(A, _, _, _)|Ts], Env,
               [t(V, Loc, Space, Hide)|Rs]) :-
    !,
    ( is_defined(A, Env) -> V = '1' ; V = '0' ),
    defined_tokens(Ts, Env, Rs).
defined_tokens([T|Ts], Env, [T|Rs]) :- defined_tokens(Ts, Env, Rs).

% expr_token(+PpToken, -Token): the c_lex token of a #if operand or
% operator. A name left after expansion, keyword or not, is 0.
expr_token(t(A, Loc, _, _), tok(T, Loc)) :-
    atom_chars(A, Cs),
    (   catch(c_tokens(Cs, '<condition>', [tok(T0, _)]), nanofil_error(_), fail)
    ->  expr_operand(T0, T)
    ;   Cs = [C|_], ident_start(C)
    ->  T = int(0, none-dec)
    ;   pp_error(Loc, bad_if_token(A))
    ).

expr_operand(id(_), int(0, none-dec)) :- !.
expr_operand(kw(_), int(0, none-dec)) :- !.
expr_operand(T, T).

pp_error(Loc, Why) :-
    format(atom(Msg), '~w: ~w', [Loc, Why]),
    throw(nanofil_error(Msg)).

%% Target profile

%! pp_profile(+Clang, -Profile)
%
%  Profile is profile(Macros, IncludeDirs, FeatureAnswers) for the
%  target of the clang executable Clang: its predefined macros, its
%  #include <...> search path and its answers to feature operators.
%
%  Impure adapter: discover the selected target, never preprocess the input.
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

% clang defines __SIZEOF_INT128__, but nanofil refuses __int128: a
% program that tests for it (coreutils' factor.c) takes its portable
% path instead. nanofil-cc undefines it in clang's preprocessing too.
profile_define([t('#', _, _, _), t(define, _, _, _), t('__SIZEOF_INT128__', _, _, _)|_],
               Macros, Macros) :- !.
profile_define([t('#', _, _, _), t(define, _, _, _)|Ts], Macros0, Macros) :-
    !,
    definition_macros(Ts, Macros0, Macros).
profile_define(_, Macros, Macros).

% clang_output(+Command, +Args, -Chars): run Command with Args; Chars is
% its standard output. Fails unless it exits with status 0.
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

text_lines([Line|Lines]) -->
    text_line(Line), !,
    text_lines(Lines).
text_lines([]) --> [].

% A line needs at least a newline or one character.
text_line([]) --> ['\n'], !.
text_line([C|Cs]) -->
    [C], !,
    text_rest(Cs).

text_rest([]) --> ['\n'], !.
text_rest([C|Cs]) -->
    [C], !,
    text_rest(Cs).
text_rest([]) --> [].

% include_directories(+Lines, -Paths): Paths are the directories listed
% after clang -v's "#include <...>" line; fails if there is none.
include_directories([Line|Lines], Paths) :-
    (   Line = "#include <...> search starts here:"
    ->  path_lines(Lines, Paths)
    ;   include_directories(Lines, Paths)
    ).

path_lines([[' '|Cs]|Lines], [Path|Paths]) :-
    !,
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

% feature_value(+Features, +Op, +Name, -A): A is the spelling of
% Op(Name), asking clang if the profile has no answer for it.
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

% query_features(+Clang, +Pairs, -Answers): Answers are clang's
% answer(Op, Name, A) for each Op-Name in Pairs.
query_features(Clang, Pairs, Answers) :-
    findall(Quoted,
            (   member(Op-Name, Pairs),
                format(atom(Query), '~w(~w)', [Op, Name]),
                shell_quoted(Query, Quoted)
            ),
            Queries),
    atomic_list_concat(Queries, ' ', Args),
    shell_quoted(Clang, ClangQuoted),
    format(atom(Cmd), "printf '%s\\n' ~w | ~w -E -P -x c -",
           [Args, ClangQuoted]),
    clang_output('/bin/sh', ['-c', Cmd], Cs),
    source_tokens(Cs, '<features>':1, PpTokens),
    exclude(=(nl), PpTokens, Values),
    maplist(feature_answer, Pairs, Values, Answers).

feature_answer(Op-Name, t(A, _, _, _), answer(Op, Name, A)).

% shell_quoted(+A, -Quoted): Quoted is A in single quotes for /bin/sh.
shell_quoted(A, Quoted) :-
    atom_chars(A, Cs),
    phrase(shell_chars(Cs), Escaped),
    append(['\''|Escaped], ['\''], All),
    atom_chars(Quoted, All).

shell_chars([]) --> [].
shell_chars(['\''|Cs]) -->
    "'\\''", !,
    shell_chars(Cs).
shell_chars([C|Cs]) --> [C], shell_chars(Cs).
