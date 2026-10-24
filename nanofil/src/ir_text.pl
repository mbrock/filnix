/*  IR text: a module is written as Prolog clauses, one func/5 or
    data/4 term (ir.pl) per item in module order, and read back with
    read_term/3. An IR file may also state run(Fn, Args): a call of Fn
    on the integer Args that difftest and the tests run.

      run(addw, [3, 4]).
      func(addw, export, w, [par(w, t(a)), par(w, t(b))], [
                blk(start, [], [
              ins(t(r), w, add, [t(a), t(b)])
          ], ret(t(r)))
      ]).
      data(msg, local, 1, [item(b, str("hi\\n")), item(b, c(0))]).

    The printer is ours rather than writeq/1, so the text is the same on
    both hosts and the layout stays stable: an atom is bare when it is a
    lowercase identifier, else quoted; a list of characters in str/1 is
    a string (double_quotes is chars on both hosts).
*/
:- module(ir_text, [read_ir_file/3, print_module/1, module_text//1,
                    item_text//1]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).

%! read_ir_file(+File, -Module, -Runs) is det.
%
%  Module is the module(Items) of the IR clauses in File and Runs their
%  run(Fn, Args) terms, each in file order. Throws nanofil_error(Msg)
%  for a clause that is not an item or a run, or not ground. The module
%  is not validated; see ir:valid_module/1.
read_ir_file(File, module(Items), Runs) :-
    setup_call_cleanup(open(File, read, S),
                       read_clauses(S, File, Items, Runs),
                       close(S)).

read_clauses(S, File, Items, Runs) :-
    catch(read_term(S, T, []), error(E, _),
          ( format(atom(Msg), '~w: cannot read IR: ~q', [File, E]),
            throw(nanofil_error(Msg)) )),
    (   T == end_of_file -> Items = [], Runs = []
    ;   ir_clause(T, File, Items, Items1, Runs, Runs1),
        read_clauses(S, File, Items1, Runs1)
    ).

% ir_clause(+T, +File, ?Items0, ?Items, ?Runs0, ?Runs): T adds itself to
% the items or the runs, as difference lists.
ir_clause(T, File, _, _, _, _) :-
    \+ ground(T), !,
    format(atom(Msg), '~w: IR clause with a variable: ~q', [File, T]),
    throw(nanofil_error(Msg)).
ir_clause(run(Fn, Args), _, Is, Is, [run(Fn, Args)|Rs], Rs) :- !.
ir_clause(T, _, [T|Is], Is, Rs, Rs) :-
    ( T = func(_, _, _, _, _) ; T = data(_, _, _, _) ), !.
ir_clause(T, File, _, _, _, _) :-
    format(atom(Msg), '~w: not an IR clause: ~q', [File, T]),
    throw(nanofil_error(Msg)).

%! print_module(+Module) is det.
%
%  Print the text of Module on the current output.
print_module(Module) :-
    phrase(module_text(Module), Cs),
    format("~s", [Cs]).

%! module_text(+Module)//
%
%  The clauses of Module, each item ending in a full stop and a newline.
module_text(module(Items)) --> items(Items).

items([]) --> [].
items([Item|Items]) --> item_text(Item), ".\n", items(Items).

%! item_text(+Item)//
%
%  Item as a term, without its full stop: a function's blocks and
%  instructions one per line, anything else on one line.
item_text(func(Name, Linkage, Ret, Params, Blocks)) --> !,
    "func(", args([Name, Linkage, Ret, Params]), ", [\n",
    blocks(Blocks),
    "])".
item_text(Item) --> term(Item).

blocks([B]) --> !, block(B), "\n".
blocks([B|Bs]) --> block(B), ",\n", blocks(Bs).

block(blk(Label, Phis, Insts, Jump)) -->
    "    blk(", term(Label), ", ", lines(Phis), ", ", lines(Insts), ", ",
    term(Jump), ")".

% lines(+Xs)//: the list Xs, one element per line, or [] when empty.
lines([]) --> !, "[]".
lines(Xs) --> "[\n", elements(Xs), "    ]".

elements([X]) --> !, "        ", term(X), "\n".
elements([X|Xs]) --> "        ", term(X), ",\n", elements(Xs).

% term(+T)//: the text of the ground term T, which read_term/3 reads
% back as T.
term(T) --> { integer(T) }, !, { number_chars(T, Cs) }, seq(Cs).
term(T) --> { atom(T) }, !, atom_text(T).
term([]) --> !, "[]".
term([X|Xs]) --> !, "[", args([X|Xs]), "]".
term(str(Cs)) --> { is_list(Cs) }, !, "str(\"", string_chars(Cs), "\")".
term(L-V) --> !, term(L), "-", term(V).
term(T) --> { T =.. [F|As] }, atom_text(F), "(", args(As), ")".

args([A]) --> !, term(A).
args([A|As]) --> term(A), ", ", args(As).

% atom_text(+A)//: A bare when it is a lowercase identifier, else quoted.
atom_text(A) -->
    { atom_chars(A, Cs) },
    (   { Cs = [C|Rest], lower(C), maplist(ident, Rest) } -> seq(Cs)
    ;   "'", quoted_chars(Cs, ''''), "'"
    ).

string_chars(Cs) --> quoted_chars(Cs, '"').

% quoted_chars(+Cs, +Q)//: Cs inside quotes Q, with Q, backslash and
% control characters escaped.
quoted_chars([], _) --> [].
quoted_chars([C|Cs], Q) --> quoted_char(C, Q), quoted_chars(Cs, Q).

quoted_char(C, Q) --> { C == Q }, !, ['\\', C].
quoted_char('\\', _) --> !, "\\\\".
quoted_char('\n', _) --> !, "\\n".
quoted_char('\t', _) --> !, "\\t".
quoted_char(C, _) -->
    { char_code(C, N), ( N < 32 ; N =:= 127 ) }, !,
    { format(chars(Hex), "~16r", [N]) },
    "\\x", seq(Hex), "\\".
quoted_char(C, _) --> [C].

lower(C) :- char_code(C, N), N >= 0'a, N =< 0'z.
ident(C) :- lower(C), !.
ident(C) :- char_code(C, N), ( N >= 0'A, N =< 0'Z ; N >= 0'0, N =< 0'9 ; N =:= 0'_ ), !.
