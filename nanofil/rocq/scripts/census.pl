/* This script counts the checked IR stored in generated Rocq fixtures.
   It reads Gallina through the site's parser and counts every element of
   each block's instruction list, regardless of its opcode. It reports phi
   nodes and terminators separately. Identical function terms across files
   count once; different bodies with the same name remain separate rows.

   Run `swipl rocq/scripts/census.pl FILE.v... > census.json` to write
   the counts and their per-function inventory as JSON.

   These counts describe fixture contents, not proved coverage. A function
   term does not establish that its WP premises or initial state are closed.
   The output retains file provenance and body identities for that audit. */
:- use_module('../../web/rocq/rocq_syntax').
:- use_module(library(crypto)).
:- use_module(library(http/json)).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- initialization(main, main).

main :-
    catch(census, E, (print_message(error, E), halt(1))).

census :-
    current_prolog_flag(argv, Files),
    ( Files = [_|_] -> true ; throw(error(domain_error(fixture_files, Files), census)) ),
    maplist(read_fixture, Files, Sources),
    findall(Name-Body,
      ( member(source(_, Items), Sources), sub_term(def(_,_,n(_,Name),[],_,Body), Items) ), Defs),
    nb_setval(census_defs, Defs),
    maplist(file_functions, Sources, Groups), append(Groups, Functions),
    ( Functions = [_|_] -> true ; throw(error(domain_error(function_fixtures, Files), census)) ),
    sort(Functions, Unique),
    findall(Row, function_row(Unique, Row), Rows),
    maplist(row_counts, Rows, Counts),
    foldl(add_counts, Counts, counts(0,0,0,0), counts(B,P,I,T)),
    length(Rows, N), Total is I + T,
    json_write_dict(current_output,
      _{files:Files, functions:N, blocks:B, phis:P, instructions:I,
        terminators:T, instructions_and_terminators:Total, rows:Rows}, [width(0)]), nl.

read_fixture(File, source(File, Items)) :- rocq_read_file(File, _, rocq(Items, _)).

file_functions(source(File, Items), Functions) :-
    findall(fn(Name, Hash, Canonical, File, Counts),
      ( sub_term(Node, Items),
        Node = app(_, id(_, 'TApp'), [str(_, "func"), list(_, [NameNode,_,_,_,Blocks])]),
        NameNode = app(_, id(_, 'TAtom'), [str(_, Name)]),
        normal(Node, Canonical),
        term_string(Canonical, Text, [quoted(true), ignore_ops(true)]),
        crypto_data_hash(Text, Hash, [algorithm(sha256)]),
        ir_list(Blocks, Bs), maplist(block_counts, Bs, Cs),
        foldl(add_counts, Cs, counts(0,0,0,0), Counts)
      ), Functions).

% Positions, parentheses and gallina.pl's list chunking do not change IR.
normal(paren(_, X), Y) :- !, normal(X, Y).
normal(app(_, id(_, 'TList'), [X]), tlist(Ys)) :- !,
    ir_list(X, Xs), maplist(normal, Xs, Ys).
normal(X, Y) :- compound(X), !,
    compound_name_arguments(X, F, Args),
    ( Args = [A-B|Rest], integer(A), integer(B) -> As = Rest ; As = Args ),
    maplist(normal, As, Bs), compound_name_arguments(Y, F, Bs).
normal(X, X).

% gallina.pl --chunk may split a long list with ordinary list append.
ir_list(app(_, id(_, 'TList'), [X]), Items) :- !, ir_list(X, Items).
ir_list(list(_, Items), Items) :- !.
ir_list(paren(_, X), Items) :- !, ir_list(X, Items).
ir_list(app(_, id(_, app), [L,R]), Items) :- !,
    ir_list(L, Ls), ir_list(R, Rs), append(Ls, Rs, Items).
ir_list(bin(_, '++', L, R), Items) :- !,
    ir_list(L, Ls), ir_list(R, Rs), append(Ls, Rs, Items).
ir_list(id(_, Name), Items) :- !,
    nb_getval(census_defs, Defs),
    findall(Body, member(Name-Body, Defs), Bodies),
    ( Bodies = [X] -> ir_list(X, Items)
    ; throw(error(domain_error(unique_list_definition, Name), census)) ).
ir_list(X, _) :- throw(error(domain_error(literal_ir_list, X), census)).

block_counts(app(_, id(_, 'TApp'), [str(_, "block"), list(_, [_,Phis,Insts,_])]),
             counts(1,P,I,1)) :- !,
    ir_list(Phis, Ps), length(Ps, P), ir_list(Insts, Is), length(Is, I).
block_counts(X, _) :- throw(error(domain_error(ir_block, X), census)).

add_counts(counts(B,P,I,T), counts(B0,P0,I0,T0), counts(B1,P1,I1,T1)) :-
    B1 is B+B0, P1 is P+P0, I1 is I+I0, T1 is T+T0.

function_row(Functions, Row) :-
    setof(File, member(fn(Name,Hash,Body,File,Counts), Functions), Files),
    Counts = counts(B,P,I,T),
    % Keep Body in the grouping key too: a hash collision cannot merge IR.
    ground(Body),
    Row = _{name:Name, sha256:Hash, files:Files, blocks:B, phis:P,
            instructions:I, terminators:T}.

row_counts(Row, counts(B,P,I,T)) :-
    B=Row.blocks, P=Row.phis, I=Row.instructions, T=Row.terminators.
