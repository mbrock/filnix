:- use_module('parser.pl').
:- use_module('ir.pl').
:- use_module('x86_64.pl').
:- use_module('target.pl').
:- use_module(library(lists)).
:- initialization(main).

main :- catch((run -> halt(0); throw(error(compilation_failed))), Error,
    (format(user_error,'sarcasm-prolog: ~q~n',[Error]),halt(1))).
run :- current_prolog_flag(argv,Chars), maplist(atom_chars,Args,Chars),
    options(Args,x86_64,on,c,Arch,Opt,Mode,Path),
    % Reject unsupported architectures before interpreting x86 input.
    (Arch=x86_64 -> true; emit(Arch,[])),
    parse_file(Path,Statements), lower(Statements,Functions),
    maplist(prepare(Opt),Functions,Prepared),
    (Mode=ir -> maplist(print_ir,Prepared); emit(Arch,Prepared)).
options(['--arch',A|Xs],_,O,M,Arch,Opt,Mode,P) :- !, options(Xs,A,O,M,Arch,Opt,Mode,P).
options(['--no-coalesce'|Xs],A,_,M,Arch,Opt,Mode,P) :- !, options(Xs,A,off,M,Arch,Opt,Mode,P).
options(['--emit-c'|Xs],A,O,_,Arch,Opt,Mode,P) :- !, options(Xs,A,O,c,Arch,Opt,Mode,P).
options(['--emit-ir'|Xs],A,O,_,Arch,Opt,Mode,P) :- !, options(Xs,A,O,ir,Arch,Opt,Mode,P).
options([P],A,O,M,A,O,M,P) :- !.
options(_,_,_,_,_,_,_,_) :- throw(error(usage('sarcasm-prolog [--arch x86_64|aarch64] [--no-coalesce] [--emit-ir] FILE'))).
prepare(Opt,function(N,A,IR),function(N,A,Plan)) :- plan(Opt,IR,Plan), validate(IR,Plan).
print_ir(function(N,A,Plan)) :-
    format('function(~q,~q,[~n',[N,A]), print_steps(Plan), format(']).~n',[]).
print_steps([]).
print_steps([P|Ps]) :- write('  '), write_term(P,[quoted(true)]),
    (Ps=[] -> nl; write(','),nl), print_steps(Ps).
