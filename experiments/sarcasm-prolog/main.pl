% Entry points load the module graph explicitly; runtime passes use qualified
% calls so their dependencies and authority are visible.
:- use_module('flags.pl', []).
:- use_module('effects.pl', []).
:- use_module('cfg.pl', []).
:- use_module('x86-flags.pl', []).
:- use_module('x86-cfg.pl', []).
:- use_module('accesses.pl', []).
:- use_module('report.pl', []).
:- use_module('parser.pl').
:- use_module('ir.pl').
:- use_module('x86_64.pl').
:- use_module('target.pl').
:- use_module(library(lists)).
:- initialization(main).

main :- catch((run -> halt(0); throw(error(compilation_failed))), Error,
    (sp_report:diagnostic('sarcasm-prolog',Error),halt(1))).
run :- current_prolog_flag(argv,Chars), maplist(atom_chars,Args,Chars),
    (memberchk(Args,[['--help'],['-h']]) -> usage
    ; options(Args,options(x86_64,on,default,cfg),Config,Path),
      catch(compile(Path,Config),Error,
            (sp_report:diagnostic(Path,Error),halt(1)))).
compile(Path,options(Arch,Opt,Mode,Frontend)) :-
    (Arch=x86_64 -> true; emit(Arch,[])),
    parse_file(Path,Statements),
    (Frontend=linear -> lower(Statements,Functions,Effects),maplist(prepare(Opt),Functions,Prepared,Traces)
    ; sp_cfg:lower(Statements,Functions,Effects),maplist(sp_cfg:prepare(Opt),Functions,Prepared,Traces)),
    (Mode=ir -> sp_report:print_terms(Prepared)
    ; Mode=effects -> sp_report:print_terms(Effects)
    ; Mode=explain -> sp_report:explain(Path,Prepared,Traces)
    ; emit(Arch,Prepared)).
options(['--arch',A|Xs],options(_,O,M,F),Config,P) :- !,options(Xs,options(A,O,M,F),Config,P).
options(['--no-coalesce'|Xs],options(A,_,M,F),Config,P) :- !,options(Xs,options(A,off,M,F),Config,P).
options(['--linear'|Xs],options(A,O,M,_),Config,P) :- !,options(Xs,options(A,O,M,linear),Config,P).
options([Flag|Xs],options(A,O,M,F),Config,P) :- output_flag(Flag,Next), !,
    ((M=default; M=Next) -> options(Xs,options(A,O,Next,F),Config,P)
    ; throw(error(conflicting_output_modes(M,Next)))).
options([P],Config,Config,P) :- atom_chars(P,[C|_]),char_code(C,Code),Code =\= 45,!.
options(_,_,_,_) :- throw(error(invalid_arguments('see --help; select at most one output mode'))).
output_flag('--emit-c',c).
output_flag('--emit-ir',ir).
output_flag('--emit-effects',effects).
output_flag('--explain',explain).
prepare(Opt,function(N,A,IR),function(N,A,Plan),trace(N,Decisions)) :-
    sp_accesses:plan(Opt,IR,Plan,Decisions), validate(IR,Plan).
usage :-
    format('sarcasm-prolog [--arch x86_64|aarch64] [--no-coalesce] [--linear] [MODE] FILE~n',[]),
    format('MODE: --emit-c | --emit-ir | --emit-effects | --explain~n',[]),
    format('The installed wrapper emits Fil-C assembly by default; this Prolog entry emits C.~n',[]).
