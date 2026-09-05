% Entry points load the module graph explicitly; runtime passes use qualified
% calls so their dependencies and authority are visible.
:- use_module('effects.pl', []).
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
    ; options(Args,x86_64,on,default,Arch,Opt,Mode,Path),
      catch(compile(Path,Arch,Opt,Mode),Error,
            (sp_report:diagnostic(Path,Error),halt(1)))).
compile(Path,Arch,Opt,Mode) :-
    (Arch=x86_64 -> true; emit(Arch,[])),
    parse_file(Path,Statements), lower(Statements,Functions,Effects),
    maplist(prepare(Opt),Functions,Prepared,Traces),
    (Mode=ir -> sp_report:print_terms(Prepared)
    ; Mode=effects -> sp_report:print_terms(Effects)
    ; Mode=explain -> sp_report:explain(Path,Prepared,Traces)
    ; emit(Arch,Prepared)).
options(['--arch',A|Xs],_,O,M,Arch,Opt,Mode,P) :- !, options(Xs,A,O,M,Arch,Opt,Mode,P).
options(['--no-coalesce'|Xs],A,_,M,Arch,Opt,Mode,P) :- !, options(Xs,A,off,M,Arch,Opt,Mode,P).
options([Flag|Xs],A,O,M,Arch,Opt,Mode,P) :- output_flag(Flag,Next), !,
    ((M=default; M=Next) -> options(Xs,A,O,Next,Arch,Opt,Mode,P)
    ; throw(error(conflicting_output_modes(M,Next)))).
options([P],A,O,M,A,O,M,P) :- atom_chars(P,[C|_]), char_code(C,Code), Code =\= 45, !.
options(_,_,_,_,_,_,_,_) :- throw(error(invalid_arguments('see --help; select at most one output mode'))).
output_flag('--emit-c',c).
output_flag('--emit-ir',ir).
output_flag('--emit-effects',effects).
output_flag('--explain',explain).
prepare(Opt,function(N,A,IR),function(N,A,Plan),trace(N,Decisions)) :-
    sp_accesses:plan(Opt,IR,Plan,Decisions), validate(IR,Plan).
usage :-
    format('sarcasm-prolog [--arch x86_64|aarch64] [--no-coalesce] [MODE] FILE~n',[]),
    format('MODE: --emit-c | --emit-ir | --emit-effects | --explain~n',[]),
    format('The installed wrapper emits Fil-C assembly by default; this Prolog entry emits C.~n',[]).
