% Entry points load the module graph explicitly; runtime passes use qualified
% calls so their dependencies and authority are visible.
:- use_module('flags.pl', []).
:- use_module('effects.pl', []).
:- use_module('cfg.pl', []).
:- use_module('dataflow.pl', []).
:- use_module('x86-flags.pl', []).
:- use_module('x86-cfg.pl', []).
:- use_module('accesses.pl', []).
:- use_module('check-model.pl', []).
:- use_module('check-reuse.pl', []).
:- use_module('check-validator.pl', []).
:- use_module('conditions.pl', []).
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
    ; options(Args,options(x86_64,on,default,cfg,off,on),Config,Path),
      catch(compile(Path,Config),Error,
            (sp_report:diagnostic(Path,Error),halt(1)))).
compile(Path,options(Arch,Opt,Mode,Frontend,Check,Conditions)) :-
    (Arch=x86_64 -> true; emit(Arch,[])),
    parse_file(Path,Statements),
    (Frontend=linear -> lower(Statements,Functions,Effects),maplist(prepare(Opt),Functions,Prepared,Traces)
    ; sp_cfg:lower(Statements,Functions,Effects),maplist(sp_cfg:prepare(Opt),Functions,Grouped,Traces),
      maplist(simplify_conditions(Conditions),Grouped,Prepared)),
    ((Mode=checks;Check=on) ->
       (Frontend=cfg -> maplist(analyze_checks,Prepared,Checks)
       ; throw(error(check_analysis_requires_cfg)))
    ; true),
    (Mode=checks -> maplist(print_check_report,Checks)
    ; Mode=ir -> sp_report:print_terms(Prepared)
    ; Mode=effects -> sp_report:print_terms(Effects)
    ; Mode=explain -> sp_report:explain(Path,Prepared,Traces)
    ; emit(Arch,Prepared)).
options(['--arch',A|Xs],options(_,O,M,F,C,S),Config,P) :- !,options(Xs,options(A,O,M,F,C,S),Config,P).
options(['--no-coalesce'|Xs],options(A,_,M,F,C,S),Config,P) :- !,options(Xs,options(A,off,M,F,C,S),Config,P).
options(['--linear'|Xs],options(A,O,M,_,C,S),Config,P) :- !,options(Xs,options(A,O,M,linear,C,S),Config,P).
options(['--verify-checks'|Xs],options(A,O,M,F,_,S),Config,P) :- !,options(Xs,options(A,O,M,F,on,S),Config,P).
options(['--no-simplify-conditions'|Xs],options(A,O,M,F,C,_),Config,P) :- !,options(Xs,options(A,O,M,F,C,off),Config,P).
options([Flag|Xs],options(A,O,M,F,C,S),Config,P) :- output_flag(Flag,Next), !,
    ((M=default; M=Next) -> options(Xs,options(A,O,Next,F,C,S),Config,P)
    ; throw(error(conflicting_output_modes(M,Next)))).
options([P],Config,Config,P) :- atom_chars(P,[C|_]),char_code(C,Code),Code =\= 45,!.
options(_,_,_,_) :- throw(error(invalid_arguments('see --help; select at most one output mode'))).
output_flag('--emit-c',c).
output_flag('--emit-ir',ir).
output_flag('--emit-effects',effects).
output_flag('--explain',explain).
output_flag('--emit-checks',checks).
analyze_checks(function(N,_,Graph),checks(N,Report)) :- sp_check_reuse:analyze(Graph,Report).
simplify_conditions(Mode,function(N,A,Graph),function(N,A,Next)) :-
    sp_conditions:optimize(Mode,Graph,Next,_).
print_check_report(Report) :- write_term(Report,[quoted(true)]),write('.'),nl.
prepare(Opt,function(N,A,IR),function(N,A,Plan),trace(N,Decisions)) :-
    sp_accesses:plan(Opt,IR,Plan,Decisions), validate(IR,Plan).
usage :-
    format('sarcasm-prolog [--arch x86_64|aarch64] [--no-coalesce] [--no-simplify-conditions] [--linear] [--verify-checks] [MODE] FILE~n',[]),
    format('MODE: --emit-c | --emit-ir | --emit-effects | --explain | --emit-checks~n',[]),
    format('The installed wrapper emits Fil-C assembly by default; this Prolog entry emits C.~n',[]).
