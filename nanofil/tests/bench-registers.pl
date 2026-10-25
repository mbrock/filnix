/* SWI-only diagnostic for M6, not part of the compiler or test gate.
   From src/, with C already preprocessed by filcc:
     ../bin/nanofil --script ../tests/bench-registers.pl \
       INPUT.i o0|o1 stack|local OUTPUT.s </dev/null
   Run under /usr/bin/time for peak RSS, assemble OUTPUT.s and use size
   for object text. CPU times exclude source-module loading and printing;
   total includes the frontend, validation, middle end and backend.
   The wrapper measures the public translation check without changing it.
   Alternate modes and repeat; static frame accesses are not dynamic
   memory traffic, and instruction counts do not establish native speed. */
:- use_module('../src/c_lex').
:- use_module('../src/c_parse').
:- use_module('../src/c_lower').
:- use_module('../src/ir').
:- use_module('../src/opt').
:- use_module('../src/pizlonate').
:- use_module('../src/filc_amd64').
:- use_module('../src/asm').
:- use_module(library(prolog_wrap)).
:- use_module(library(pio)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(format)).
:- initialization(main).

main :-
    catch((measure -> halt(0) ; halt(1)),E,(print_message(error,E),halt(1))).

measure :-
    current_prolog_flag(argv,[File,Opt,Mode,Out]),
    nb_setval(check_seconds,0),
    wrap_predicate(amd64_cache_check:check_cache(_M,_B,_A),measure,Wrapped,
        (statistics(cputime,T0),call(Wrapped),statistics(cputime,T1),
         nb_getval(check_seconds,S0), S is S0+T1-T0,
         nb_setval(check_seconds,S))),
    statistics(cputime,Start),
    phrase_from_file(seq(Cs),File), c_tokens(Cs,File,Ts),
    c_parse(Ts,Items), c_module(Items,Module), valid_module(Module),
    optimize(Opt,Module,Optimized), pizlonate_module(Optimized,Checked),
    statistics(cputime,BeforeBackend),
    filc_module_asm(Checked,Mode,Lines,Reports),
    statistics(cputime,End), nb_getval(check_seconds,Check),
    Total is End-Start, Backend is End-BeforeBackend,
    findall(1,member(ins(_,_,_),Lines),Is), length(Is,NIns),
    findall(1,(member(ins(_,_,Ops),Lines),member(mem(_,rbp),Ops)),Fs),
    length(Fs,NFrame),
    findall(N,member(function(_,cached(N,_)),Reports),Ns),sum_list(Ns,Homes),
    findall(N,member(function(_,cached(_,N)),Reports),Rs),sum_list(Rs,Regions),
    findall(X,member(function(_,excluded(X)),Reports),Fallbacks),
    setup_call_cleanup(open(Out,write,Stream),
                       with_output_to(Stream,print_asm(Lines)),close(Stream)),
    format('~w ~w ~w total=~6f backend=~6f checker=~6f~n',
           [File,Opt,Mode,Total,Backend,Check]),
    format('instructions=~d frame=~d homes=~d regions=~d fallbacks=~q~n',
           [NIns,NFrame,Homes,Regions,Fallbacks]).
