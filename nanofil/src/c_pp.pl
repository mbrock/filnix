/* M4e: preprocessing tokens keep spelling, whitespace, location and a hide
   set. Only file and target-profile adapters do I/O.
   No C source or header is sent to clang. */
:- module(c_pp, [pp_file/3, pp_profile/2]).
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(pio)).
:- use_module(library(assoc)).
:- use_module(library(process)).
:- use_module(library(charsio)).
:- use_module(c_lex).

% profile(Macros, IncludeDirectories, FeatureAnswers)
pp_file(File, profile(M, Paths, Features), Tokens) :-
    preprocess(File, env(M, Paths, Features, [], File), _, Raw),
    phrase(classify_tokens(Raw),Tokens).

classify_tokens([]) --> [].
classify_tokens([t(A,L,_,_)|Raw]) -->
    { atom_chars(A,Cs),c_tokens(Cs,'<preprocessing token>',Lex),
      maplist(token_location(L),Lex,Ts) },seq(Ts),classify_tokens(Raw).
token_location(L,tok(T,_),tok(T,L)).

preprocess(F, E0, E, Ts) :-
    E0 = env(M,Paths,Features,Once,Caller),absolute_file_name(F,Identity),
    ( memberchk(Identity,Once) -> E=E0, Ts=[]
    ; read_source(F,Raw),
      lines(Raw, Ls),
      process(Ls,F,[],[],env(M,Paths,Features,Once,F),End,Ts,[]),
      End=env(M1,Paths,Features,Once1,_),E=env(M1,Paths,Features,Once1,Caller)
    ).
% Impure file adapter. Keep the input buffer local so it can be reclaimed
% before processing nested includes; the macro environment stays explicit.
read_source(F,Raw) :- phrase_from_file(seq(Cs),F),once(source_tokens(Cs,F:1,Raw)).

% Translation phases 2 and 3. A comment is one whitespace character, even
% across physical newlines. Space flags are needed by # and #define.
% A parallel location vector survives splicing even inside identifiers and
% literals. In particular __LINE__ after a continuation is the physical
% source line, not the number of newlines in the spliced buffer.
source_tokens(Cs,L,Ts) :- located_splice(Cs,L,Sp,Locs),phrase(scan(Ts,Locs,yes),Sp).
located_splice(['\\','\r','\n'|Cs],F:N,Sp,Ls) :- !,
    N1 is N+1,located_splice(Cs,F:N1,Sp,Ls).
located_splice(['\\','\n'|Cs],F:N,Sp,Ls) :- !,
    N1 is N+1,located_splice(Cs,F:N1,Sp,Ls).
located_splice([C|Cs],F:N,[C|Sp],[F:N|Ls]) :- !,
    ( C=='\n' -> N1 is N+1 ; N1=N ),located_splice(Cs,F:N1,Sp,Ls).
located_splice([],_,[],[]).

scan([nl|Ts], [_|Ls], _) --> ['\n'], !,scan(Ts,Ls,yes).
scan(Ts,[_|Ls],_) --> [C], { space(C) }, !, scan(Ts,Ls,yes).
scan(Ts,[_,_|Ls],_) --> ['/', '/'], !, line_comment(Ls,Rest), scan(Ts,Rest,yes).
scan(Ts,[_,_|Ls],_) --> ['/', '*'], !, comment(Ls,After),scan(Ts,After,yes).
scan([t(A,L,S,[])|Ts],[L|Ls],S) --> spelling(Cs), !,
    { atom_chars(A,Cs),length(Cs,N),N1 is N-1,drop(N1,Ls,Rest) },scan(Ts,Rest,no).
scan([],[],_) --> [].
drop(0,Ls,Ls) :- !.
drop(N,[_|Ls],Rest) :- N1 is N-1,drop(N1,Ls,Rest).

space(' '). space('\t'). space('\r'). space('\f'). space('\v').
line_comment(Ls,Ls), ['\n'] --> ['\n'], !.
line_comment([_|Ls],Rest) --> [_], !, line_comment(Ls,Rest).
line_comment([],[]) --> [].
comment([_,_|Ls],Ls) --> ['*','/'], !.
comment([_|Ls],Rest) --> [_], !, comment(Ls,Rest).
comment(_,_) --> { throw(nanofil_error('unterminated preprocessing comment')) }.

spelling([P,Q|Cs]) --> [P,Q], { memberchk(P,['L',u,'U']), memberchk(Q,['"','\'']) }, !, quoted(Q,Cs).
spelling([Q|Cs]) --> [Q], { memberchk(Q,['"','\'']) }, !, quoted(Q,Cs).
spelling([C|Cs]) --> [C], { start(C) }, !, ident(Cs).
spelling([C|Cs]) --> [C], { digit(C) }, !, number_rest(Cs).
spelling(['.',C|Cs]) --> ['.',C], { digit(C) }, !, number_rest(Cs).
spelling(Cs) --> [A,B,C], { Cs=[A,B,C], atom_chars(P,Cs),
    memberchk(P,['...','<<=','>>=']) }, !.
spelling(Cs) --> [A,B], { Cs=[A,B], atom_chars(P,Cs),
    memberchk(P,['##','->','++','--','<<','>>','<=','>=','==','!=','&&','||',
                 '*=','/=','%=','+=','-=','&=','^=','|=','<:',':>','<%','%>','%:']) }, !.
spelling([C]) --> [C].
quoted(Q,['\\',C|Cs]) --> ['\\',C], !, quoted(Q,Cs).
quoted(Q,[Q]) --> [Q], !.
quoted(Q,[C|Cs]) --> [C], { C \== '\n' }, !, quoted(Q,Cs).
quoted(_,_) --> { throw(nanofil_error('unterminated preprocessing literal')) }.
start(C) :- char_type(C,alpha), !.
start('_'). start('$').
digit(C) :- char_type(C,decimal_digit).
part(C) :- start(C), !.
part(C) :- digit(C).
ident([C|Cs]) --> [C], { part(C) }, !, ident(Cs).
ident([]) --> [].
number_rest([E,S|Cs]) --> [E,S],
    { memberchk(E,[e,'E',p,'P']), memberchk(S,['+','-']) }, !, number_rest(Cs).
number_rest([C|Cs]) --> [C], { part(C); C=='.' }, !, number_rest(Cs).
number_rest([]) --> [].

lines([],[]).
lines(Ts,[L|Ls]) :- Ts\=[], take_line(Ts,L,Rest), lines(Rest,Ls).
take_line([],[],[]).
take_line([nl|Ts],[],Ts) :- !.
take_line([T|Ts],[T|Ls],Rest) :- take_line(Ts,Ls,Rest).

% Ordinary lines are expanded together, so a function invocation can span
% newlines. Directives are barriers; inactive groups never expand tokens.
process([],F,Stack,Pending,E,E,Ts,End) :-
    ( Stack=[] -> true ; pp_error(F:1,'unterminated #if') ),
    expand_pending(Pending,E,Ex), append(Ex,End,Ts).
process([L|Ls],F,Stack,Pending,E0,E,Ts,End) :-
    ( L=[t('#',HashLoc,_,_)|D] ->
        expand_pending(Pending,E0,Ex), append(Ex,Rest,Ts),
        ( D=[t(line,_,_,_)|Args],active(Stack) ->
            expand(Args,E0,Marker),line_target(Marker,HashLoc,Target),
            remap_lines(Ls,HashLoc,Target,More),S1=Stack,E1=E0,Rest=Next
        ; directive(D,F,Stack,S1,E0,E1,Rest,Next),More=Ls ),
        process(More,F,S1,[],E1,E,Next,End)
    ; active(Stack) -> process(Ls,F,Stack,[L|Pending],E0,E,Ts,End)
    ; process(Ls,F,Stack,Pending,E0,E,Ts,End)
    ).

line_target([t(A,_,_,_)|Ts],F:_,NewF:N) :- atom_number(A,N),integer(N),N>0,
    ( Ts=[] -> NewF=F ; include_name(Ts,NewF,quote) ).
remap_lines([],_,_,[]).
remap_lines([Ts|Ls],Old,New,[Rs|Rest]) :-
    maplist(remap_token(Old,New),Ts,Rs),
    remap_lines(Ls,Old,New,Rest).
remap_token(Old,New,t(A,L,S,H),t(A,L1,S,H)) :- remap_location(Old,New,L,L1).
remap_location(_:Old,F:New,_:N,F:M) :- M is N-Old-1+New.

expand_pending(Rev,E,Ts) :- reverse(Rev,Ls),append(Ls,Flat),expand(Flat,E,Ts).
active([]).
active([cond(yes,_,_)|_]).
truth(V,yes) :- V=\=0, !.
truth(_,no).

directive([],_,S,S,E,E,T,T) :- !.
directive([t(K,L,_,_)|Args],F,S0,S,E0,E,T,R) :-
    ( memberchk(K,[if,ifdef,ifndef]) ->
        ( active(S0) -> Parent=yes, condition(K,Args,E0,V), truth(V,B)
        ; Parent=no, B=no ),
        S=[cond(B,B,Parent)|S0], E=E0,T=R
    ; K==elif ->
        ( S0=[cond(_,Seen,P)|Tail], Seen\==else -> true ; pp_error(L,'unexpected #elif') ),
        ( P==yes, Seen==no -> condition(if,Args,E0,V), truth(V,B) ; B=no ),
        ( B==yes -> Seen1=yes ; Seen1=Seen ),
        S=[cond(B,Seen1,P)|Tail],E=E0,T=R
    ; K==else ->
        ( S0=[cond(_,Seen,P)|Tail], Seen\==else -> true ; pp_error(L,'unexpected #else') ),
        ( Seen==no -> B=P ; B=no ), S=[cond(B,else,P)|Tail],E=E0,T=R
    ; K==endif ->
        ( S0=[_|S] -> true ; pp_error(L,'unexpected #endif') ),E=E0,T=R
    ; \+active(S0) -> S=S0,E=E0,T=R
    ; S=S0, E0=env(M,Paths,Features,Once,Current),
      ( K==define -> define(Args,M,M1),E=env(M1,Paths,Features,Once,Current),T=R
      ; K==undef -> Args=[t(Name,_,_,_)],
          remove_macro(Name,M,M1), E=env(M1,Paths,Features,Once,Current),T=R
      ; memberchk(K,[include,include_next]) -> header_operand(Args,E0,Name,Kind),
          search_paths(K,F,Paths,Search),
          ( include_path(Name,Kind,F,Search,Path) -> true ; pp_error(L,include_not_found(Name)) ),
          preprocess(Path,E0,E,Inc), append(Inc,R,T)
      ; K==pragma -> pragma(Args,F,E0,E),T=R
      ; K==error -> pp_error(L,error_directive(Args))
      ; K==ident -> E=E0,T=R
      ; pp_error(L,unsupported_directive(K))
      )
    ).

% Macro save stacks use compound assoc keys, which cannot collide with C
% identifier atoms. Pragma operands are deliberately not macro-expanded.
pragma([t(once,_,_,_)],F,env(M,P,B,Once,C),env(M,P,B,[I|Once],C)) :- !,
    absolute_file_name(F,I).
pragma([t(Op,_,_,_),t('(',_,_,_),Str,t(')',_,_,_)],_,
       env(M,P,B,O,C),env(M1,P,B,O,C)) :-
    memberchk(Op,[push_macro,pop_macro]),include_name([Str],Name,quote),!,
    ( Op==push_macro ->
        ( get_assoc(Name,M,Def) -> Saved=some(Def) ; Saved=none ),
        ( get_assoc(saved(Name),M,Stack) -> true ; Stack=[] ),
        put_assoc(saved(Name),M,[Saved|Stack],M1)
    ; get_assoc(saved(Name),M,[Saved|Stack]) ->
        put_assoc(saved(Name),M,Stack,M0),
        ( Saved=some(Def) -> put_assoc(Name,M0,Def,M1) ; remove_macro(Name,M0,M1) )
    ; M1=M ).
pragma(_,_,E,E).
remove_macro(Name,M,M1) :- ( del_assoc(Name,M,_,M1) -> true ; M1=M ).

define([t(Name,_,_,_)|Ts],M,M1) :-
    ( Ts=[t('(',_,no,_)|Rest] -> params(Rest,Ps,Body), Def=fun(Ps,Body)
    ; Def=obj(Ts) ), put_assoc(Name,M,Def,M1).
params([t(')',_,_,_)|Ts],[],Ts) :- !.
params([t('...',_,_,_),t(')',_,_,_)|Ts],[variadic('__VA_ARGS__')],Ts) :- !.
params([t(P,_,_,_),t('...',_,_,_),t(')',_,_,_)|Ts],[variadic(P)],Ts) :- !.
params([t(P,_,_,_),t(',',_,_,_)|Ts],[P|Ps],Body) :- !,params(Ts,Ps,Body).
params([t(P,_,_,_),t(')',_,_,_)|Ts],[P],Ts).

include_name([t(A,_,_,_)],Name,quote) :- atom_chars(A,['"'|Cs]),
    append(N,['"'],Cs), atom_chars(Name,N), !.
include_name([t('<',_,_,_)|Ts],Name,angle) :-
    append(Mid,[t('>',_,_,_)],Ts), maplist(spell,Mid,As), atomic_list_concat(As,Name).
spell(t(A,_,_,_),A).
header_operand(Ts,E,N,K) :-
    ( include_name(Ts,N,K) -> true ; expand(Ts,E,Ex),include_name(Ex,N,K) ).
include_path(Name,_,_,_,Name) :- sub_atom(Name,0,1,_,'/'), exists_file(Name), !.
include_path(Name,quote,F,_,Path) :- directory(F,D),join(D,Name,Path),exists_file(Path),!.
include_path(Name,_,_,Paths,Path) :- member(D,Paths),join(D,Name,Path),exists_file(Path),!.
directory(F,D) :- atom_chars(F,Cs), reverse(Cs,R), append(_,['/'|Tail],R),!,
    reverse(Tail,Ds),atom_chars(D,Ds).
directory(_,'.').
join(D,N,P) :- atomic_list_concat([D,'/',N],P).
search_paths(include,_,Ps,Ps).
search_paths('__has_include',_,Ps,Ps).
search_paths(_,F,Ps,Rest) :-
    ( append(_,[D|Rest0],Ps),atom_concat(D,'/',Prefix),atom_concat(Prefix,_,F)
    -> Rest=Rest0 ; Rest=Ps ).

% Macro replacement uses token hide sets rather than a global recursion
% stack: an unexpandable token stays unexpandable after argument prescan,
% and a replacement may consume a function-call '(' from the input tail.
expand([],_,[]).
expand([T|Ts],E,Out) :-
    T=t(A,L,S,H), E=env(M,_,_,_,_),
    ( \+memberchk(A,H), get_assoc(A,M,Def),
      replacement(Def,Ts,Rest,E,L,Repl,EndH) ->
        ( EndH=none -> BaseH=H ; intersection(H,EndH,BaseH) ),
        maplist(hide_at([A|BaseH],L),Repl,R0),
        first_space(R0,S,R), append(R,Rest,Next), expand(Next,E,Out)
    ; builtin(T,Ts,Rest,E,R) -> append(R,Rest,Next),expand(Next,E,Out)
    ; Out=[T|Os],expand(Ts,E,Os)
    ).

intersection([],_,[]).
intersection([A|As],Bs,Cs) :-
    ( memberchk(A,Bs) -> Cs=[A|Ds] ; Cs=Ds ),intersection(As,Bs,Ds).
hide_at(H,L,t(A,_,S,H0),t(A,L,S,H1)) :- append(H,H0,Hs),sort(Hs,H1).
first_space([],_,[]).
first_space([t(A,L,_,H)|Ts],S,[t(A,L,S,H)|Ts]).
replacement(obj(Body),Ts,Ts,_,L,R,none) :- paste(Body,R,L).
replacement(fun(Ps,Body),[t('(',_,_,_)|Ts],Rest,E,L,R,H) :-
    arguments(Ts,0,[],[],Args0,Rest,H),
    ( Args0=[[]], Ps=[] -> Args=[] ; Args=Args0 ),
    bindings(Ps,Args,E,Bs,L), substitute(Body,Bs,R0),paste(R0,R,L).

arguments([t(')',_,_,H)|Ts],0,Rev,Acc,Args,Ts,H) :- !,
    reverse(Rev,A),reverse([A|Acc],Args).
arguments([t(',',_,_,_)|Ts],0,Rev,Acc,Args,Rest,H) :- !,
    reverse(Rev,A),arguments(Ts,0,[],[A|Acc],Args,Rest,H).
arguments([T|Ts],N,Rev,Acc,Args,Rest,H) :-
    T=t(A,_,_,_), ( A=='(' -> N1 is N+1 ; A==')' -> N1 is N-1 ; N1=N ),
    arguments(Ts,N1,[T|Rev],Acc,Args,Rest,H).

bindings([],[],_,[],_).
bindings([variadic(P)],As,E,[bind(P,Raw,E)],_) :- !,comma_join(As,Raw).
bindings([P|Ps],[A|As],E,[bind(P,A,E)|Bs],L) :- !,bindings(Ps,As,E,Bs,L).
bindings(_,_,_,_,L) :- pp_error(L,'wrong macro argument count').
comma_join([],[]).
comma_join([A],A) :- !.
comma_join([A|As],Ts) :- comma_join(As,Rest),append(A,[t(',', '<macro>':0,no,[])|Rest],Ts).

substitute(Ts,Bs,Rs) :- sub_tokens(Ts,Bs,no,Rs).
sub_tokens([],_,_,[]).
sub_tokens([t('#',L,S,H),t(P,_,_,_)|Ts],Bs,_,[t(Str,L,S,H)|Rs]) :-
    memberchk(bind(P,Raw,_),Bs),!,stringify(Raw,Str),sub_tokens(Ts,Bs,no,Rs).
sub_tokens([t(P,L,S,H)|Ts],Bs,Prev,Rs) :-
    ( memberchk(bind(P,Raw,E),Bs) ->
        ( ( Prev==yes ; Ts=[t('##',_,_,_)|_] ) -> Use=Raw ; expand(Raw,E,Use) ),
        ( Use=[] -> R=[t('',L,S,H)] ; first_space(Use,S,R) )
    ; R=[t(P,L,S,H)] ),
    ( P=='##' -> Next=yes ; Next=no ),
    append(R,Tail,Rs),sub_tokens(Ts,Bs,Next,Tail).

stringify(Ts,A) :- phrase(string_chars(Ts,first),Cs),
    phrase(escape_string(Cs),Esc),append(['"'|Esc],['"'],All),atom_chars(A,All).
string_chars([],_) --> [].
string_chars([t(A,_,S,_)|Ts],Which) -->
    ( { S==yes, Which\==first } -> [' '] ; [] ),
    { atom_chars(A,Cs) },seq(Cs),string_chars(Ts,next).
escape_string([]) --> [].
escape_string([C|Cs]) -->
    ( { memberchk(C,['"','\\']) } -> ['\\',C] ; [C] ),escape_string(Cs).
paste([t(A,L,S,H),t('##',_,_,_),t(B,_,_,H1)|Ts],Rs,Loc) :- !,
    atom_concat(A,B,C),
    ( C=='' -> true ; atom_chars(C,Cs),phrase(spelling(Cs),Cs) -> true
    ; pp_error(Loc,invalid_token_paste(A,B)) ),
    intersection(H,H1,H2),paste([t(C,L,S,H2)|Ts],Rs,Loc).
paste([t('',_,_,_)|Ts],Rs,L) :- !,paste(Ts,Rs,L).
paste([T|Ts],[T|Rs],L) :- paste(Ts,Rs,L).
paste([],[],_).

% Builtin operators are not macros in clang's -dM output. Feature answers
% are discovered once with the target profile, not guessed from __GNUC__.
builtin(t('__LINE__',L,S,H),Ts,Ts,_,[t(A,L,S,H)]) :- L=_:N,atom_number(A,N).
builtin(t('__FILE__',L,S,H),Ts,Ts,_,[t(A,L,S,H)]) :- L=F:_,
    stringify([t(F,L,no,[])],A).
builtin(t(Op,L,S,H),[t('(',_,_,_)|Ts],Rest,E,[t(A,L,S,H)]) :-
    memberchk(Op,['__has_include','__has_include_next']),
    arguments(Ts,0,[],[],[Arg],Rest,_),header_operand(Arg,E,N,K),
    E=env(_,Paths,_,_,F),search_paths(Op,F,Paths,Search),
    ( include_path(N,K,F,Search,_) -> A='1' ; A='0' ).
builtin(t(K,L,S,H),[t('(',_,_,_),t(Name,_,_,_),t(')',_,_,_)|Ts],Ts,
        env(_,_,Features,_,_),[t(A,L,S,H)]) :-
    feature_operator(K),
    feature_value(Features,K,Name,A).
feature_operator('__has_attribute'). feature_operator('__has_builtin').
feature_operator('__has_extension'). feature_operator('__has_feature').
feature_operator('__has_c_attribute'). feature_operator('__building_module').
is_defined(A,env(M,_,_,_,_)) :- get_assoc(A,M,_),!.
is_defined('__has_include',_).
is_defined('__has_include_next',_).
is_defined('__LINE__',_). is_defined('__FILE__',_).
is_defined(A,_) :- feature_operator(A).

condition(ifdef,[t(A,_,_,_)],E,V) :- ( is_defined(A,E) -> V=1 ; V=0 ).
condition(ifndef,As,E,V) :- condition(ifdef,As,E,N),V is 1-N.
condition(if,As,E,V) :-
    defined_tokens(As,E,Ds),expand(Ds,E,Ex),maplist(expr_token,Ex,Es),
    ( phrase(expression(Tree),Es) -> eval(Tree,V)
    ; pp_error('<condition>':0,bad_if_expression(Es)) ).
defined_tokens([],_,[]).
defined_tokens([t(defined,L,S,H),t('(',_,_,_),t(A,_,_,_),t(')',_,_,_)|Ts],E,
               [t(V,L,S,H)|Rs]) :- !,
    ( is_defined(A,E) -> V='1' ; V='0' ),defined_tokens(Ts,E,Rs).
defined_tokens([t(defined,L,S,H),t(A,_,_,_)|Ts],E,[t(V,L,S,H)|Rs]) :- !,
    ( is_defined(A,E) -> V='1' ; V='0' ),defined_tokens(Ts,E,Rs).
defined_tokens([T|Ts],E,[T|Rs]) :- defined_tokens(Ts,E,Rs).
expr_token(t(A,_,_,_),T) :-
    atom_chars(A,Cs),
    ( Cs=[P,'\''|Rest],memberchk(P,['L',u,'U']) ->
        c_tokens(['\''|Rest],'<condition>',[tok(chr(N),_)]),T=num(N)
    ; Cs=[C|_], start(C) -> T=num(0)
    ; c_tokens(Cs,'<condition>',Lex),
      ( Lex=[tok(int(N,S-_),_)] -> T=num(N,S)
      ; Lex=[tok(chr(N),_)] -> T=num(N)
      ; T=A ) ).

% Pratt-style precedence DCG builds an expression before evaluating it:
% inactive &&/||/?: arms must not divide by zero.
expression(T) --> binary(1,A), conditional(A,T).
conditional(A,T) --> ['?'],!,expression(B),[':'],expression(C),{T=tern(A,B,C)}.
conditional(T,T) --> [].
binary(Min,T) --> unary(A),binary_tail(Min,A,T).
binary_tail(Min,A,T) --> [Op],{precedence(Op,P),P>=Min},!,
    { Next is P+1 },binary(Next,B),binary_tail(Min,bin(Op,A,B),T).
binary_tail(_,T,T) --> [].
unary(un(Op,A)) --> [Op],{memberchk(Op,['+','-','!','~'])},!,unary(A).
unary(A) --> ['('],!,expression(A),[')'].
unary(num(N)) --> [num(N)].
unary(num(N,S)) --> [num(N,S)].
precedence('||',1). precedence('&&',2). precedence('|',3). precedence('^',4).
precedence('&',5). precedence('==',6). precedence('!=',6).
precedence('<',7). precedence('>',7). precedence('<=',7). precedence('>=',7).
precedence('<<',8). precedence('>>',8). precedence('+',9). precedence('-',9).
precedence('*',10). precedence('/',10). precedence('%',10).
% Preprocessor arithmetic uses intmax_t/uintmax_t (64 bits at this pin),
% not the host Prolog's unbounded integers or floating-point division.
eval(num(N),N).
eval(num(N,_),N).
eval(un(Op,A),V) :- eval(A,X),unary_value(Op,X,R),expr_unsigned(un(Op,A),U),wrap(R,U,V).
eval(tern(A,B,C),V) :- eval(A,X),( X=\=0 -> eval(B,R) ; eval(C,R) ),
    expr_unsigned(tern(A,B,C),U),wrap(R,U,V).
eval(bin('&&',A,B),V) :- !,eval(A,X),( X=:=0 -> V=0 ; eval(B,Y),boolean(Y,V) ).
eval(bin('||',A,B),V) :- !,eval(A,X),( X=\=0 -> V=1 ; eval(B,Y),boolean(Y,V) ).
eval(bin(Op,A,B),V) :- eval(A,X0),eval(B,Y0),
    ( memberchk(Op,['<<','>>']) -> X=X0,Y=Y0
    ; usual_unsigned(A,B,U),wrap(X0,U,X),wrap(Y0,U,Y) ),
    binary_value(Op,X,Y,R),expr_unsigned(bin(Op,A,B),ResultU),wrap(R,ResultU,V).
expr_unsigned(num(_),no).
expr_unsigned(num(N,S),U) :-
    ( ( memberchk(S,[u,ul,ull]); N>9223372036854775807 ) -> U=yes ; U=no ).
expr_unsigned(un('!',_),no) :- !.
expr_unsigned(un(_,A),U) :- expr_unsigned(A,U).
expr_unsigned(tern(_,B,C),U) :- usual_unsigned(B,C,U).
expr_unsigned(bin(Op,A,B),U) :-
    ( memberchk(Op,['<','>','<=','>=','==','!=','&&','||']) -> U=no
    ; memberchk(Op,['<<','>>']) -> expr_unsigned(A,U)
    ; usual_unsigned(A,B,U) ).
usual_unsigned(A,B,U) :- expr_unsigned(A,UA),expr_unsigned(B,UB),
    ( ( UA==yes ; UB==yes ) -> U=yes ; U=no ).
wrap(N,U,V) :- Bits is N mod 18446744073709551616,
    ( U==no, Bits>=9223372036854775808 -> V is Bits-18446744073709551616 ; V=Bits ).
boolean(X,1) :- X=\=0,!.
boolean(_,0).
unary_value('+',X,X). unary_value('-',X,V) :- V is -X.
unary_value('~',X,V) :- V is \X.
unary_value('!',X,V) :- ( X=:=0 -> V=1 ; V=0 ).
binary_value('+',X,Y,V) :- V is X+Y.
binary_value('-',X,Y,V) :- V is X-Y.
binary_value('*',X,Y,V) :- V is X*Y.
binary_value('/',X,Y,V) :- V is X//Y.
binary_value('%',X,Y,V) :- V is X rem Y.
binary_value('<<',X,Y,V) :- V is X<<Y.
binary_value('>>',X,Y,V) :- V is X>>Y.
binary_value('&',X,Y,V) :- V is X /\ Y.
binary_value('|',X,Y,V) :- V is X \/ Y.
binary_value('^',X,Y,V) :- V is xor(X,Y).
binary_value('<',X,Y,V) :- ( X<Y -> V=1 ; V=0 ).
binary_value('>',X,Y,V) :- ( X>Y -> V=1 ; V=0 ).
binary_value('<=',X,Y,V) :- ( X=<Y -> V=1 ; V=0 ).
binary_value('>=',X,Y,V) :- ( X>=Y -> V=1 ; V=0 ).
binary_value('==',X,Y,V) :- ( X=:=Y -> V=1 ; V=0 ).
binary_value('!=',X,Y,V) :- ( X=\=Y -> V=1 ; V=0 ).

pp_error(L,Why) :- format(atom(M),'~w: ~w',[L,Why]),throw(nanofil_error(M)).

% Impure adapter: discover the selected target, never preprocess the input.
% This avoids embedding Nix store paths or a second, stale copy of the pin's
% 400+ predefined macros. Pipes are drained before waiting for the child.
pp_profile(Clang,profile(M,Paths,Features)) :-
    clang_output(Clang,['-dM','-E','-x',c,'/dev/null'],Defs),
    source_tokens(Defs,'<built-in>':1,Raw),lines(Raw,Ls),empty_assoc(M0),
    foldl(profile_define,Ls,M0,M),
    process_create(Clang,['-E','-v','-x',c,'/dev/null'],
        [stdout(null),stderr(pipe(S)),process(P)]),
    read_chars(S,Verbose),close(S),process_wait(P,exit(0)),
    phrase(text_lines(VLines),Verbose),include_directories(VLines,Paths),
    feature_profile(Clang,Features).
profile_define([t('#',_,_,_),t(define,_,_,_)|Ts],M,M1) :- !,define(Ts,M,M1).
profile_define(_,M,M).
clang_output(C,Args,Cs) :-
    process_create(C,Args,[stdout(pipe(S)),process(P)]),
    read_chars(S,Cs),close(S),process_wait(P,exit(0)).
read_chars(S,Cs) :- get_char(S,C),
    ( C==end_of_file -> Cs=[] ; Cs=[C|Rest],read_chars(S,Rest) ).
text_lines([L|Ls]) --> text_line(L),!,text_lines(Ls).
text_lines([]) --> [].
text_line([]) --> ['\n'],!.
text_line([C|Cs]) --> [C],!,text_rest(Cs).
text_rest([]) --> ['\n'],!.
text_rest([C|Cs]) --> [C],!,text_rest(Cs).
text_rest([]) --> [].
include_directories([L|Ls],Paths) :-
    ( L="#include <...> search starts here:" -> path_lines(Ls,Paths)
    ; include_directories(Ls,Paths) ).
path_lines([[' '|Cs]|Ls],[P|Ps]) :- !,atom_chars(P,Cs),path_lines(Ls,Ps).
path_lines(_,[]).

% Batch the feature names used by glibc. The adapter uses a shell pipeline
% because this Trealla revision leaves the child's own stdin writer open
% with stdin(pipe(...)); closing the parent stream cannot deliver EOF.
feature_names('__has_attribute',['__nothrow__','__cold__','__malloc__','__alloc_align__',
    '__pure__','__const__','__unused__','__used__','__deprecated__','__format_arg__',
    '__format__','__nonnull__','__returns_nonnull__','__warn_unused_result__',
    '__always_inline__','__artificial__','__indirect_return__']).
feature_names('__has_builtin',['__builtin_expect','__builtin_FILE','__builtin_fclose']).
feature_names('__has_extension',['__attribute_deprecated_with_message__',c_generic_selections]).
feature_names('__has_feature',[modules]).
feature_names('__has_c_attribute',[]).
feature_names('__building_module',['_Builtin_stddef']).
feature_profile(C,features(C,Features)) :-
    findall(K-N,(feature_names(K,Ns),member(N,Ns)),Pairs),
    query_features(C,Pairs,Features).
% This is target introspection only: pass an operator and a single name,
% never a source expression, file, declaration or include to clang.
feature_value(features(C,Answers),K,N,A) :-
    ( memberchk(answer(K,N,A),Answers) -> true
    ; atom_chars(N,[H|Tail]),start(H),maplist(part,Tail),
      query_features(C,[K-N],[answer(K,N,A)]) ).
query_features(C,Pairs,Features) :-
    findall(Q,(member(K-N,Pairs),format(atom(A),'~w(~w)',[K,N]),shell_quote(A,Q)),Qs),
    atomic_list_concat(Qs,' ',Args),shell_quote(C,CQ),
    format(atom(Cmd),"printf '%s\\n' ~w | ~w -E -P -x c -",[Args,CQ]),
    clang_output('/bin/sh',['-c',Cmd],Cs),
    source_tokens(Cs,'<features>':1,Ts),exclude(=(nl),Ts,Vals),
    maplist(feature_answer,Pairs,Vals,Features).
feature_answer(K-N,t(A,_,_,_),answer(K,N,A)).
shell_quote(A,Q) :- atom_chars(A,Cs),phrase(shell_chars(Cs),Esc),
    append(['\''|Esc],['\''],All),atom_chars(Q,All).
shell_chars([]) --> [].
shell_chars(['\''|Cs]) --> "'\\''",!,shell_chars(Cs).
shell_chars([C|Cs]) --> [C],shell_chars(Cs).
