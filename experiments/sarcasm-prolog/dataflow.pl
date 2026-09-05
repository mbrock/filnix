:- module(sp_dataflow, [analyze/4, analyze/5, validate/3]).
:- use_module(library(lists)).

% A finite may-domain: each register has a nonempty subset of
% {integer,pointer,uninitialized}; each flag of {defined,undefined}.
% Only singleton initialized types and singleton defined flags are usable.
% The entry state contributes to joins even when block zero has backedges.
analyze(Graph,Initial,States,Stats) :-
    sp_effects:register_roots(Rs),length(Rs,R),length(Graph,B),
    Limit is B*(3*R+12),analyze(Graph,Initial,Limit,States,Stats).
analyze(Graph,Initial,Limit,States,stats(Changes,Limit)) :-
    require((ground(Graph-Initial-Limit),integer(Limit),Limit>=0),invalid_dataflow(arguments)),
    initial(Initial,Entry),check_graph(Graph),
    worklist([0],Graph,Entry,[],0,Limit,Out,Changes),
    maplist(finish(Graph,Entry,Out),Graph,States),
    validate(Graph,Initial,States).

initial(Concrete,abstract(Registers,Flags)) :-
    sp_effects:register_roots(Roots),maplist(initial_register(Concrete),Roots,Registers),
    findall(F-[undefined],flag(F),Flags).
initial_register(S,R,R-[T]) :-
    (memberchk(R-int(_),S) -> T=integer
    ; memberchk(R-ptr(_),S) -> T=pointer
    ; T=uninitialized).
flag(cf). flag(pf). flag(af). flag(zf). flag(sf). flag(of).

check_graph(Graph) :-
    findall(B,member(flow_block(B,_,_),Graph),Ids),sort(Ids,Unique),
    require((Graph=[_|_],same_length(Graph,Ids),Ids==Unique,memberchk(0,Ids)),invalid_dataflow(blocks)),
    forall(member(flow_block(_,_,Next),Graph),
           require(forall(member(B,Next),memberchk(B,Ids)),invalid_dataflow(target))).
incoming(B,Graph,Entry,Out,Inputs) :-
    findall(S,(member(flow_block(P,_,Next),Graph),memberchk(B,Next),memberchk(P-S,Out)),Preds),
    (B=0 -> Inputs=[Entry|Preds];Inputs=Preds).
worklist([],_,_,Out,C,_,Out,C).
worklist([B|Queue],Graph,Entry,Old,C,Limit,Out,Changes) :-
    memberchk(flow_block(B,Steps,Next),Graph),incoming(B,Graph,Entry,Old,Inputs),
    join(Inputs,In),transfer(Steps,In,New),
    (memberchk(B-Previous,Old),Previous==New ->
        worklist(Queue,Graph,Entry,Old,C,Limit,Out,Changes)
    ; (memberchk(B-Previous,Old) ->
          require(covers(New,Previous),invalid_dataflow(non_monotone(B)));true),
      C1 is C+1,require(C1=<Limit,dataflow_limit(Limit)),
      put(B,New,Old,Updated),enqueue(Next,Queue,Pending),
      worklist(Pending,Graph,Entry,Updated,C1,Limit,Out,Changes)).
enqueue([],Q,Q).
enqueue([B|Bs],Q,Out) :-
    (memberchk(B,Q) -> Next=Q;append(Q,[B],Next)),enqueue(Bs,Next,Out).
put(Key,Value,Old,[Key-Value|Rest]) :- remove(Key,Old,Rest).
remove(_,[],[]).
remove(K,[K-_|Xs],Ys) :- !,remove(K,Xs,Ys).
remove(K,[X|Xs],[X|Ys]) :- remove(K,Xs,Ys).

join([First|Inputs],Joined) :- !,join_more(Inputs,First,Joined).
join([],_) :- throw(error(invalid_dataflow(empty_join))).
join_more([],S,S).
join_more([abstract(R,F)|Xs],abstract(A,B),Out) :-
    union_cells(A,R,C),union_cells(B,F,D),join_more(Xs,abstract(C,D),Out).
union_cells([],[],[]).
union_cells([K-A|As],[K-B|Bs],[K-C|Cs]) :-
    append(A,B,Both),sort(Both,C),union_cells(As,Bs,Cs).

transfer([],S,S).
transfer([node(_,_,semantics(_,effects(registers(_,Writes),_,Flags,_,_)))|Ns],
         abstract(Registers,OldFlags),Out) :-
    writes(Writes,Registers,Registers,Next),
    Flags=flags(_,defined(D),cleared(C),undefined(U),preserved(_)),
    append(D,C,Known),maplist(flag_step(Known,U),OldFlags,NextFlags),
    transfer(Ns,abstract(Next,NextFlags),Out).
writes([],_,S,S).
writes([write(register(R,_),Type,_)|Xs],Old,S,Out) :-
    (Type=same_type_as(register(Source,_)) -> memberchk(Source-Values,Old)
    ; memberchk(Type,[integer,pointer]),Values=[Type]),
    replace_cell(R,Values,S,Next),writes(Xs,Old,Next,Out).
replace_cell(K,V,[K-_|Xs],[K-V|Xs]) :- !.
replace_cell(K,V,[X|Xs],[X|Ys]) :- replace_cell(K,V,Xs,Ys).
flag_step(Known,U,F-Old,F-New) :-
    (memberchk(F,Known) -> New=[defined]
    ; memberchk(F,U) -> New=[undefined]
    ; New=Old).

finish(Graph,Entry,Out,flow_block(B,_,_),block_state(B,In,Exit)) :-
    require(memberchk(B-Exit,Out),invalid_dataflow(incomplete(B))),
    incoming(B,Graph,Entry,Out,Inputs),join(Inputs,In).

% Check local inductive obligations, without rerunning the worklist. States
% may conservatively overapproximate the least fixed point, but must include
% entry and every predecessor, and cover the effect transfer of their inputs.
% The graph and instruction effects are the trusted source of these obligations.
validate(Graph,Initial,States) :-
    require(ground(Graph-Initial-States),invalid_dataflow(non_ground)),
    (checked(Graph,Initial,States) -> true;throw(error(invalid_dataflow(structure)))).
checked(Graph,Initial,States) :-
    check_graph(Graph),initial(Initial,Entry),
    findall(B,member(flow_block(B,_,_),Graph),Ids),
    findall(B,member(block_state(B,_,_),States),Found),
    require((Ids==Found,same_length(Ids,States)),invalid_dataflow(changed_blocks)),
    forall(member(block_state(_,I,O),States),(shape(I),shape(O))),
    findall(B-O,member(block_state(B,_,O),States),Outputs),
    maplist(check_block(Graph,Entry,Outputs),Graph,States).
check_block(Graph,Entry,Outputs,flow_block(B,Steps,_),block_state(B,In,Out)) :-
    incoming(B,Graph,Entry,Outputs,Inputs),join(Inputs,Expected),
    require(covers(In,Expected),invalid_dataflow(missing_incoming(B))),
    transfer(Steps,In,Result),
    require(covers(Out,Result),invalid_dataflow(missing_outgoing(B))).
shape(abstract(R,F)) :-
    sp_effects:register_roots(Roots),findall(X,flag(X),Flags),
    maplist(cell([integer,pointer,uninitialized]),Roots,R),
    maplist(cell([defined,undefined]),Flags,F).
cell(Universe,K,K-Values) :-
    require((Values=[_|_],sort(Values,Values),forall(member(V,Values),memberchk(V,Universe))),
            invalid_dataflow(domain(K,Values))).
covers(abstract(A,B),abstract(C,D)) :- covers_cells(A,C),covers_cells(B,D).
covers_cells([],[]).
covers_cells([K-A|As],[K-B|Bs]) :-
    forall(member(V,B),memberchk(V,A)),covers_cells(As,Bs).
require(G,R) :- (call(G) -> true;throw(error(R))).
