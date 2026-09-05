:- module(sp_cfg, [lower/3, lower/4, prepare/4, validate_flow/2]).
:- use_module(library(lists)).

lower(S,F,E) :- lower(S,F,E,_).
lower(Statements,Functions,Effects,Proofs) :-
    sp_ir:strip_metadata(Statements,Code), functions(Code,Functions,Effects,Proofs),
    findall(N,member(function(N,_,_),Functions),Names),sort(Names,Unique),
    require(same_length(Names,Unique),duplicate_function).
functions([],[],[],[]).
functions([located(L,label(N)),located(_,signature(u64,Args))|Ss],
          [function(N,Args,Graph)|Fs],[function(N,Args,Effects)|Es],[Proof|Ps]) :- !,
    require((sp_ir:c_name(N),memberchk(Args,[[ptr],[ptr,u64]])),at(L,unsupported_signature(N,Args))),
    function_body(Ss,Body,Rest), nodes(Body,0,Nodes,Effects),
    blocks([label(L,N)|Nodes],0,[],[],Raw), label_map(Raw,[],Labels),
    maplist(resolve_block(Labels,Raw),Raw,Resolved),
    reachable([0],Resolved,[],Reach0),sort(Reach0,Reach),
    include_reachable(Resolved,Reach,Pending),
    sp_ir:initial_state(Args,Initial),maplist(flow_block,Pending,FlowGraph),
    sp_dataflow:analyze(FlowGraph,Initial,Analysis,_),
    maplist(lower_block(Analysis),Pending,Bounds),
    connect_edge(0,Initial,[],Bounds,Entry),maplist(connect_block(Bounds),Bounds,Connected),
    Graph=cfg(Entry,Connected),Proof=flow(state(Initial,[]),Bounds),
    validate_flow(Graph,Proof), functions(Rest,Fs,Es,Ps).
functions([S|_],_,_,_) :- throw(error(expected_annotated_function(S))).
function_body([],[],[]).
function_body([located(L,label(N)),located(S,signature(R,A))|Xs],[],
              [located(L,label(N)),located(S,signature(R,A))|Xs]) :- !.
function_body([X|Xs],[X|Ys],Rest) :- function_body(Xs,Ys,Rest).
nodes([],_,[],[]).
nodes([located(L,label(Name))|Ss],N,[label(L,Name)|Ns],Es) :- !,nodes(Ss,N,Ns,Es).
nodes([located(L,I)|Ss],N,[node(N,L,Sem)|Ns],[located(L,Sem)|Es]) :-
    catch(sp_effects:instruction_effects(I,Sem),error(R),throw(error(at(L,R)))),
    N1 is N+1,nodes(Ss,N1,Ns,Es).

% A label or terminator ends a block. Adjacent labels alias one block.
blocks([],_,[],[],[]) :- !.
blocks([],_,Names,Steps,_) :-
    (Steps=[node(_,L,_)|_] -> true;Names=[label(_,L)|_]),
    throw(error(at(L,missing_return))).
blocks([label(L,N)|Xs],B,Names,[],Bs) :- !,
    blocks(Xs,B,[label(N,L)|Names],[],Bs).
blocks([label(L,N)|Xs],B,Names,Steps,[raw(B,Labels,Ops,fall(L,Next))|Bs]) :- !,
    reverse(Names,Labels),reverse(Steps,Ops),Next is B+1,
    blocks([label(L,N)|Xs],Next,[],[],Bs).
blocks([node(N,L,Sem)|Xs],B,Names,Steps,Bs) :-
    Sem=semantics(_,effects(_,_,_,control(Control),_)),
    (Control=next -> blocks(Xs,B,Names,[node(N,L,Sem)|Steps],Bs)
    ; reverse(Names,Labels),reverse(Steps,Ops),Next is B+1,
      Bs=[raw(B,Labels,Ops,terminal(node(N,L,Sem),Next))|Rest],
      blocks(Xs,Next,[],[],Rest)).
label_map([],Map,Map).
label_map([raw(B,Names,_,_)|Bs],Old,Map) :-
    add_labels(Names,B,Old,Next),label_map(Bs,Next,Map).
add_labels([],_,M,M).
add_labels([label(N,L)|Ns],B,Old,Map) :-
    require(\+memberchk(N-_,Old),at(L,duplicate_label(N))),
    add_labels(Ns,B,[N-B|Old],Map).
resolve_block(Labels,All,raw(B,N,S,T),raw(B,N,S,Resolved)) :-
    resolve_term(T,Labels,All,Resolved).
resolve_term(fall(L,B),_,All,jump(L,B)) :- target_exists(B,L,All).
resolve_term(terminal(Node,Next),Labels,All,T) :-
    Node=node(_,L,semantics(Action,_)),
    (Action=return(_) -> T=return_node(Node)
    ; Action=jump(Name) -> target_label(Name,L,Labels,B),T=jump(L,B)
    ; Action=branch(C,Name) -> target_label(Name,L,Labels,B),target_exists(Next,L,All),T=branch(L,C,B,Next)
    ; throw(error(at(L,invalid_terminator(Action))))).
target_label(Name,L,Labels,B) :- require(memberchk(Name-B,Labels),at(L,unknown_label(Name))).
target_exists(B,L,All) :- require(memberchk(raw(B,_,_,_),All),at(L,missing_fallthrough)).
successors(return_node(_),[]).
successors(jump(_,B),[B]).
successors(branch(_,_,A,B),Xs) :- sort([A,B],Xs).
reachable([],_,Seen,Seen).
reachable([B|Queue],All,Seen,Reach) :-
    (memberchk(B,Seen) -> reachable(Queue,All,Seen,Reach)
    ; memberchk(raw(B,_,_,T),All),successors(T,Next),append(Next,Queue,Pending),
      reachable(Pending,All,[B|Seen],Reach)).
include_reachable([],_,[]).
include_reachable([raw(B,N,S,T)|Xs],Reach,Ys) :-
    (memberchk(B,Reach) -> Ys=[raw(B,N,S,T)|Rest];Ys=Rest),include_reachable(Xs,Reach,Rest).

% Type/flag availability reaches a finite fixed point before any value IR is
% produced. Parameter identities break cycles in the value representation.
flow_block(raw(B,_,Nodes,Term),flow_block(B,Nodes,Next)) :- successors(Term,Next).
lower_block(Analysis,raw(B,Names,Nodes,T),bound(B,Names,Params,Ops,Term,Out,OutFlags)) :-
    memberchk(block_state(B,abstract(Types,Available),_),Analysis),
    register_inputs(Types,B,RegParams,State),
    findall(parameter(flag(F),boolean,param(B,flag(F))),member(F-[defined],Available),FlagParams),
    findall(F-param(B,flag(F)),member(F-[defined],Available),Flags),
    append(RegParams,FlagParams,Params),
    lower_nodes(Nodes,State,Flags,Ops,Out,OutFlags),lower_term(T,Out,OutFlags,Term).
register_inputs([],_,[],[]).
register_inputs([R-Types|Rs],B,Params,State) :-
    (memberchk(uninitialized,Types) -> Params=Ps,State=Ss
    ; Types=[integer] -> Params=[parameter(reg(R),integer,param(B,reg(R)))|Ps],State=[R-int(param(B,reg(R)))|Ss]
    ; Types=[pointer] -> Params=[parameter(reg(R),pointer,param(B,reg(R)))|Ps],State=[R-ptr(param(B,reg(R)))|Ss]
    ; Params=Ps,State=[R-incompatible(Types)|Ss]),
    register_inputs(Rs,B,Ps,Ss).
lower_nodes([],S,F,[],S,F).
lower_nodes([node(N,L,Sem)|Ns],State,Flags,Ops,Out,OutFlags) :-
    sp_ir:lower_step(Sem,State,N,L,Op,Next,Bindings),
    sp_flags:transfer(Sem,Bindings,N,L,Flags,FlagOps,NextFlags),
    (Op=compare(_,_,_,_,_) -> Here=FlagOps;Here=[Op|FlagOps]),
    append(Here,Rest,Ops),lower_nodes(Ns,Next,NextFlags,Rest,Out,OutFlags).
lower_term(return_node(node(N,L,Sem)),State,_,Term) :-
    sp_ir:lower_step(Sem,State,N,L,Term,_,_).
lower_term(jump(_,B),_,_,jump(B)).
lower_term(branch(L,C,A,B),_,Flags,branch(Expr,A,B)) :- sp_flags:condition(C,Flags,L,Expr).

connect_block(All,bound(B,N,P,O,T,S,F),block(B,N,P,O,Term)) :- connect_term(T,S,F,All,Term).
connect_term(return(V),_,_,_,return(V)).
connect_term(jump(B),S,F,All,jump(Edge)) :- connect_edge(B,S,F,All,Edge).
connect_term(branch(C,A,B),S,F,All,branch(C,EA,EB)) :-
    connect_edge(A,S,F,All,EA),connect_edge(B,S,F,All,EB).
connect_edge(B,State,Flags,All,edge(B,Copies)) :-
    memberchk(bound(B,_,Params,_,_,_,_),All),
    maplist(copy_input(State,Flags),Params,Copies).
copy_input(State,_,parameter(reg(R),integer,D),set(D,integer,view(V,64))) :- memberchk(R-int(V),State).
copy_input(State,_,parameter(reg(R),pointer,D),set(D,pointer,V)) :- memberchk(R-ptr(V),State).
copy_input(_,Flags,parameter(flag(F),boolean,D),set(D,boolean,V)) :- memberchk(F-V,Flags).

% Validate proposals against recorded, typed exit states and original targets.
% This does not call connect_edge/copy_input or repeat the worklist search.
validate_flow(Graph,Proof) :-
    require(ground(Graph-Proof),invalid_control_flow(non_ground)),
    (checked_flow(Graph,Proof) -> true;throw(error(invalid_control_flow(unrecognized_structure)))).
checked_flow(Graph,Proof) :-
    Graph=cfg(Entry,Blocks),Proof=flow(state(Initial,IF),Bounds),
    findall(B,member(block(B,_,_,_,_),Blocks),Ids),
    findall(B,member(bound(B,_,_,_,_,_,_),Bounds),Expected),
    require(Ids==Expected,invalid_control_flow(changed_blocks)),
    sort(Ids,Unique),require(same_length(Ids,Unique),invalid_control_flow(duplicate_blocks)),
    check_edge(Entry,0,Initial,IF,Bounds),
    maplist(check_block(Bounds),Bounds,Blocks).
check_block(All,bound(B,N,P,O,T,S,F),block(B1,N1,P1,O1,T1)) :-
    require(B-N-P-O==B1-N1-P1-O1,invalid_control_flow(changed_block(B))),
    check_term(T,T1,S,F,All).
check_term(return(V),return(W),_,_,_) :-
    require(V==W,invalid_control_flow(changed_return)).
check_term(jump(B),jump(E),S,F,All) :- check_edge(E,B,S,F,All).
check_term(branch(C,A,B),branch(D,EA,EB),S,F,All) :-
    require(C==D,invalid_control_flow(changed_condition)),
    check_edge(EA,A,S,F,All),check_edge(EB,B,S,F,All).
check_edge(edge(Target,Sets),Expected,State,Flags,All) :-
    require(Target==Expected,invalid_control_flow(changed_target(Expected,Target))),
    require(memberchk(bound(Target,_,Params,_,_,_,_),All),invalid_control_flow(missing_target(Target))),
    require(same_length(Params,Sets),invalid_control_flow(edge_arity(Target))),
    findall(binding(reg(R),integer,view(V,64)),member(R-int(V),State),Ints),
    findall(binding(reg(R),pointer,V),member(R-ptr(V),State),Pointers),
    findall(binding(flag(F),boolean,V),member(F-V,Flags),Bits),
    append(Ints,Pointers,Registers),append(Registers,Bits,Bindings),
    maplist(check_set(Bindings),Params,Sets).
check_set(Bindings,parameter(Key,Type,Dest),set(D,T,V)) :-
    require(D==Dest,invalid_control_flow(changed_parameter(Key))),
    require(T==Type,invalid_control_flow(changed_type(Key))),
    require(memberchk(binding(Key,Type,V),Bindings),invalid_control_flow(changed_edge_value(Key,V))).
require(G,R) :- (call(G) -> true;throw(error(R))).

prepare(Mode,function(N,A,cfg(E,Bs)),function(N,A,cfg(E,Ps)),trace(N,blocks(Traces))) :-
    maplist(prepare_block(Mode),Bs,Ps,Traces).
prepare_block(Mode,block(B,N,P,IR,T),block(B,N,P,Plan,T),trace_block(B,Ds)) :-
    sp_accesses:plan(Mode,IR,Plan,Ds),sp_accesses:validate(IR,Plan).
