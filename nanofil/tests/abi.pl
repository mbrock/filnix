/* Public lowering-product contracts, independent of AMD64 placement.
   Inputs are the synchronized fused/live views accepted by filc_abi.
   Expected channels, sizes and ordering come from abi-findings.md and
   setjmp.md, not from inspecting the emitted assembly. */
:- module(abi_tests, [abi_products/0]).
:- use_module('../src/filc_abi').
:- use_module(library(lists)).

abi_products :- transport, snapshot_lifetimes, variadic_lifetime, routing.

transport :-
    Ps = [param(p,tmp(p)),param(s,tmp(s)),param(d,tmp(d)),param(l,tmp(n))],
    Args = [arg(p,tmp(p)),arg(s,tmp(s)),arg(d,tmp(d)),arg(l,tmp(n))],
    Res = tuple([result(tmp(q),p),result(tmp(r),l)]),
    Call = call(Res,tmp(p),Args),
    F = func(mixed,export,tuple([p,l]),Ps,
             [block(start,[],[fused(check_function,Call)],rets([tmp(q),tmp(r)]))]),
    Live = [block(start,[],[Call],rets([tmp(q),tmp(r)]))],
    lower_function(module([F]),F,Live,
        abi_function(mixed,export,tuple([p,l]),229312,
            frame(Plain,Roots,Aliases),Entry,Blocks,
            [pop_frame,exception(buffer(3))],Object,Origins)),
    % p and its result overlap at the call, so neither half can alias.
    memberchk(tmp(p)-P,Aliases), memberchk(tmp(q)-Q,Aliases), P \== Q,
    memberchk(lower(tmp(p))-lower(P),Aliases), memberchk(lower(P),Roots),
    memberchk(lower(tmp(q))-lower(Q),Aliases), memberchk(lower(Q),Roots),
    memberchk(retbuf,Plain), length(Roots,NR),
    Origins == [origin(c,catches,NR,0,0),origin(n,no_catch,NR,0,0)],
    memberchk(receive(buffer(3),[wf(l,tmp(p)),wf(l,lower(tmp(p))),
                               wf(s,tmp(s)),wf(d,tmp(d)),wf(l,tmp(n))]),Entry),
    Words = [wf(l,addr(tmp(p))),wf(l,lower(tmp(p))),wf(s,val(s,tmp(s))),
             wf(d,val(d,tmp(d))),wf(l,val(l,tmp(n)))],
    Result = result(buffer(3),slots([tmp(q),lower(tmp(q)),tmp(r)])),
    Cells = [cell(0,l,tmp(p),lower(tmp(p))),cell(1,s,tmp(s),none),
             cell(2,d,tmp(d),none),cell(3,l,tmp(n),none)],
    Generic = receive_generic(16,[cell(0,p,tmp(q),lower(tmp(q))),cell(1,l,tmp(r),none)]),
    Blocks == [block(start,[],[abi([origin(c),reserve_result(buffer(3)),
                    dispatch(tmp(p),229312,buffer(3),Words,Result,32,Cells,Generic),
                    release_result(buffer(3))])],
                    abi_return([return_buffer([wf(l,addr(tmp(q))),wf(l,lower(tmp(q))),
                                               wf(l,val(l,tmp(r)))]),
                                success_buffer,pop_frame,native_return]))],
    Object == fast_and_generic(229312,adapt(32,
        [wf(l,data(0)),wf(l,aux(0)),wf(s,data(1)),wf(d,data(2)),wf(l,data(3))],
        adapter_result(buffer(3),words,16,packet([data(0),aux(0),data(1)],[aux(1)])))).

snapshot_lifetimes :-
    Is = [call(void,global(collect),[]),
          let(tmp(z),w,setjmp('_setjmp'),[tmp(buf),const(0)]),
          let(tmp(cursor),p,va_args,[const(8)])],
    Bs = [block(start,[],Is,goto(join)),
          block(join,[phi(tmp(q),p,[start-tmp(cursor)])],[],ret),
          block(dead,[],[let(tmp(a),w,setjmp(sigsetjmp),[tmp(buf),const(1)])],ret)],
    F = func(lifetimes,local,void,[param(p,tmp(buf))],Bs),
    lower_function(module([F]),F,Bs,
        abi_function(lifetimes,local,void,1065,frame(Plain,Roots,[]),Entry,Blocks,
                     [pop_frame,exception(registers)],Object,Origins)),
    % Static order is z,a, initialization order a,z, copy order is the
    % logical-key order. Dead sites still disable sharing and count.
    Roots == [lower(tmp(buf)),lower(tmp(cursor)),lower(tmp(q)),
              lower(tmp(hidden(va_snapshot))),lower(shadow(q)),
              lower(setjmp_snapshot(z)),lower(setjmp_snapshot(a)),
              lower(tmp(hidden(setjmp_buf(z)))),lower(tmp(hidden(setjmp_buf(a))))],
    Payload = [shadow(q),tmp(a),tmp(buf),tmp(cursor),tmp(q),tmp(z),
               tmp(hidden(va_snapshot))],
    Entry == [native_frame(registers),stack_check,save_thread,save_return(registers),
              zero_roots(9),push_frame(c),
              receive(registers,[wf(l,tmp(buf)),wf(l,lower(tmp(buf))),
                  wf(l,tmp(hidden(va_snapshot))),wf(l,lower(tmp(hidden(va_snapshot))))]),
              snapshots([a,z],Payload)],
    memberchk(tmp(hidden(setjmp_buf(z))),Plain),
    memberchk(tmp(hidden(setjmp_buf(a))),Plain),
    Origins == [origin(c,catches,9,2,0),origin(n,no_catch,9,2,0)],
    Object == generic_only(promote_incoming(8,
        [wf(l,data(0)),wf(l,aux(0)),wf(l,snapshot),wf(l,snapshot)],
        adapter_result(registers,void,8,packet([],[data(0),aux(0)])))),
    Blocks = [block(start,[],[_,abi([origin(c),returns_twice(z,1,tmp(buf),const(0),Payload)]),
                     abi([snapshot_cursor(tmp(hidden(va_snapshot)),8,cursor)])],goto(join)),
              block(join,_,[],abi_return([pop_frame,success(registers)])),
              block(dead,[],[abi([origin(c),returns_twice(a,2,tmp(buf),const(1),Payload)])],_)].

variadic_lifetime :-
    Is = [let(tmp(early),p,alloc(8),[const(8)]),
          call(void,global(collect),[]),
          let(tmp(cursor),p,va_args,[const(8)]),
          let(tmp(late),p,alloc(8),[const(8)]),
          call(result(tmp(out),s),global(ext),[arg(p,tmp(late))])],
    Bs = [block(start,[],Is,ret(tmp(out)))],
    F = func(vfloat,local,s,[param(w,tmp(n))],Bs),
    lower_function(module([F]),F,Bs,
        abi_function(vfloat,local,s,136,frame(_,Roots,Aliases),_,
                     [block(start,[],Lowered,Jump)],_,Object,_)),
    % No setjmp: sharing is enabled. A dead pointer on either side of
    % va_args must still not reuse the invocation-lived snapshot root.
    memberchk(tmp(hidden(va_snapshot))-Snapshot,Aliases),
    memberchk(lower(tmp(hidden(va_snapshot)))-lower(Snapshot),Aliases),
    memberchk(lower(Snapshot),Roots),
    memberchk(tmp(early)-Early,Aliases), Early \== Snapshot,
    memberchk(tmp(late)-Late,Aliases), Late \== Snapshot,
    Object == generic_only(promote_incoming(8,
        [wf(w,data(0)),wf(l,snapshot),wf(l,snapshot)],
        adapter_result(registers,float(s),8,packet([data(0)],[aux(0)])))),
    Lowered = [let(tmp(early),p,alloc(8),[const(8)]),_,
               abi([snapshot_cursor(tmp(hidden(va_snapshot)),8,cursor)]),
               let(tmp(late),p,alloc(8),[const(8)]),
               abi([origin(c),reserve_result(registers),
                    invoke(entry(ext,1067),registers,
                           [wf(l,addr(tmp(late))),wf(l,lower(tmp(late)))]),
                    result(registers,float(s,tmp(out))),release_result(registers)])],
    Jump == abi_return([return_value(s,tmp(out)),pop_frame,success(registers)]).

routing :-
    Fixed = func(fixed,local,void,[],[block(start,[],[],ret)]),
    Variadic = func(variadic,local,void,[],
        [block(start,[],[let(tmp(v),p,va_args,[const(0)])],ret)]),
    Is = [call(void,global(fixed),[]),call(void,global(variadic),[]),
          call(void,global(ext),[arg(w,const(7))]),
          call(void,global(ext),[arg(l,const(8))]),
          let(tmp(local),p,copy,[global(fixed)]),
          let(tmp(external),p,copy,[global(unknown)]),
          call(void,global(wdef),[]),call(void,global(wdecl),[]),
          let(tmp(weakdef),p,copy,[global(wdef)]),
          let(tmp(weakdecl),p,copy,[global(wdecl)])],
    Bs = [block(start,[],Is,ret)], F = func(caller,local,void,[],Bs),
    % A weak definition may be replaced, so it is reached as an external
    % symbol; a weak declaration's getter may be null.
    WeakDef = func(wdef,weak,void,[],[block(start,[],[],ret)]),
    M = module([Fixed,Variadic,F,WeakDef,data(wdecl,extern(weak),1,[])]),
    lower_function(M,F,Bs,abi_function(_,_,_,_,_,_,[block(start,[],Lowered,_)],_,_,_)),
    Lowered = [abi([_,_,invoke(implementation(fixed,1),registers,[]),_,_]),
               abi([_,_,invoke(entry(variadic,1),registers,[]),_,_]),_,_,
               abi([origin(c),getter(local_getter(fixed),c,local)]),
               abi([origin(c),getter(external_getter(unknown),c,external)]),
               abi([_,_,invoke(entry(wdef,1),registers,[]),_,_]),
               abi([_,_,invoke(entry(wdecl,1),registers,[]),_,_]),
               abi([origin(c),getter(external_getter(wdef),c,weakdef)]),
               abi([origin(c),getter(weak_getter(wdecl),c,weakdecl)])],
    % w/l signatures coincide. The sorted representative is l; void
    % requires zero returned bytes although its adapter produces eight.
    % The local variadic's thunk is local, never merged with another
    % object's (tests/c/prog/static-thunks.c).
    lower_thunks(M,[thunk(ext,strong,134,[wf(l,tmp(0))],
                         [cell(0,l,saved(0),none)],8,
                         adapter_result(registers,void,8,packet([],[data(0),aux(0)])),0),
                    thunk(variadic,local,1,[],[],0,
                         adapter_result(registers,void,8,packet([],[data(0),aux(0)])),0),
                    thunk(wdecl,weak,1,[],[],0,
                         adapter_result(registers,void,8,packet([],[data(0),aux(0)])),0),
                    thunk(wdef,strong,1,[],[],0,
                         adapter_result(registers,void,8,packet([],[data(0),aux(0)])),0)]).
