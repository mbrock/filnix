/*  Fil-C ABI lowering, before AMD64 placement and instruction selection.

    lower_function/4 reads two synchronized views: checked operations
    (proof/access pairs already fused) and ordinary operations for liveness.
    It never inserts an instruction into either view. Each abi(Actions)
    occupies its original closed instruction interval, including all its
    helper calls. Memory operations pass through unchanged.

    The product is a function with a frame, entry actions, lowered blocks,
    exception exit, public object and origins. Frames name payload slots,
    ordered roots and aliases, not native offsets. Fast words explicitly
    split pointers into address/lower; generic cells carry separate data
    and aux sources, including zero aux for scalars. registers/buffer(N)
    chooses the return protocol; AMD64 assigns registers and buffer bytes.

    `frame(Plain, Roots, Aliases)` includes `local(Name, Size)` in Plain
    for nonescaping objects, separate from temporary slots. The special
    `stack_aux(Name)` roots form a suffix before the setjmp slots;
    `origin(Which, Catch, NRoots, NSetjmps, NLocals)` describes that order
    to the collector. `initialize_local(Name)` zeroes payload and aux
    and publishes the stack-aux root without a safepoint. It does not
    produce a heap lower or an address value.

    `returns_twice` invokes native setjmp in the current body and restores
    payloads without a safepoint before writing the full native int result.
    Setjmp disables sharing even for unreachable sites. Its snapshots
    contain every logical temporary/phi payload, never frame bookkeeping
    or jmpbuf payloads. Snapshot roots are stable from entry; jmpbuf roots
    are last and persist across nonlocal returns. Variadic entry promotes
    the incoming packet eagerly and passes an invocation-lived hidden
    pointer to the private body. `promote_incoming` uses the original
    packet size, then roots that pointer in the body before any further
    safepoint. See docs/setjmp.md and abi-findings.md.
*/
:- module(filc_abi, [lower_function/4, lower_thunks/2, signature/3, never_signature/1]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ir).
:- use_module(frame_slots).

% lower_function(+Module, +FusedFunction, +LiveBlocks, -Product).
lower_function(Module, Func, LiveBlocks,
               abi_function(Name, Linkage, Ret, Sig, Frame, Entry, Blocks,
                            Exit, Object, Origins)) :-
    Func = func(Name, Linkage, Ret, Params, Blocks0),
    param_kinds(Params, Ks), signature(Ret, Ks, Sig),
    return_protocol(Ret, Return),
    body_params(Func, Params, BodyParams),
    frame(BodyParams, LiveBlocks, Return, Frame, Snapshots),
    Frame = frame(Plain, Roots, _), length(Roots, NRoots),
    findall(N, member(local(N, _), Plain), LocalNames), length(LocalNames, NLocals),
    fast_params(BodyParams, Incoming),
    Snapshots = snapshots(Sites, Payload), sort(Sites, InitSites),
    Entry = [native_frame(Return), stack_check, save_thread, save_return(Return),
             zero_roots(NRoots), push_frame(c), receive(Return, Incoming),
             snapshots(InitSites, Payload)],
    Exit = [pop_frame, exception(Return)],
    maplist(lower_block(Module, Ret, Return, Snapshots), Blocks0, Blocks),
    public_object(Func, Return, Object),
    Snapshots = snapshots(Sites, _), length(Sites, NSites),
    Origins = [origin(c, catches, NRoots, NSites, NLocals),
               origin(n, no_catch, NRoots, NSites, NLocals)].

% The bijective base-11 encoding is independent of native locations.
signature(Ret, ParamKs, Sig) :-
    ret_kinds(Ret, RetKs),
    maplist(class_digit, RetKs, RetDigits),
    maplist(class_digit, ParamKs, ArgDigits),
    length(ArgDigits, NArgs),
    (   NArgs =< 16
    ->  bijective_value(RetDigits, R), bijective_value(ArgDigits, A),
        Sig is 1 + R + 133 * A
    ;   never_signature(Sig)
    ).

% More than 16 words have no fast signature (clang's is generic, 0). A
% call site gets one no function object has, the largest 64-bit value
% (fast signatures stay below 2^63), so it always goes generic; the
% frontend makes such a definition generic-only, and its private body is
% named with this one.
never_signature(18446744073709551615).

class_digit(w, 0).
class_digit(l, 0).
class_digit(p, 7).
class_digit(s, 1).
class_digit(d, 2).
bijective_value([], 0).
bijective_value([D|Ds], V) :-
    bijective_value(Ds, V1), V is D + 1 + 11 * V1.

param_kinds(Ps, Ks) :- findall(K, member(param(K, _), Ps), Ks).
ret_kinds(void, []).
ret_kinds(tuple(Ks), Ks).
ret_kinds(w, [w]).
ret_kinds(l, [l]).
ret_kinds(p, [p]).
ret_kinds(s, [s]).
ret_kinds(d, [d]).

% A buffer has one exception byte followed by N full payload/lower words.
return_protocol(Ret, Protocol) :-
    ret_kinds(Ret, Ks), foldl(return_words, Ks, 0, N),
    ( N > 2 -> Protocol = buffer(N) ; Protocol = registers ).
return_words(p, N0, N) :- N is N0 + 2.
return_words(w, N0, N) :- N is N0 + 1.
return_words(l, N0, N) :- N is N0 + 1.
% Float words return in %xmm0 and %xmm1, not in integer registers.
return_words(s, N, N).
return_words(d, N, N).

body_params(Func, Ps, Body) :-
    ( variadic_func(Func)
    -> append(Ps, [param(p, tmp(hidden(va_snapshot)))], Body)
    ; Body = Ps ).

frame(Params, Blocks, Return, frame(Plain, Roots, Aliases),
      snapshots(Sites, Payload)) :-
    findall(N-K, (member(param(K, tmp(N)), Params)
                ; member(block(_, Phis, Is, _), Blocks),
                  ( member(phi(tmp(N), K, _), Phis)
                  ; member(I, Is), inst_dest(I, N, K) )), Temps0),
    sort(Temps0, Temps),
    findall(N-K, (member(block(_, Phis, _, _), Blocks),
                  member(phi(tmp(N), K, _), Phis)), Shadows0),
    sort(Shadows0, Shadows),
    findall(shadow(N), member(N-_, Shadows), ShadowKeys),
    findall(D, (member(block(_, _, Is, _), Blocks),
                member(let(tmp(D), w, setjmp(_), _), Is)), Sites),
    temp_storage(Sites, Params, Blocks, Temps, Keys, Lowers, Aliases),
    return_storage(Return, Extra),
    findall(tmp(hidden(setjmp_buf(D))), member(D, Sites), JPlain),
    local_objects(func(frame, local, void, Params, Blocks), Locals),
    findall(local(N, Size), member(N-Size, Locals), LocalStorage),
    findall(stack_aux(N), member(N-_, Locals), LocalRoots),
    append([Keys, ShadowKeys, [thread, aux], Extra, JPlain, LocalStorage], Plain),
    findall(lower(shadow(N)), member(N-p, Shadows), ShadowRoots),
    findall(lower(setjmp_snapshot(D)), member(D, Sites), SnapRoots),
    findall(lower(tmp(hidden(setjmp_buf(D)))), member(D, Sites), JRoots),
    % Explicit stack auxes are the final root group before jmpbufs,
    % as filc_function_origin_stack_aux_begin/end_index specifies.
    append([Lowers, ShadowRoots, SnapRoots, LocalRoots, JRoots], Roots),
    % Preserve the old assoc's canonical payload traversal order.
    findall(tmp(N), member(N-_, Temps), TempPayload),
    append(TempPayload, ShadowKeys, Payload0), sort(Payload0, Payload).

temp_storage([], Ps, Bs, Temps, Keys, Lowers, Aliases) :-
    temp_slots(Ps, Bs, Temps, Map, NS, NP, NW),
    storage_keys(scalar, NS, Scalars), storage_keys(pointer, NP, Pointers),
    storage_keys(wide, NW, Wides),
    append([Scalars, Pointers, Wides], Keys), maplist(storage_lower, Pointers, Lowers),
    assoc_to_list(Map, Pairs), foldl(storage_alias, Pairs, Aliases, []).
temp_storage([_|_], _, _, Temps, _, _, _) :-
    memberchk(_-x, Temps), !,
    throw(nanofil_error('long double in a function that calls setjmp is not supported')).
temp_storage([_|_], _, _, Temps, Keys, Lowers, []) :-
    findall(tmp(N), member(N-_, Temps), Keys),
    findall(lower(tmp(N)), member(N-p, Temps), Lowers).
storage_keys(Pool, N, Keys) :-
    Last is N - 1, findall(storage(Pool, I), between(0, Last, I), Keys).
storage_lower(Key, lower(Key)).
storage_alias(N-storage(pointer,I),
              [tmp(N)-storage(pointer,I),lower(tmp(N))-lower(storage(pointer,I))|As], As).
storage_alias(N-storage(scalar,I), [tmp(N)-storage(scalar,I)|As], As).
storage_alias(N-storage(wide,I), [tmp(N)-storage(wide,I)|As], As).
return_storage(registers, []).
return_storage(buffer(_), [retbuf]).
inst_dest(let(tmp(N), K, _, _), N, K).
inst_dest(flight(tmp(N), _, _, _), N, p).
inst_dest(local_load(tmp(N), K, _, _, _), N, K).
inst_dest(call(result(tmp(N), K), _, _), N, K).
inst_dest(call(tuple(Tos), _, _), N, K) :- member(result(tmp(N), K), Tos).

% No physical locations: these are ordered words and their sources.
fast_params(Ps, Ts) :- foldl(fast_param, Ps, Ts, []).
fast_param(param(p,T), [wf(l,T),wf(l,lower(T))|Ts], Ts).
fast_param(param(K,T), [wf(K,T)|Ts], Ts) :- K \== p.
fast_args(As, Ts) :- foldl(fast_arg, As, Ts, []).
fast_arg(arg(p,V), [wf(l,addr(V)),wf(l,lower(V))|Ts], Ts).
fast_arg(arg(K,V), [wf(K,val(K,V))|Ts], Ts) :- K \== p.

% Generic cells are one eightbyte per source value, not per fast word.
% Source names for adapters are abstract too: data(I), aux(I), snapshot.
generic_args(Args, Cells) :-
    findall(cell(I, B, V, Lower),
            (nth0(I, Args, arg(K,V)), value_lower(K,V,Lower), payload_class(K,B)), Cells).
payload_class(p,l).
payload_class(K,K) :- K \== p.
value_lower(p, V, lower(V)).
value_lower(K, _, none) :- K \== p.
generic_params(Ks, Ts) :-
    findall(wf(B, Source), (nth0(I,Ks,K), packet_word(K,I,B,Source)), Ts).
packet_word(p, I, l, data(I)).
packet_word(p, I, l, aux(I)).
packet_word(K, I, K, data(I)) :- K \== p.

result_tos(void, []).
result_tos(result(T,K), [result(T,K)]).
result_tos(tuple(Tos), Tos).
result_ret(void, void).
result_ret(result(_,K), K).
result_ret(tuple(Tos), tuple(Ks)) :-
    findall(K, member(result(_,K), Tos), Ks).
result_slots(Tos, Slots) :- foldl(result_slot, Tos, Slots, []).
result_slot(result(T,p), [T,lower(T)|Ss], Ss).
result_slot(result(T,K), [T|Ss], Ss) :- K \== p.

% Results name their channels explicitly. Scalar floating results are
% distinct from integer slots; the target must test the exception first.
% A tuple with a float word names each slot's class: typed(K-Slot).
fast_result(Res, result(Return, Channels)) :-
    result_ret(Res, Ret), return_protocol(Ret, Return),
    ( Res = result(T,K), memberchk(K,[s,d]) -> Channels = float(K,T)
    ; Res = tuple(Tos), float_tuple(Tos)
    -> foldl(typed_slot, Tos, Typed, []), Channels = typed(Typed)
    ; result_tos(Res,Tos), result_slots(Tos,Slots), Channels = slots(Slots) ).
float_tuple(Tos) :- member(result(_,K), Tos), memberchk(K, [s,d]), !.
typed_slot(result(T,p), [l-T,l-lower(T)|Ss], Ss) :- !.
typed_slot(result(T,K), [K-T|Ss], Ss).
generic_result(Res, receive_generic(Need, Cells)) :-
    result_tos(Res, Tos), length(Tos,N), Need is 8*N,
    findall(cell(I,K,T,Lower),
            (nth0(I,Tos,result(T,K)), value_lower(K,T,Lower)), Cells).

lower_block(Module, Ret, Return, Snapshots, block(L,Ps,Is0,J0), block(L,Ps,Is,J)) :-
    maplist(lower_inst(Module, Snapshots), Is0, Is),
    lower_jump(Ret, Return, J0, J).

lower_inst(Module, _, call(Res,global(F),Args), abi(Actions)) :- !,
    call_signature(Res, Args, Sig0), call_symbol_signature(Res, Args, Sig0, Sig),
    direct_target(Module,F,Sig,Target),
    fast_result(Res, Result), Result = result(Return,_), fast_args(Args,Words),
    Actions = [origin(c), reserve_result(Return),
               invoke(Target, Return, Words), Result, release_result(Return)].
lower_inst(_, _, fused(check_function,call(Res,P,Args)), abi(Actions)) :- !,
    call_signature(Res,Args,Sig), fast_result(Res,Result),
    Result = result(Return,_), fast_args(Args,Words),
    generic_args(Args,Cells), length(Args,N), Size is 8*N,
    generic_result(Res,GenericResult),
    Actions = [origin(c), reserve_result(Return),
               dispatch(P,Sig,Return,Words,Result,Size,Cells,GenericResult),
               release_result(Return)].
lower_inst(Module, _, let(tmp(D),p,copy,[global(S)]),
           abi([origin(c), getter(Target,c,D)])) :- !,
    getter_target(Module,S,Target).
lower_inst(_, snapshots(_,Keys), let(tmp(D),w,setjmp(Kind),[Buf,Mask]),
           abi([origin(c), returns_twice(D,KindNo,Buf,Mask,Keys)])) :- !,
    setjmp_kind(Kind,KindNo).
lower_inst(_, _, let(tmp(D),p,va_args,[const(Off)]),
           abi([snapshot_cursor(tmp(hidden(va_snapshot)),Off,D)])) :- !.
lower_inst(_, _, let(tmp(D),K,va_arg,[P]),
           abi([origin(c), consume_va(K,P,Size,D)])) :- !,
    % A long double's cell is 16 bytes at 16 (docs/float.md).
    ( K == x -> Size = 16 ; width_bytes(K,Size) ).
lower_inst(_, _, local_alloc(Name, _), abi([initialize_local(Name)])) :- !.
lower_inst(_, _, I, I).

% Returns are actions too: materialize before popping roots, then signal
% success in the appropriate exception channel. No safepoint intervenes.
lower_jump(K, Return, ret(V), abi_return([return_value(K,V),pop_frame,success(Return)])) :- !.
lower_jump(tuple(Ks), buffer(N), rets(Vs),
           abi_return([return_buffer(Words),success_buffer,pop_frame,native_return])) :- !,
    maplist(return_arg,Ks,Vs,Args), fast_args(Args,Words), length(Words,N).
lower_jump(tuple(Ks), registers, rets(Vs),
           abi_return([return_typed(Ks,Vs),pop_frame,success(registers)])) :-
    member(K, Ks), memberchk(K, [s,d]), !.
lower_jump(_, registers, rets(Vs),
           abi_return([return_registers(Vs),pop_frame,success(registers)])) :- !.
lower_jump(_, Return, ret, abi_return([pop_frame,success(Return)])) :- !.
lower_jump(_, _, J, J).
return_arg(K,V,arg(K,V)).

setjmp_kind(setjmp, 0).
setjmp_kind('_setjmp', 1).
setjmp_kind(sigsetjmp, 2).

call_signature(Res, Args, Sig) :-
    result_ret(Res,Ret), findall(K,member(arg(K,_),Args),Ks), signature(Ret,Ks,Sig).

% call_symbol_signature(+Res, +Args, +Sig0, -Sig): Sig names the weak
% thunk a direct call goes through. Every call of more than 16 words has
% the never signature, so its thunk is named never(R-A) by the whole
% word list instead: two such calls with different words (a variadic
% callee's, say) must not share one thunk and its packet size.
call_symbol_signature(Res, Args, Sig0, Sig) :-
    (   never_signature(Sig0)
    ->  result_ret(Res,Ret), findall(K,member(arg(K,_),Args),Ks),
        word_codes(Ret, Ks, Code), Sig = never(Code)
    ;   Sig = Sig0
    ).
word_codes(Ret, Ks, R-A) :-
    ret_kinds(Ret, RetKs),
    maplist(class_digit, RetKs, RDs), maplist(class_digit, Ks, ADs),
    bijective_value(RDs, R), bijective_value(ADs, A).
direct_target(Module,F,_,implementation(F,Sig)) :-
    func_named(Module,F,Func), \+ variadic_func(Func), !,
    Func = func(_,_,Ret,Ps,_), param_kinds(Ps,Ks), signature(Ret,Ks,Sig).
direct_target(_,F,Sig,entry(F,Sig)).
getter_target(module(Items), S, Target) :-
    ( ( memberchk(func(S,_,_,_,_),Items) ; memberchk(data(S,_,_,_),Items) )
    -> Target = local_getter(S) ; Target = external_getter(S) ).

% Adapter plans are consumed by public generic entries and weak thunks.
% The void generic result is one zero word, despite having no fast value.
adapter_return(Ret, adapter_result(Return,Channel,Size,Packet)) :-
    return_protocol(Ret,Return), ret_kinds(Ret,Ks), length(Ks,N),
    Size is 8*max(1,N),
    ( Ks = [] -> Channel = void
    ; Ks = [K], memberchk(K,[s,d]) -> Channel = float(K)
    ; member(K, Ks), memberchk(K,[s,d]) -> Channel = typed(Ks)
    ; Channel = words ),
    generic_params(Ks, Words), findall(S,member(wf(_,S),Words),Copies),
    ( Ks = [] -> Zeros = [data(0),aux(0)]
    ; findall(aux(I),(nth0(I,Ks,K),K \== p),Zeros) ),
    Packet = packet(Copies,Zeros).
public_object(Func, _, Object) :-
    Func = func(_,_,Ret,Ps,_), param_kinds(Ps,Ks),
    length(Ps,N), Need is 8*N, adapter_return(Ret,Result),
    ( variadic_func(Func)
    -> generic_params(Ks,Prefix),
       append(Prefix,[wf(l,snapshot),wf(l,snapshot)],Words),
       Object = generic_only(promote_incoming(Need,Words,Result))
    ; signature(Ret,Ks,Sig), generic_params(Ks,Words),
      Object = fast_and_generic(Sig,adapt(Need,Words,Result)) ).

lower_thunks(Module, Thunks) :-
    Module = module(Items),
    findall(t(F,Sig,Ret,Ks),
            (member(func(_,_,_,_,Bs),Items),member(block(_,_,Is,_),Bs),
             member(call(Res,global(F),Args),Is),
             direct_target(Module,F,unused,Target), Target = entry(F,unused),
             result_ret(Res,Ret),findall(K,member(arg(K,_),Args),Ks),
             signature(Ret,Ks,Sig0), call_symbol_signature(Res,Args,Sig0,Sig)), Ts0),
    sort(Ts0,Ts1), one_per_symbol(Ts1,Ts), maplist(lower_thunk,Ts,Thunks).
one_per_symbol([], []).
one_per_symbol([T|Ts0], [T|Ts]) :-
    T = t(F,Sig,_,_), exclude(same_symbol(F,Sig),Ts0,Ts1), one_per_symbol(Ts1,Ts).
same_symbol(F,Sig,t(F,Sig,_,_)).
lower_thunk(t(F,Sig,Ret,Ks), thunk(F,Sig,Words,Cells,ArgsSize,Result,Need)) :-
    findall(param(K,tmp(I)),nth0(I,Ks,K),Ps), fast_params(Ps,Words),
    thunk_cells(Ks,0,0,Cells),
    length(Ks,N), ArgsSize is 8*N,
    adapter_return(Ret,Result), ret_kinds(Ret,RKs), length(RKs,NR), Need is 8*NR.

% Native saves are indexed by flattened word, generic cells by value.
% The caller, not these saves, roots every incoming capability.
thunk_cells([], _, _, []).
thunk_cells([K|Ks], I, W, [cell(I,B,saved(W),Lower)|Cells]) :-
    payload_class(K,B),
    ( K == p -> L is W+1, Lower = saved(L), Next is W+2
    ; Lower = none, Next is W+1 ),
    I1 is I+1, thunk_cells(Ks,I1,Next,Cells).
