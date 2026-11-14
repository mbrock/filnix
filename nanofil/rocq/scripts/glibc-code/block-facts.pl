/* This command describes the explicit memory accesses and live temporaries of each block.
   The compiler's phi-aware liveness and flight analysis supply the data.
   These hints can guide symbolic execution, but they supply no safety evidence. */
:- use_module('../../../src/cfg').
:- use_module('../../../src/ir', [single_definitions/3, guard_chain/3, access_size_align/3]).
:- use_module(library(assoc)).
:- use_module(library(http/json)).
:- initialization(main, main).

main :-
    current_prolog_flag(argv, [File|Names]),
    read_file_to_terms(File, [module(Items)], []),
    findall(Row,
            ( member(func(F, _, _, Ps, Bs), Items),
              ( Names == [] -> true ; memberchk(F, Names) ),
              temp_liveness(Bs, In, Out), single_definitions(Ps, Bs, Once),
              findall(Block,
                      ( member(block(L, _, Is, _), Bs),
                        get_assoc(L, In, LiveIn), get_assoc(L, Out, LiveOut),
                        findall(Access,
                                ( nth0(I, Is, Inst), memory_access(Inst, A, Off, Width, Read, Write),
                                  pointer(Once, A, P, Base), Offset is Base + Off,
                                  root(Once, P, Offset, Root, Distance), address(P, Address),
                                  Access = _{index:I, address:Address, offset:Offset, width:Width,
                                             read:Read, write:Write, root:Root, root_offset:Distance} ), Accesses),
                        Block = _{label:L, live_in:LiveIn, live_out:LiveOut, footprint:Accesses} ), Blocks),
              Row = _{function:F, blocks:Blocks} ), Rows),
    json_write_dict(current_output, Rows, [width(0)]), nl.

memory_access(uses(I, _), A, Off, Size, Read, Write) :-
    memory_access(I, A, Off, Size, Read, Write).
memory_access(let(_, _, Op, [A]), A, Off, Size, true, false) :-
    ( Op = load(T), Off = 0
    ; Op = atomic_load(T), Off = 0
    ; Op = raw_load(T, Off)
    ; Op = raw_load_pointer(Off, _), T = p ), access_size_align(T, Size, _).
memory_access(store(T, _, A), A, 0, Size, false, true) :- access_size_align(T, Size, _).
memory_access(atomic_store(T, _, A), A, 0, Size, false, true) :- access_size_align(T, Size, _).
memory_access(raw_store(T, Off, _, A), A, Off, Size, false, true) :- access_size_align(T, Size, _).
memory_access(raw_store_pointer(Off, _, A, _), A, Off, 8, false, true).
memory_access(let(_, _, cas(T), [_, _, A]), A, 0, Size, true, true) :- access_size_align(T, Size, _).
memory_access(let(_, _, raw_cas(T, Off), [A, _, _]), A, Off, Size, true, true) :- access_size_align(T, Size, _).
memory_access(local_load(_, _, T, N, Off), local(N), Off, Size, true, false) :- access_size_align(T, Size, _).
memory_access(local_store(T, _, N, Off), local(N), Off, Size, false, true) :- access_size_align(T, Size, _).
memory_access(let(_, _, va_arg, [A]), A, 0, null, true, true).
memory_access(let(_, _, setjmp(_), [A, _]), A, 0, null, false, true).

pointer(Once, tmp(Q), P, Base) :-
    get_assoc(Q, Once, let(_, a, Op, Args)), !,
    ( Op = check_local(N, Base, _, _, _) -> P = local(N)
    ; ir:proof_pointer(Op, Args, P) -> Base = 0
    ; P = unresolved_proof(Q), Base = 0 ).
pointer(_, P, P, 0).

address(tmp(N), address{kind:tmp, name:N}) :- !.
address(global(N), address{kind:global, name:N}) :- !.
address(local(N), address{kind:local, name:N}) :- !.
address(unresolved_proof(N), address{kind:proof, name:N}) :- !.
address(const(N), address{kind:const, name:N}).

root(Once, P, Offset, Root, Distance) :-
    donor(Once, P, [], R),
    ( R = tmp(N)
    -> Root = N, guard_chain(Once, P, Chain),
       ( member(R-i(K, K), Chain) -> Distance is Offset + K ; Distance = null )
    ; Root = null, Distance = null ).

donor(Once, tmp(N), Seen, Root) :-
    \+ memberchk(N, Seen), get_assoc(N, Once, flight(_, _, _, lower(P))), !,
    donor(Once, P, [N|Seen], Root).
donor(_, P, _, P).
