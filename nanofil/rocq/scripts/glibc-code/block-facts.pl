/* This command describes the explicit memory accesses and live temporaries of each block.
   The compiler's phi-aware liveness and flight analysis supply the data.
   Typed origins and completed C layouts name field accesses when possible.
   These source hints can guide symbolic execution, but they supply no safety evidence. */
:- use_module('../../../src/cfg').
:- use_module('../../../src/ir', [single_definitions/3, guard_chain/3, access_size_align/3]).
:- use_module('../../../src/provenance', [site_index/2, site_origins/3]).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(library(http/json)).
:- initialization(main, main).

main :-
    current_prolog_flag(argv, [File|Args]),
    access_args(Args, Names, Units),
    read_file_to_terms(File, [module(Items)], []),
    findall(Row,
            ( member(func(F, _, _, Ps, Bs), Items),
              ( Names == [] -> true ; memberchk(F, Names) ),
              ( memberchk(context(F, Rs), Items) -> true ; Rs = [] ),
              function_layouts(Units, F, Rs, Layouts), path_context(Rs, Ctx),
              temp_liveness(Bs, In, Out), single_definitions(Ps, Bs, Once),
              findall(Block,
                      ( member(block(L, _, Is, _), Bs),
                        get_assoc(L, In, LiveIn), get_assoc(L, Out, LiveOut),
                        findall(Access,
                                ( nth0(I, Is, Inst), memory_access(Inst, A, Off, Width, Read, Write),
                                  pointer(Once, A, P, Base), Offset is Base + Off,
                                  root(Once, P, Offset, Root, Distance), address(P, Address),
                                  access_path(Ctx, Layouts, L, I, P, Offset, Width, Root, Distance, Path),
                                  Access = _{index:I, address:Address, offset:Offset, width:Width,
                                             read:Read, write:Write, root:Root, root_offset:Distance,
                                             path:Path} ), Accesses),
                        Block = _{label:L, live_in:LiveIn, live_out:LiveOut, footprint:Accesses} ), Blocks),
              Row = _{function:F, blocks:Blocks} ), Rows),
    json_write_dict(current_output, Rows, [width(0)]), nl.

% Record identities are local to a translation unit. Match its unchanged
% context, not just its function name or a coincidentally equal record id.
access_args([], [], []).
access_args(['--unit', Spec|Args], Names, [unit(Obj, Items, Records)|Units]) :- !,
    atomic_list_concat([Obj, Code, Layout], '=', Spec),
    read_file_to_terms(Code, [module(Items)], []),
    read_file_to_terms(Layout, [layouts(Records, _)], []),
    access_args(Args, Names, Units).
access_args([Name|Args], [Name|Names], Units) :- access_args(Args, Names, Units).

function_layouts(Units, F, Rs, Records) :-
    findall(Defs,
            ( member(unit(Obj, Items, Defs), Units), member(context(N, Original), Items),
              (F == N ; atomic_list_concat([Obj, '#', N], F)), Original == Rs ), Candidates),
    sort(Candidates, Unique), ( Unique = [Records] -> true ; Records = [] ).

path_context(Rs, ctx(Origins, Children, Bindings, Values, Sites)) :-
    findall(Id-(D-Ps), member(origin(Id, _, D, Ps), Rs), Os), list_to_assoc(Os, Origins),
    findall(P-Id, (member(origin(Id, _, _, Ps), Rs), member(P, Ps)), Edges),
    keysort(Edges, Sorted), group_pairs_by_key(Sorted, Cs), list_to_assoc(Cs, Children),
    findall(Id-(N-T), member(binding(Id, N, T, _), Rs), Bs), list_to_assoc(Bs, Bindings),
    findall(V-(H-Ids), member(value(V, H, Ids), Rs), Vs), list_to_assoc(Vs, Values),
    site_index(Rs, Sites).

% A source member expression may use a cast to a different record type.
% Prefer a unique expression; otherwise resolve the actual root offset.
access_path(Ctx, Layouts, L, I, P, Offset, Width, Root, Distance, Path) :-
    findall(Text,
            ( root_object(Ctx, Root, Base, T), record_pointer(T, Id), integer(Distance),
              layout_path(Layouts, Id, Distance, Width, deref(Base), [], Field),
              path_text(Field, Text) ), Ls0), sort(Ls0, Ls),
    findall(Text,
            ( Offset =:= 0, integer(Width),
              source_access(Ctx, L, I, P, Field), path_text(Field, Text) ), Ss0), sort(Ss0, Ss),
    ( Ss = [Only] -> Path = Only
    ; Ls = [Only] -> Path = Only
    ; Ls = [_,_|_], intersection(Ls, Ss, [Only]) -> Path = Only
    ; Path = opaque ).

root_object(ctx(Os, Cs, Bs, Vs, Sites), Root, Path, T) :-
    get_assoc(Root, Vs, H-Ids), Ctx = ctx(Os, Cs, Bs, Vs, Sites),
    ( H = named(B, value), get_assoc(B, Bs, Name-T) -> Path = base(Name)
    ; H = named(B, address), get_assoc(B, Bs, Name-BT) -> Path = address(base(Name)), T = ptr(BT)
    ; findall(P-Type, (member(Id, Ids), node_path(Ctx, Id, [], P, Type)), Ps),
      sort(Ps, [Path-T]) ).

record_pointer(qualified(_, T), Id) :- !, record_pointer(T, Id).
record_pointer(ptr(T), Id) :- record_type(T, Id).
record_type(qualified(_, T), Id) :- !, record_type(T, Id).
record_type(struct(Id), Id).
record_type(union(Id), Id).

layout_path(Layouts, Id, Offset, Width, Base, Seen, Path) :-
    \+ memberchk(Id, Seen), integer(Width),
    memberchk(record(Id, _, def(_, _, _, _), Fields), Layouts),
    member(field(Name, T, Off, Size, _, _), Fields), Rest is Offset - Off,
    Rest >= 0, Rest + Width =< Size, field_path(Base, Name, Field),
    ( record_type(T, Inner)
    -> layout_path(Layouts, Inner, Rest, Width, Field, [Id|Seen], Path)
    ; Rest =:= 0, Path = Field ).

source_access(Ctx, _, _, tmp(P), Field) :-
    Ctx = ctx(_, _, _, Vs, _), get_assoc(P, Vs, _-Ids), member(Id, Ids),
    source_object(Ctx, Id, [], address, Field).
source_access(Ctx, L, I, _, Field) :-
    Ctx = ctx(_, _, _, _, Sites), site_origins(Sites, inst(L, I), Ids), member(Id, Ids),
    source_object(Ctx, Id, [], site, Field).

% A loaded field's value is not its address: reading through a buffer pointer
% must not be described as reading the pointer field itself.
source_object(Ctx, Id, Seen, Role, Field) :-
    \+ memberchk(Id, Seen), Ctx = ctx(Os, Cs, _, _, _), get_assoc(Id, Os, D-Ps),
    ( D = typed(obj, _, member(_)) -> node_path(Ctx, Id, [], Field, _)
    ; Role == site, D = typed(val, _, Op), (Op = load ; Op = assign(_)), get_assoc(Id, Cs, Children),
      member(Child, Children), get_assoc(Child, Os, typed(obj, _, member(_))-_)
    -> node_path(Ctx, Child, [], Field, _)
    ; D = generated(_, _), member(Parent, Ps), source_object(Ctx, Parent, [Id|Seen], Role, Field) ).

% Shallow typed nodes retain containment edges. Reconstruct only bindings,
% members and transparent loads/casts; arithmetic and subscripts stay opaque.
node_path(Ctx, Id, Seen, Path, T) :-
    \+ memberchk(Id, Seen), Ctx = ctx(Os, Cs, Bs, _, _),
    get_assoc(Id, Os, typed(_, T, Form)-_),
    ( Form = binding(B), get_assoc(B, Bs, Name-_) -> Path = base(Name)
    ; get_assoc(Id, Cs, Children),
      findall(C, (member(C, Children), get_assoc(C, Os, typed(_, _, _)-_)), [Child]),
      node_path(Ctx, Child, [Id|Seen], P, _),
      ( Form = member(Name) -> field_path(P, Name, Path)
      ; Form == deref -> Path = deref(P)
      ; memberchk(Form, [load, cast]) -> Path = P ) ).

field_path(deref(address(P)), Name, field(P, '.', Name)) :- !.
field_path(deref(P), Name, field(P, '->', Name)) :- !.
field_path(P, Name, field(P, '.', Name)).

path_text(base(Name), Name).
path_text(deref(P), Text) :- path_text(P, Base), atomic_list_concat(['(*', Base, ')'], Text).
path_text(field(P, Op, Name), Text) :-
    path_text(P, Base), atomic_list_concat([Base, Op, Name], Text).

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
