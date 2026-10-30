/*  The Fil-C backend for x86-64: filc_abi.pl lowers checked functions
    to frame, call and entry products; this module places their words
    and emits asm.pl lines whose GNU as text links with code clang builds
    for filnix staging Fil-C 0.687. Checked pointer-memory emission remains
    here, as does global-data serialization and getter initialization.

    Every rule is chosen to be easy to check, not fast; docs/m3.md has
    them in full.

    ## The frame

    Each temporary has an 8-byte slot below %rbp, except a check's
    proof, which stays in %rax:%rcx for the access fused with it. A `p`
    temporary's slot holds its address; its lower lives in a `lowers[]`
    entry of the function's filc_frame, which the prologue pushes on
    `thread->top_frame` and every return and exception exit pops.
    Values are never kept in registers across a call or safepoint, so
    every live capability is always in a slot the GC scans. The prologue
    zeroes `lowers[]`, so the GC sees no stale lowers. Only function,
    operands and cells modes (amd64_regs.pl; cells is the -O default) keep
    scalar `w`/`l` homes in registers, callee-saved ones across calls;
    pointers never.

    Temporaries whose closed live intervals are disjoint share a slot
    (frame_slots.pl). A function that calls setjmp is the exception:
    each of its temporaries gets a slot of its own.

    ```diagram
    ┌────────────────────────────┐ ← %rbp
    │ 8-byte slots: temporaries, │   -8, -16, …
    │ phi shadows, thread, aux,  │
    │ retbuf, jmp_buf pointers   │
    ├────────────────────────────┤
    │ lowers[NLowers-1]          │
    │ …                          │
    │ lowers[0]                  │   -FrameBase+16
    ├────────────────────────────┤
    │ origin                     │   -FrameBase+8
    │ parent                     │   -FrameBase
    ├────────────────────────────┤
    │ padding to 16 bytes        │
    └────────────────────────────┘ ← %rsp = %rbp - Size
    ```

    ## Instructions

    - The IR must be checked (ir.pl, pizlonate.pl): each check comes
      right before the raw access or call it covers, and the two are
      emitted as one instruction, `fused(Check, Access)`: the check's
      sequence, then the operation. Function identity checks come from
      `check_function`, not from inferring that an indirect call needs one.
      A later scalar access that reuses a heap proof (docs/m7.md) is
      `reused(Access)`: the access at the checked pointer, reloaded from
      its slot, plus the access's offset (a related pointer's distance),
      without a check.
    - Pointer loads and stores go through the object's aux array; a
      pointer store ensures the aux array and runs the store barrier.
    - `flight` supplies its address calculation and lower source
      separately. Emission preserves neither by inference from a `p`
      arithmetic operation; pizlonation has already chosen both.
    - `alloc` is a heap allocation.
    - An edge to `poll(L)` runs a pollcheck: a call of
      filc_pollcheck_slow when the thread's state asks for one.
    - Scalar integer and SSE2 instructions share amd64:compute_op//5.
      Local mode selects integer immediates before scalar stack caching.
    - Float bits have no lower. At ABI boundaries they travel in XMM
      registers, or in generic payload words with zero aux
      (docs/abi-findings.md).

    ## Calls and entries

    Calls use the fast convention: the thread, the callee's lower, then
    the argument words (a buffered return passes its buffer first). A
    function that throws pops its frame and returns has_exception = 1,
    in %al or in the return buffer; a caller that sees it propagates it
    the same way.

    Origins preserve the existing can_throw=0: exception flags propagate,
    but the runtime will not unwind a C++ exception through this frame.

    Every function gets a getter, a function object and a generic entry,
    so its address can be taken; an exported one also gets the global
    alias for its signature and a global getter, so clang code can call
    it directly or indirectly.

    ## Variable conventions

    | Variable | Means |
    |---|---|
    | Ctx | the function context (function_ctx/8) |
    | Fn | the amd64 context inside Ctx |
    | K | a word class: `w`, `l`, `p`, `s` or `d` |
    | V | a value, `tmp(N)` or `const(N)` |
    | D | the number of a destination `tmp(D)` |
    | T | a load type |
    | W | a store width |
    | S, F | symbols |
    | Off | a byte offset |
    | Form | a placed return form, `reg` or `mem(Bytes)` (target_form/2) |
*/
:- module(filc_amd64, [filc_module_asm/2, filc_module_asm/4, filc_module_emit/3,
                       signature/3]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(ir).
:- use_module(amd64).
:- use_module(amd64_regs).
:- use_module(amd64_regs_check, [callee_saved/1]).
:- use_module(filc_abi).
:- use_module(cfg, [edge_label/2, inst_def/2]).

%! filc_module_asm(+Module, -Lines) is det.
%
%  Lines is the asm.pl line list of IR module Module for the Fil-C ABI:
%  each item's code and data, a weak thunk for each function the module
%  calls but does not define, and the GNU-stack note. Throws
%  nanofil_error(Msg) if an item cannot be lowered.
filc_module_asm(Module, Lines) :- filc_module_asm(Module, stack, Lines, _).

% Emission is emit(Registers, Branches), or just Registers with reference
% branches. Registers is stack (the reference) or temps (validated
% whole-function register homes, amd64_regs.pl, with validated register
% operands and frame cells, on a frame with a home per scalar temporary:
% docs/perf.md items 3, 5a-loads and 3d); Branches is reference or
% selected (branch selection, below). emit(Registers, Branches, Copies)
% also gives Copies: call (the reference) or inline, the small-copy
% filter of docs/perf.md item 7a; emit/2 means call.
% Reports records each item's caching result, without driver-side state.
filc_module_asm(Module0, Emission, Lines, Reports) :-
    without_locs(Module0, Module),
    Module = module(Items),
    emission(Emission, Registers, Branches),
    % Lower and place each item in one committed step, so a large
    % module (SQLite) never holds every item's ABI product at once.
    module_symbols(Module, Symbols),
    maplist(item_placed_lines(Symbols, Registers, Branches), Items, LinesPerItem, Reports),
    lower_thunks(Module, Callees),
    append(LinesPerItem, ItemLines),
    maplist(thunk_lines, Callees, LinesPerThunk),
    append(LinesPerThunk, ThunkLines),
    append([ItemLines, ThunkLines, [section(note_gnu_stack)]], Lines).

emission(emit(Registers, Branches, Copies), Registers, choices(Branches, Copies)) :- !.
emission(emit(Registers, Branches), Registers, Branches) :- !.
emission(Registers, Registers, reference).

item_placed_lines(Symbols, _, _, alias(Name, Linkage, Target), Lines, data(Name)) :- !,
    phrase(alias_getter(Symbols, Name, Linkage, Target), Lines).
% limited(Registers, Limit): Registers (temps or pointers) for a
% function of at most Limit instructions, and the reference emission for
% a larger one (main.pl's --registers-limit).
item_placed_lines(Symbols, limited(Registers0, Limit), Branches, Item, Lines, Report) :- !,
    (   Item = func(_, _, _, _, Blocks),
        foldl(block_insts, Blocks, 0, Size), Size > Limit
    ->  Registers = stack
    ;   Registers = Registers0
    ),
    item_placed_lines(Symbols, Registers, Branches, Item, Lines, Report).
item_placed_lines(Symbols, Registers, Branches, Item, Lines, Report) :-
    % The allocating modes keep float temporaries out of the scalar
    % slots (frame_slots:temp_slots/9), so integer homes stay eligible.
    % Temps mode also gives each w/l temporary its own home (docs/perf.md 3d).
    % It lowers twice: once with every w/l temporary in a home of its own,
    % then with the temporaries pooled by where the first allocation put
    % them: those left in the frame together, and those given a register
    % with the others given the same one, so the frame stays compact.
    % Both are layout choices; the checkers validate the emitted stream.
    % Pointers mode is temps with pointer address words as homes too
    % (docs/perf.md 5b-2).
    (   memberchk(Registers, [temps, pointers])
    ->  temps_first(Registers, Symbols, Branches, Item, First),
        (   First = placed(Lines, Report) -> true
        ;   First = again(Groups, Fused, Ranges),
            % The first lowering is garbage now; collect it before the
            % second grows the stacks, in large functions only (SQLite's
            % largest): collecting before every function costs far more.
            (   length(Groups, NG), NG > 1024
            ->  catch(garbage_collect, error(existence_error(_, _), _), true)
            ;   true
            ),
            once(lower_fused(own(Groups, Ranges), Symbols, Fused, Product)),
            once(placed_lines(temps(Registers), Branches, Item, Product, Lines, Report, _))
        )
    ;   once(( lower_item(shared, Symbols, Item, Product),
               placed_lines(Registers, Branches, Item, Product, Lines, Report) ))
    ).

block_insts(block(_, _, Is, _), N0, N) :- length(Is, K), N is N0 + K.

% temps_first(+Homes, +Symbols, +Branches, +Item, -First): temps mode's first
% lowering, with a home per w/l temporary. First is placed(Lines,
% Report) when it has at most own_frame_limit/1 such homes, else
% again(Groups, Fused, Ranges) with each temporary's group for the
% second lowering, from a function-mode (3a) allocation of the first,
% and the fused blocks and live ranges the second reuses (the groups
% change only which slots the ranges share); the first's lines are
% dropped, so the second lowering does not hold them. Homes is temps or
% pointers, as for placed_lines/7.
temps_first(Homes, Symbols, Branches, Item, First) :-
    fused_item(Item, Fused),
    once(lower_fused(own([], Ranges), Symbols, Fused, Product)),
    own_frame_limit(Limit),
    (   Product = abi_function(_,_,_,_,frame(_,_,Aliases),_,_,_,_,_),
        findall(x, member(_-storage(scalar,_), Aliases), Xs), length(Xs, N), N > Limit
    ->  % Only the register map matters here: 3a's allocation, unchecked
        % because these lines are dropped, and no operand rewrite.
        once(placed_lines(map(Homes), Branches, Item, Product, _, _, Groups)),
        First = again(Groups, Fused, Ranges)
    ;   once(placed_lines(temps(Homes), Branches, Item, Product, Lines, Report, _)),
        First = placed(Lines, Report)
    ).

% own_frame_limit(-N): own scalar homes (512 bytes) worth a second
% lowering to share their slots (docs/perf.md 3d).
own_frame_limit(16).

%! filc_module_emit(+Module, +Emission, :Emit) is det.
%
%  Calls Emit(Lines) for each part of the lines filc_module_asm/4 gives,
%  in order, so a large module (SQLite) need not hold all its lines.
filc_module_emit(Module0, Emission, Emit) :-
    % A last call after deterministic goals: the frame holding Module0
    % and its provenance contexts (170 MB for SQLite) is dropped.
    once(without_locs(Module0, Module)),
    emission(Emission, Registers, Branches),
    module_emit(Module, Registers, Branches, Emit).

module_emit(Module, Registers, Branches, Emit) :-
    Module = module(Items),
    % Validation leaves SWI's heap near its peak; collecting once here,
    % with only 130 MB live for SQLite, keeps emission within 1 GB.
    catch(garbage_collect, error(existence_error(_, _), _), true),
    module_symbols(Module, Symbols),
    forall(member(Item, Items),
           ( item_placed_lines(Symbols, Registers, Branches, Item, Lines, _),
             call(Emit, Lines) )),
    lower_thunks(Module, Callees),
    forall(member(Callee, Callees),
           ( thunk_lines(Callee, Lines), call(Emit, Lines) )),
    call(Emit, [section(note_gnu_stack)]).

thunk_lines(Callee, Lines) :-
    phrase(thunk(Callee), Lines).

% Complete the ABI product before any instruction selection. Fusion is
% still target preparation; its separate liveness view preserves indices.
lower_item(Pools, Symbols, Item, Product) :-
    fused_item(Item, Fused), lower_fused(Pools, Symbols, Fused, Product).

fused_item(func(N,L,R,Ps,Bs0), fused(func(N,L,R,Ps,Bs), Live)) :-
    fused_blocks(N, Ps, Bs0, Bs, Live).
fused_item(data(N,L,A,Is), data(N,L,A,Is)).

lower_fused(Pools, Symbols, fused(Func, Live), Product) :-
    lower_function(Pools, Symbols, Func, Live, Product).
lower_fused(_, _, data(N,L,A,Is), data(N,L,A,Is)).

item_lines(Selection, Item, Lines) :-
    (   phrase(item(Selection,Item), Lines) -> true
    ;   arg(1, Item, Name),
        format(atom(Msg), 'Fil-C backend cannot emit ~w', [Name]),
        throw(nanofil_error(Msg))
    ).

% placed_lines(+Registers, +Branches, +Item, +Product, -Lines, -Report,
% -Groups): Registers is stack, temps(Homes) or map(Homes), Homes being
% temps (scalar homes) or pointers (pointer address words too). Groups
% pairs each temporary in a scalar home with the register the map gave
% the home, or frame, for temps mode's second lowering; [] for data and
% the non-allocating modes.
placed_lines(R, Br, Item, Product, Lines, Report) :-
    placed_lines(R, Br, Item, Product, Lines, Report, _).

% A setjmp function keeps reference selection, branches included.
placed_lines(stack, Branches, Func, Item, Lines, stack, []) :-
    ( setjmp_func(Func) -> B = reference ; B = Branches ),
    item_lines(sel(stack,B),Item,Lines).
placed_lines(temps(_), _, data(N,L,A,Is), Item, Lines, data(N), []) :-
    Item = data(N,L,A,Is), item_lines(sel(stack,reference),Item,Lines).
% Temps mode reserves a save slot for each callee-saved register, so
% the stream the checker compares with has the same frame. Map is temps
% mode's first lowering when it only needs the register map.
placed_lines(Mode, Branches, Func, Item0, Lines, function(Name,Report), Groups) :-
    ( Mode = temps(HomeKind) -> true ; Mode = map(HomeKind) ),
    Func = func(Name,_,_,_,_),
    Item0 = abi_function(Name,Lk,Rt,Sig,frame(Plain,Lowers,Aliases),E,B,X,O,Or),
    (   setjmp_func(Func)
    ->  Setjmp = true, Selection = sel(stack,reference), Item = Item0
    ;   Setjmp = false, Selection = sel(local,Branches),
        findall(callee_save(R), callee_saved(R), Extra),
        append(Plain, Extra, Plain1),
        Item = abi_function(Name,Lk,Rt,Sig,frame(Plain1,Lowers,Aliases),E,B,X,O,Or)
    ),
    item_lines(Selection,Item,Original),
    abi_symbol(impl(Sig),Name,Impl),
    once(append(Body,[size(Impl)|Rest],Original)),
    Item = abi_function(_,_,_,_,Frame,_,_,_,_,_),
    layout(Frame,Slots,FrameBase,_),
    scalar_homes(Func, Aliases, Slots, Homes0),
    % Phi shadows are homes too. Phis of different blocks may share a
    % shadow slot (filc_abi.pl's shadow_storage/8): one home each, with
    % the classes of the phis sharing it. A pointer phi's shadow is its
    % address word, of class p, or a in pointers mode.
    Func = func(_,_,_,_,Bs),
    findall(D-K, ( member(block(_,Phis,_,_),Bs), member(phi(tmp(N),K0,_),Phis),
                   home_class(HomeKind, K0, K),
                   get_assoc(shadow(N),Slots,Off), D is -Off ), DKs0),
    sort(DKs0, DKs), group_pairs_by_key(DKs, ShadowGroups),
    findall(home(D,Ks), member(D-Ks, ShadowGroups), Shadows),
    % Pointers mode: each pointer pool slot's address word is a home of
    % class a; its lower stays in lowers[] (docs/perf.md 5b-2).
    findall(home(D,[a]), ( HomeKind == pointers,
                           gen_assoc(storage(pointer,_), Slots, Off), D is -Off ), Pointers),
    % The GC roots, which no home may overlap: the frame record (parent,
    % origin and lowers[], stack-aux and jmpbuf roots included) and each
    % local object's payload and aux words.
    Frame = frame(_,Lowers1,_), length(Lowers1, NLowers),
    RecordD is -FrameBase, RecordN is 16 + 8*NLowers,
    findall(root(D,N), ( gen_assoc(local(L), Slots, V), other_range(local(L), V, D, N) ), Locals),
    append([Homes0, Shadows, Pointers, [root(RecordD,RecordN)|Locals]], Homes),
    findall(save(R,D), ( callee_saved(R), get_assoc(callee_save(R),Slots,Off),
                         D is -Off ), Saves),
    regs_mode(Mode, Slots, Mode1),
    regs_asm(Mode1,regs_metadata(Setjmp,Impl,Homes,Saves),Body,Allocated,
             checked(_,Map),Report),
    append(Allocated,[size(Impl)|Rest],Lines),
    ( Map == [] -> empty_assoc(Mapped) ; list_to_assoc(Map, Mapped) ),
    findall(N-G, ( member(tmp(N)-storage(scalar,I), Aliases),
                   get_assoc(storage(scalar,I), Slots, Off), D is -Off,
                   ( get_assoc(D, Mapped, R) -> G = R ; G = frame ) ), Groups0),
    sort(Groups0, Groups).

% regs_mode(+Mode, +Slots, -Mode1): temps mode allocates with register
% operands and the frame cells (docs/perf.md, 5a-loads): the 8-byte words of lowers[],
% the scalar and pointer pools, phi shadows, thread, aux, retbuf, and
% stack-aux roots, as cells(Ds, Others) with the other frame ranges
% (local storage, wide slots, save slots) the checker keeps them apart
% from. The header words (parent, origin) are never cells.
regs_mode(temps(_), Slots, frame(cells(Ds, Others))) :- !,
    assoc_to_list(Slots, Ps),
    findall(D, ( member(K-Off, Ps), integer(Off), cell_key(K), D is -Off ), Ds0),
    sort(Ds0, Ds),
    findall(D-N, ( member(K-V, Ps), other_range(K, V, D, N) ), Others).
regs_mode(map(_), _, map).

% home_class(+Homes, +Class0, -Class): a pointer phi's shadow is a home
% of class a (its address word) in pointers mode, and of class p, which
% no allocation takes, otherwise.
home_class(pointers, p, a) :- !.
home_class(_, K, K).

cell_key(lower(_)).
cell_key(storage(scalar,_)).
cell_key(storage(float,_)).
cell_key(storage(pointer,_)).
cell_key(shadow(_)).
cell_key(shadow_slot(_,_)).
cell_key(thread).
cell_key(aux).
cell_key(retbuf).
cell_key(stack_aux(_)).

other_range(local(_), local(Payload, Aux, _, Padded), D, N) :-
    D is -Aux, N is Aux - Payload + Padded.
other_range(storage(wide,_), Off, D, 16) :- D is -Off.
other_range(callee_save(_), Off, D, 8) :- D is -Off.

% scalar_homes(+Func, +Aliases, +Slots, -Homes): home(Disp, Classes) for
% each scalar-pool slot, with the classes of the temporaries sharing it.
scalar_homes(func(_,_,_,Ps,Bs), Aliases, Slots, Homes) :-
    findall(T-K, (member(param(K,T),Ps)
                ; member(block(_,Phis,Is,_),Bs),
                  ( member(phi(T,K,_),Phis)
                  ; member(I,Is), cache_temp_class(I,T,K) )), Types0),
    sort(Types0,Types1), list_to_assoc(Types1,Types),
    findall(Key-K, (member(T-Key,Aliases), Key = storage(scalar,_),
                    ( get_assoc(T,Types,K0) -> K = K0 ; K = unknown )), Uses),
    keysort(Uses,Sorted), group_pairs_by_key(Sorted,Groups),
    findall(home(D,Ks),
            (member(Key-Ks,Groups), get_assoc(Key,Slots,Off), D is -Off), Homes).

cache_temp_class(let(T,K,_,_),T,K).
cache_temp_class(local_load(T,K,_,_,_),T,K).
cache_temp_class(call(result(T,K),_,_),T,K).
cache_temp_class(raw_call(result(T,K),_,_),T,K).
cache_temp_class(call(tuple(Rs),_,_),T,K) :- member(result(T,K),Rs).
cache_temp_class(raw_call(tuple(Rs),_,_),T,K) :- member(result(T,K),Rs).

%% ABI facts (docs/abi-findings.md), at the pin

% abi_symbol(+Role, +F, -Symbol): Symbol is the name under which code
% finds Role of the function or global F: its implementation (the fast
% entry) and FI alias for signature Sig, its getter, its function object,
% or its data object and aux array.
abi_symbol(impl(Sig), F, S) :- format(atom(S), 'pizlonatedFIP~w_~w', [Sig, F]).
abi_symbol(entry(never(R-A)), F, S) :- !,
    format(atom(S), 'pizlonatedFIN~w_~w_~w', [R, A, F]).
abi_symbol(entry(Sig), F, S) :- format(atom(S), 'pizlonatedFI~w_~w', [Sig, F]).
abi_symbol(getter, F, S) :- format(atom(S), 'pizlonated_~w', [F]).
abi_symbol(function_object, F, S) :- format(atom(S), 'pizlonatedFO_~w', [F]).
abi_symbol(data_object, F, S) :- format(atom(S), 'pizlonatedDO_~w', [F]).
abi_symbol(data_aux, F, S) :- format(atom(S), 'pizlonatedDA_~w', [F]).

% field(+Struct, +Field, +Base, -Mem): Mem is the operand of Field of the
% Struct whose address is in register Base. A function object's fields
% are at its lower.
field(Struct, Field, Base, mem(Off, Base)) :-
    struct_field(Struct, Field, Off).

struct_field(thread, stack_limit, 0).
struct_field(thread, state, 8).
struct_field(thread, top_frame, 16).
struct_field(thread, cc_inline_buffer, 128).
struct_field(thread, cc_inline_aux_buffer, 384).
struct_field(thread, cc_outline_buffer, 640).
struct_field(thread, cc_outline_aux_buffer, 648).
struct_field(thread, cc_outline_size, 656).
struct_field(function_object, fast_entry, 0).
struct_field(function_object, generic_entry, 8).
struct_field(function_object, signature, 16).

% aux_bits(+Flags, -Bits): Bits are the flags Flags in an aux word, whose
% low 48 bits are the aux pointer (aux_pointer_mask/1) and whose high 16
% the flags. The special type is a field of the flags.
aux_bits(Flags, Bits) :-
    foldl(flag_or, Flags, 0, Sum),
    Bits is Sum << 48.

flag_or(Flag, Sum0, Sum) :-
    object_flag(Flag, Bit),
    Sum is Sum0 \/ Bit.

object_flag(global, 0x1).
object_flag(readonly, 0x2).
object_flag(global_aux, 0x10).       % the aux array is static data
object_flag(function, 0x80).         % special type 1, function
object_flag(special_type, 0x780).    % the special type field, bits 7-10

aux_pointer_mask(0xffffffffffff).

%% Frame layout

% Place the already chosen payloads, roots and aliases below %rbp.
layout(frame(Plain, Lowers, Aliases), Slots, FrameBase, Size) :-
    length(Lowers, NLowers),
    empty_assoc(Slots0),
    foldl(plain_slot, Plain, Slots0-0, Slots1-PlainBytes),
    FrameBase is PlainBytes + 16 + 8 * NLowers,
    foldl(lower_slot(FrameBase), Lowers, Slots1-0, Slots2-_),
    % One assoc from all the keys, not an insertion per alias (a fifth
    % of the frame's cost for SQLite). put_assoc would let a later alias
    % replace a key; list_to_assoc refuses duplicates, which no frame has.
    assoc_to_list(Slots2, Placed),
    findall(T-Off, ( member(T-Key, Aliases), get_assoc(Key, Slots2, Off) ), AliasSlots),
    append(Placed, AliasSlots, All),
    list_to_assoc(All, Slots),
    Size is (FrameBase + 15) // 16 * 16.

% Named object storage is not a temporary slot and is never reused.
% Payload is 16-aligned; aux is a count header followed by lower words.
plain_slot(local(Name, Size), Slots0-Off0, Slots-End) :- !,
    Padded is (Size + 15) // 16 * 16,
    Payload is (Off0 + Padded + 15) // 16 * 16,
    Aux is Payload + Padded + 8, End = Aux,
    put_assoc(local(Name), Slots0, local(Payload, Aux, Size, Padded), Slots).
% A long double temporary's wide slot is 16 bytes, 10 of them used.
plain_slot(storage(wide, I), Slots0-Off0, Slots-Off) :- !,
    Off is Off0 + 16,
    put_assoc(storage(wide, I), Slots0, Off, Slots).
plain_slot(Key, Slots0-Off0, Slots-Off) :-
    Off is Off0 + 8,
    put_assoc(Key, Slots0, Off, Slots).

% lower_slot(+FrameBase, +Key, +Slots0-I0, -Slots-I): Slots maps Key to
% lowers[I0] of the filc_frame at -FrameBase(%rbp).
lower_slot(FrameBase, Key, Slots0-I0, Slots-I) :-
    Off is FrameBase - 16 - 8 * I0,
    I is I0 + 1,
    put_assoc(Key, Slots0, Off, Slots).

%% The function context

/* function_ctx(+Name, +Ret, +Slots, +Blocks, +Size, +FrameBase, +Selection, -Ctx):
   Ctx = ctx(Fn, Size, FrameBase, Labels, Selection) is the context of function
   Name, where Fn = f(Name, Ret, Slots, Blocks) is the context amd64's
   load//4 and compute_op//4 take. Labels maps each block label to its
   phis, so an edge finds them without searching Blocks. */
function_ctx(Name, Ret, Slots, Blocks, Size, FrameBase, sel(Imm, B0), Ctx) :-
    findall(Label-Phis, member(block(Label, Phis, _, _), Blocks), LabelBlocks),
    list_to_assoc(LabelBlocks, Labels),
    ( B0 = choices(B, Copies) -> true ; B = B0, Copies = call ),
    branch_selection(B, Blocks, Branches),
    Ctx = ctx(f(Name, Ret, Slots, Blocks), Size, FrameBase, Labels,
              sel(Imm, Branches, Copies)).

ctx_fn(ctx(Fn, _, _, _, _), Fn).

ctx_name(ctx(f(Name, _, _, _), _, _, _, _), Name).

ctx_size(ctx(_, Size, _, _, _), Size).

ctx_frame_base(ctx(_, _, FrameBase, _, _), FrameBase).

ctx_labels(ctx(_, _, _, Labels, _), Labels).

% Immediate selection: stack (the reference) or local.
ctx_selection(ctx(_, _, _, _, sel(Selection, _, _)), Selection).

% Branch selection: reference, or selected(Uses) (branch selection).
ctx_branches(ctx(_, _, _, _, sel(_, Branches, _)), Branches).

% Small constant copies: call (the reference) or inline (item 7a).
ctx_copies(ctx(_, _, _, _, sel(_, _, Copies)), Copies).

% ctx_slot(+Ctx, +Key, -Off): Key's slot is at -Off(%rbp).
ctx_slot(ctx(f(_, _, Slots, _), _, _, _, _), Key, Off) :-
    get_assoc(Key, Slots, Off).

% The store of register Reg into Key's slot.
reg_slot_store(Reg, Key, Ctx) -->
    { ctx_slot(Ctx, Key, Off),
      Disp is -Off },
    [ins(mov, q, [reg(Reg), mem(Disp, rbp)])].

% The load of Key's slot into register Reg.
slot_reg_load(Key, Reg, Ctx) -->
    { ctx_slot(Ctx, Key, Off),
      Disp is -Off },
    [ins(mov, q, [mem(Disp, rbp), reg(Reg)])].

%% Local labels: A is the label atom in each relation.

% A label shared by the whole function, e.g. exc for exception exits.
special_label(Ctx, Tag, A) :-
    ctx_name(Ctx, Name),
    label_atom(['.L', Name, '..', Tag], A).

% The label of the block named Label.
block_label(Ctx, Label, A) :-
    ctx_name(Ctx, Name),
    label_atom(['.L', Name, '.', Label], A).

% A label inside the code of instruction Index (or a jump) in Block.
local_label(Ctx, Block, Index, Tag, A) :-
    ctx_name(Ctx, Name),
    label_atom(['.L', Name, '.', Block, '..', Index, '.', Tag], A).

% label_atom(+Parts, -A): A is the parts' text, as format's ~w writes
% them; atomic_list_concat/2 is several times faster than format/3,
% which was a twentieth of emission for SQLite.
label_atom(Parts, A) :-
    (   maplist(atomic, Parts) -> atomic_list_concat(Parts, A)
    ;   length(Parts, N), length(Ws, N), maplist(=('~w'), Ws),
        atomic_list_concat(Ws, Format), format(atom(A), Format, Parts)
    ).

% The frame's origin: c (calls, can_catch) or n (pollchecks and checks).
origin_label(Name, Which, A) :-
    format(atom(A), '.L~w..origin_~w', [Name, Which]).

%% Functions

% The lines of a module item, a function or a data object.
item(Selection, Func) -->
    { Func = abi_function(_, _, _, _, _, _, _, _, _, _) },
    function(Selection, Func).
item(_, data(Name, tls(Linkage), Align, Items)) --> !,
    thread_local_object(Name, Linkage, Align, Items).
item(_, data(Name, init(Kind, Prio), _, [item(p, sym(F, 0))])) --> !,
    init_entry(Name, Kind, Prio, F).
item(_, data(Name, extern(weak), _, [])) --> !,
    { abi_symbol(getter, Name, Getter) }, [weak(Getter)].
item(_, data(Name, Linkage, Align, Items)) -->
    data_object(Name, Linkage, Align, Items).

% A constructor or destructor table entry (ir.pl's init linkage), as
% clang's Fil-C emits one: a native forwarder in the .init_array or
% .fini_array section, which hands F's function object to the runtime
% (filc_defer_or_run_global_ctor or filc_run_global_dtor) to call.
init_entry(Name, Kind, Prio, F) -->
    { abi_symbol(function_object, F, FO),
      format(atom(Forwarder), '.L~w..forwarder', [Name]),
      init_runtime(Kind, Run) },
    [section(text), p2align(4), type(Forwarder, function), label(Forwarder),
     ins(lea, q, [rip(FO+16), reg(rdi)]),
     ins(mov, q, [reg(rdi), reg(rsi)]),
     ins(jmp, none, [plt(Run)]),
     section(init(Kind, Prio)), p2align(3), quad(Forwarder)].

init_runtime(ctor, filc_defer_or_run_global_ctor).
init_runtime(dtor, filc_run_global_dtor).

% A function: its implementation (prologue, blocks, the shared exception
% exit and failure blocks), then its function object and origins.
function(Selection, abi_function(Name, Linkage, Ret, Sig, Frame, Entry, Blocks,
                                 Exit, Object, Origins)) -->
    { layout(Frame, Slots, FrameBase, Size),
      function_ctx(Name, Ret, Slots, Blocks, Size, FrameBase, Selection, Ctx),
      abi_symbol(impl(Sig), Name, Impl),
      access_check_kinds(Blocks, CheckKinds),
      special_label(Ctx, exc, Exc) },
    [section(text), p2align(4)],
    linkage_globl(Linkage, Impl),
    [type(Impl, function), label(Impl)],
    abi_actions(Entry, entry, entry, Ctx),
    blocks(Blocks, Ctx),
    [label(Exc)],
    abi_actions(Exit, exit, exit, Ctx),
    check_fail_blocks(CheckKinds, Ctx),
    guard_slow_blocks(Blocks, Ctx),
    not_function_block(Blocks, Ctx),
    unreachable_block(Blocks, Ctx),
    [size(Impl)],
    body_function_object(Object, Name, Linkage, Impl),
    origins(Name, Origins, CheckKinds),
    unreachable_message(Blocks, Name).

/* fused_blocks(+Fn, +Params, +Blocks0, -Blocks, -LiveBlocks): Blocks are the
   checked Blocks0 with each check and the raw access after it, which
   reads its proven address, fused into fused(Check, Access) at one index,
   so labels and frame slots number instructions as they did before
   checks were explicit. Access reads the checked pointer P itself: a
   proof is a register value (%rax:%rcx after the check) and needs no
   slot. LiveBlocks have the bare accesses, for liveness and layout,
   which so keep P live through the access, as the reload after
   ensure-aux needs. Function proofs fuse with raw_call in the same way:
   the original pointer and all arguments stay live through the call,
   and neither proof gets a frame slot. Throws unless the IR is checked
   and every cycle polls. */
fused_blocks(Fn, Params, Blocks0, Blocks, LiveBlocks) :-
    (   polls_every_cycle(Blocks0) -> true
    ;   throw_fn(Fn, 'a cycle without a poll edge; run pizlonate first')
    ),
    single_proofs(Params, Blocks0, Single),
    maplist(fused_block(Fn, Single), Blocks0, Blocks),
    maplist(live_block, Blocks, LiveBlocks).

fused_block(Fn, Single, block(L, Phis, Insts0, Jump), block(L, Phis, Insts, Jump)) :-
    proofs_empty(Proofs),
    fused_insts(Insts0, Fn, Single, Proofs, Insts).

% single_proofs(+Params, +Blocks, -Single): Q-P for each heap check of P
% defining tmp(Q) where Q has one definition in the function and P at
% most one, counting parameters and phis. Only these may be reused in
% another block: with strict SSA, reloading P there gives the value
% that was checked.
single_proofs(Params, Blocks, Single) :-
    temp_defs(Params, Blocks, Defs0),
    pairs_keys(Defs0, Names), msort(Names, Sorted),
    multiply_defined(Sorted, Multi0), sort(Multi0, Multi),
    findall(N-true, member(N, Multi), MultiPairs), list_to_assoc(MultiPairs, MultiSet),
    findall(Q-P, ( member(block(_, _, Is, _), Blocks),
                   member(let(tmp(Q), a, Op, [P|_]), Is),
                   ( Op = check(_, _, _, _) ; Op = renew_if(_, _, _, _) ),
                   \+ get_assoc(Q, MultiSet, _),
                   ( P = tmp(N) -> \+ get_assoc(N, MultiSet, _) ; true ) ),
            Checks),
    % A renew's proof stands for its own pointer P, the replaced check's
    % (docs/m7.md, round 4 addendum), when Q and P have one definition.
    list_to_assoc(Checks, CheckAssoc),
    findall(Q-P, ( member(block(_, _, Is, _), Blocks),
                   member(let(tmp(Q), a, renew(_, _, _, _), [tmp(Q1), P]), Is),
                   \+ get_assoc(Q, MultiSet, _),
                   get_assoc(Q1, CheckAssoc, _),
                   ( P = tmp(N) -> \+ get_assoc(N, MultiSet, _) ; true ) ),
            Renews),
    append(Checks, Renews, Single0),
    % Q has one definition, so each key occurs once.
    list_to_assoc(Single0, Single).

% multiply_defined(+Sorted, -Names): the names that occur twice or more.
multiply_defined([], []).
multiply_defined([N, M|Ns], [N|Ds]) :- N == M, !, multiply_defined([M|Ns], Ds).
multiply_defined([_|Ns], Ds) :- multiply_defined(Ns, Ds).

% fused_insts(+Insts0, +Fn, +Single, +Proofs, -Insts): Proofs are Q-P
% for the block's heap checks so far, Single those of the function that
% may be reused in another block. A later scalar access at one of them
% is reused(Access) at P, with no check, at its offset from P (nonzero
% for a related pointer, round 3): validation (ir.pl, docs/m7.md)
% has established that its evidence still holds, which is not repeated
% here. Its liveness view reads P, so P keeps its rooted slot.
fused_insts([], _, _, _, []).
fused_insts([Inst0|Insts0], Fn, Single, Proofs0, [Inst|Insts]) :-
    % Emission reloads P from its slot where the interpreter reads the
    % value Q captured: forget a pair once either name is redefined.
    (   inst_def(Inst0, D)
    ->  proofs_kill(D, Proofs0, Proofs)
    ;   Proofs = Proofs0
    ),
    (   Inst0 = let(tmp(Q), a, check(_, _, _, _), [P])
    ->  proofs_add(Q-P, Proofs, Proofs1)
    ;   Inst0 = let(tmp(Q), a, renew_if(_, _, _, _), [P, _])
    ->  proofs_add(Q-P, Proofs, Proofs1)
    ;   Inst0 = let(tmp(Q), a, renew(_, _, _, _), [tmp(Q1), P]), get_assoc(Q1, Single, _)
    ->  proofs_add(Q-P, Proofs, Proofs1)
    ;   Proofs1 = Proofs
    ),
    (   ( Inst0 = let(_, _, raw_load(_, Off), [tmp(Q1)])
        ; Inst0 = raw_store(_, Off, _, tmp(Q1)) ),
        (   Proofs = pr(ByQ, _), get_assoc(Q1, ByQ, P1) -> true ; get_assoc(Q1, Single, P1) )
    ->  (   integer(Off), Off >= -2147483648, Off =< 2147483647,
            proven_access(Inst0, Q1, P1, Access)
        ->  Inst = reused(Access), Insts1 = Insts0
        ;   throw_fn(Fn, 'a reused proof at an offset beyond 32 bits')
        )
    ;   Inst0 = let(tmp(Q), a, renew(Lo, Hi, Rights, Align), [tmp(Q1), P])
    ->  renewed_inst(Q, renew(Lo, Hi, Rights, Align), Q1-P, Insts0, Fn, Single, Inst, Insts1)
    ;   fused_inst(Inst0, Insts0, Fn, Inst, Insts1)
    ),
    % A fused access or call may define Q's pointer too.
    live_inst(Inst, Live),
    findall(LD, inst_def(Live, LD), Ds),
    foldl(proofs_kill, Ds, Proofs1, Proofs2),
    fused_insts(Insts1, Fn, Single, Proofs2, Insts).

/* The block's proofs so far are pr(ByQ, ByP): ByQ maps each proof Q to
   its checked pointer P, and ByP each name N to the Qs once paired with
   tmp(N), perhaps since redefined. Q has at most one pair, since its
   definition drops the old one, so a kill of D is the removal of D's
   pair and of each pair whose pointer is tmp(D), without scanning the
   block's other proofs (a struct copy has tens of thousands). */
proofs_empty(pr(E, E)) :- empty_assoc(E).

proofs_add(Q-P, pr(ByQ0, ByP0), pr(ByQ, ByP)) :-
    put_assoc(Q, ByQ0, P, ByQ),
    (   P = tmp(N)
    ->  ( get_assoc(N, ByP0, Qs) -> true ; Qs = [] ),
        put_assoc(N, ByP0, [Q|Qs], ByP)
    ;   ByP = ByP0
    ).

proofs_kill(D, pr(ByQ0, ByP0), pr(ByQ, ByP)) :-
    ( del_assoc(D, ByQ0, _, ByQ1) -> true ; ByQ1 = ByQ0 ),
    (   del_assoc(D, ByP0, Qs, ByP)
    ->  foldl(proof_of_name(D), Qs, ByQ1, ByQ)
    ;   ByP = ByP0, ByQ = ByQ1
    ).

proof_of_name(D, Q, ByQ0, ByQ) :-
    (   get_assoc(Q, ByQ0, P), P == tmp(D) -> del_assoc(Q, ByQ0, _, ByQ) ; ByQ = ByQ0 ).

% renewed_inst(+Q, +Renew, +Q1-P, +Insts0, +Fn, +Single, -Inst, -Insts):
% a renew of Q1 and the access after it, at P, the replaced check's
% pointer, which has Q1's checked pointer's address and capability (the
% validator's same_pointer/3, docs/m7.md round 4 addendum). P1 is not
% read, so it need not stay live. Fusion and offsets as for a check.
renewed_inst(Q, Renew, Q1-P, [Access0|Insts], Fn, Single, fused(Renew, Access), Insts) :- !,
    (   get_assoc(Q1, Single, _), P = tmp(_),
        proven_access(Access0, Q, P, Access),
        Access \= let(_, _, raw_cas(_, _), _)
    ->  true
    ;   throw_fn(Fn, 'a renew without a single-definition source, or its access')
    ),
    (   Renew = renew(0, Size, _, Align), memberchk(Align, [1, 2, 4, 8]),
        integer(Size), Size > 0, Size =< 2147483647,
        access_pointer(Access, _, 0)
    ->  true
    ;   throw_fn(Fn, 'a renew or offset access the emitter cannot emit yet')
    ).
renewed_inst(_, _, _, [], Fn, _, _, _) :-
    throw_fn(Fn, 'a renew not followed by its access').


fused_inst(let(tmp(Q), a, Check, []), [Access0|Insts], Fn,
           fused(Check, Access), Insts) :-
    Check = check_local(Name, Off, _, _, _), !,
    ( proven_local_access(Access0, Q, local(Name, Off), Access),
      access_pointer(Access, _, 0)
    -> true
    ; throw_fn(Fn, 'a local check not followed by its local access') ).
% A guarded renewal (docs/m7.md, round 5) fuses as a check does, and
% keeps its guard G for emission and liveness.
fused_inst(let(tmp(Q), a, renew_if(Lo, Hi, Rights, Align), [P, G]), [Access0|Insts], Fn,
           fused(guarded(G, renew_if(Lo, Hi, Rights, Align)), Access), Insts) :- !,
    (   G = tmp(_), proven_access(Access0, Q, P, Access),
        Access \= let(_, _, raw_cas(_, _), _),
        Lo =:= 0, Size is Hi, Size =< 2147483647, memberchk(Align, [1, 2, 4, 8]),
        access_pointer(Access, _, 0)
    ->  true
    ;   throw_fn(Fn, 'a renew_if or its access the emitter cannot emit yet')
    ).
fused_inst(let(tmp(Q), a, Check, [P]), [Access0|Insts], Fn, Inst, Insts) :- !,
    (   proven_access(Access0, Q, P, Access) -> Inst = fused(Check, Access)
    ;   throw_fn(Fn, 'a check not followed by the access it proves')
    ),
    % access_check//2 checks [P, P+Size) for alignment 1, 2, 4 or 8 (a
    % cas is aligned to its width), and a raw
    % access emits at offset 0. subq's immediate is signed 32-bit: a
    % larger check needs a different native representation, not truncation.
    (   Check = check(0, Size, _, Align), memberchk(Align, [1, 2, 4, 8]),
        integer(Size), Size > 0, Size =< 2147483647,
        access_pointer(Access, _, 0)
    ->  true
    ;   throw_fn(Fn, 'a check or offset access_check//2 cannot emit yet')
    ).
fused_inst(let(tmp(Q), f, check_function, [P]), Insts0, Fn,
           fused(check_function, call(Res, P, Args)), Insts) :- !,
    (   Insts0 = [raw_call(Res, tmp(Q), Args)|Insts] -> true
    ;   throw_fn(Fn, 'a function check not followed by its raw call')
    ).
fused_inst(Inst, Insts, Fn, Inst, Insts) :-
    (   unchecked_access(Inst)
    ->  throw_fn(Fn, 'an unchecked access; run pizlonate first')
    ;   implicit_flight(Inst)
    ->  throw_fn(Fn, 'an implicit pointer operation; run pizlonate first')
    ;   true
    ).

% proven_access(+Access0, +Q, +P, -Access): Access0 is a raw access at
% tmp(Q) and Access is the same at P.
proven_access(let(D, K, raw_load(T, Off), [tmp(Q)]), Q, P,
              let(D, K, raw_load(T, Off), [P])) :- T \== p.
proven_access(raw_store(W, Off, V, tmp(Q)), Q, P,
              raw_store(W, Off, V, P)) :- W \== p.
proven_access(let(D, p, raw_load_pointer(Off, Es), [tmp(Q)]), Q, P,
              let(D, p, raw_load_pointer(Off, Es), [P])) :-
    pointer_memory_effects(load, Es).
proven_access(raw_store_pointer(Off, V, tmp(Q), Es), Q, P,
              raw_store_pointer(Off, V, P, Es)) :-
    pointer_memory_effects(store, Es).
% Atomic pointer accesses are heap-only: no proven_local_access clause.
proven_access(let(D, p, raw_load_pointer(Off, Es), [tmp(Q)]), Q, P,
              let(D, p, raw_load_pointer(Off, Es), [P])) :-
    pointer_memory_effects(atomic_load, Es).
proven_access(raw_store_pointer(Off, V, tmp(Q), Es), Q, P,
              raw_store_pointer(Off, V, P, Es)) :-
    pointer_memory_effects(atomic_store, Es).

% A cas, heap only too (escape.pl), reads Expected and New beside P.
proven_access(let(D, K, raw_cas(T, Off), [tmp(Q), E, N]), Q, P,
              let(D, K, raw_cas(T, Off), [P, E, N])).

proven_local_access(let(D, p, raw_load_pointer(Off, Es), [tmp(Q)]), Q, P,
                    let(D, p, raw_load_pointer(Off, Es), [P])) :-
    pointer_memory_effects(local_load, Es).
proven_local_access(raw_store_pointer(Off, V, tmp(Q), Es), Q, P,
                    raw_store_pointer(Off, V, P, Es)) :-
    pointer_memory_effects(local_store, Es).
proven_local_access(let(D, K, raw_load(T, Off), [tmp(Q)]), Q, P,
                    let(D, K, raw_load(T, Off), [P])) :- T \== p.
proven_local_access(raw_store(W, Off, V, tmp(Q)), Q, P,
                    raw_store(W, Off, V, P)) :- W \== p.

% access_pointer(+Access, -P, -Off): the fused Access is at P + Off.
access_pointer(let(_, _, raw_load(_, Off), [P]), P, Off).
access_pointer(raw_store(_, Off, _, P), P, Off).
access_pointer(let(_, p, raw_load_pointer(Off, _), [P]), P, Off).
access_pointer(raw_store_pointer(Off, _, P, _), P, Off).
access_pointer(let(_, _, raw_cas(_, Off), [P|_]), P, Off).
access_pointer(Access, P) :- access_pointer(Access, P, _).

% zero_offset(+Access, -Access0): Access at offset 0.
zero_offset(let(D, K, raw_load(T, _), Ps), let(D, K, raw_load(T, 0), Ps)).
zero_offset(raw_store(W, _, V, P), raw_store(W, 0, V, P)).

unchecked_access(let(_, _, load(_), _)).
unchecked_access(store(_, _, _)).
unchecked_access(let(_, _, atomic_load(_), _)).
unchecked_access(atomic_store(_, _, _)).
unchecked_access(call(_, tmp(_), _)).
unchecked_access(raw_call(_, _, _)).
unchecked_access(let(_, _, raw_load(_, _), _)).
unchecked_access(raw_store(_, _, _, _)).
unchecked_access(let(_, _, raw_load_pointer(_, _), _)).
unchecked_access(raw_store_pointer(_, _, _, _)).
unchecked_access(let(_, _, raw_cas(_, _), _)).
unchecked_access(local_load(_, _, _, _, _)).
unchecked_access(local_store(_, _, _, _)).

live_block(block(L, Phis, Insts0, Jump), block(L, Phis, Insts, Jump)) :-
    maplist(live_inst, Insts0, Insts).

% Layout sees exactly the former whole-pointer operation at this index.
% In particular both original p operands survive every internal helper.
% A guarded access reads its guard too, so G keeps its slot to here.
live_inst(fused(guarded(G, _), Access), uses(Inst, [G])) :- !,
    live_inst(fused(none, Access), Inst).
live_inst(fused(_, let(D, p, raw_load_pointer(Off, _), [P])),
          let(D, p, raw_load(p, Off), [P])) :- !.
live_inst(fused(_, raw_store_pointer(Off, V, P, _)),
          raw_store(p, Off, V, P)) :- !.
live_inst(reused(Access), Access) :- !.
live_inst(Inst0, Inst) :-
    (   Inst0 = fused(_, Access) -> Inst = Access ; Inst = Inst0 ).

throw_fn(Fn, Why) :-
    format(atom(Msg), 'Fil-C backend, in ~w: ~w', [Fn, Why]),
    throw(nanofil_error(Msg)).

setjmp_snapshots([], _, _) --> [].
setjmp_snapshots([D|Ds], Bytes, Ctx) -->
    origin_store(Ctx, c),
    slot_reg_load(thread, rdi, Ctx),
    [ins(mov, q, [imm(Bytes), reg(rsi)]),
     ins(call, none, [plt(filc_allocate)]),
     ins(lea, q, [mem(16, rax), reg(rdx)])],
    reg_slot_store(rdx, lower(setjmp_snapshot(D)), Ctx),
    setjmp_snapshots(Ds, Bytes, Ctx).

body_function_object(generic_only(Adapter), Name, Linkage, Impl) -->
    variadic_object(Name, Linkage, Adapter, Impl).
body_function_object(fast_and_generic(Sig,Adapter), Name, Linkage, Impl) -->
    function_object(Name, Linkage, Adapter, Sig, Impl).

% The return protocol is already chosen; this is only its native size.
target_form(registers, reg).
target_form(buffer(N), mem(Bytes)) :- Bytes is (8 + 8*N + 15) // 16 * 16.

abi_actions([], _, _, _) --> [].
abi_actions([A|As], I, B, Ctx) -->
    abi_action(A, I, B, Ctx), abi_actions(As, I, B, Ctx).

abi_action(native_frame(Return), _, _, Ctx) -->
    { ctx_size(Ctx, Size), target_form(Return, Form) },
    [ins(push, q, [reg(rbp)]),
     ins(mov, q, [reg(rsp), reg(rbp)]),
     ins(sub, q, [imm(Size), reg(rsp)])],
    entry_regs_shift(Form).
abi_action(stack_check, _, _, _) -->
    { field(thread, stack_limit, rdi, Limit) },
    [ins(cmp, q, [reg(rsp), Limit]),
     ins(jae, none, [plt(filc_stack_overflow_failure)])].
abi_action(save_thread, _, _, Ctx) --> reg_slot_store(rdi, thread, Ctx).
abi_action(save_return(Return), _, _, Ctx) -->
    { target_form(Return, Form) }, retbuf_store(Form, Ctx).
abi_action(zero_roots(N), _, _, Ctx) -->
    { ctx_frame_base(Ctx, Base) }, lowers_zeroing(N, Base).
abi_action(push_frame(Which), _, _, Ctx) -->
    { ctx_frame_base(Ctx, Base), NegFrameBase is -Base,
      field(thread, top_frame, rdi, Top) },
    [ins(mov, q, [Top, reg(rax)]),
     ins(mov, q, [reg(rax), mem(NegFrameBase, rbp)])],
    origin_store(Ctx, Which),
    [ins(lea, q, [mem(NegFrameBase, rbp), reg(rax)]),
     ins(mov, q, [reg(rax), Top])].
abi_action(receive(Return, Ts), _, _, Ctx) -->
    { target_form(Return, Form), typed_locations(Ts, Form, Ls, _, _) },
    typed_incoming(Ts, Ls, Ctx).
abi_action(snapshots(Sites, Keys), _, _, Ctx) -->
    { length(Keys, N), Bytes is 8*N }, setjmp_snapshots(Sites, Bytes, Ctx).
abi_action(initialize_local(Name), _, _, Ctx) -->
    { ctx_slot(Ctx, local(Name), local(Payload, Aux, _, Padded)),
      P is -Payload, A is -Aux, Words is Padded // 8 },
    zero_words(P, Words),
    { Lowers is A + 8 }, zero_words(Lowers, Words),
    [ins(mov, q, [imm(Words), mem(A, rbp)]),
     ins(lea, q, [mem(A, rbp), reg(rax)])],
    reg_slot_store(rax, stack_aux(Name), Ctx).
abi_action(pop_frame, _, _, Ctx) --> frame_pop(Ctx).
abi_action(exception(Return), _, _, Ctx) -->
    { target_form(Return, Form) }, exception_flag(Form, Ctx),
    [ins(leave, none, []), ins(ret, none, [])].
abi_action(origin(Which), _, _, Ctx) --> origin_store(Ctx, Which).
abi_action(reserve_result(Return), _, _, _) -->
    { target_form(Return, Form) }, ret_buffer_reservation(Form).
abi_action(release_result(Return), _, _, _) -->
    { target_form(Return, Form) }, ret_buffer_release(Form).
abi_action(invoke(Target, Return, Words), _, _, Ctx) -->
    { target_form(Return, Form), target_operand(Target, Operand) },
    fast_call(Form, Words, direct(Operand), Ctx).
abi_action(result(Return, Channels), _, _, Ctx) -->
    { target_form(Return, Form) }, fast_result(Form, Channels, Ctx).
abi_action(dispatch(P,Sig,Return,Words,Result,Size,Cells,GenericResult), I,B,Ctx) -->
    { special_label(Ctx, notfn, NotFn), target_form(Return, Form) },
    flight_load(P, Ctx), function_check(NotFn), reg_slot_store(rcx, aux, Ctx),
    indirect_call(Sig, Form, Words, Result, Size, Cells, GenericResult, I, B, Ctx).
abi_action(getter(weak_getter(S), Which, D), I, B, Ctx) --> !,
    % A weak declaration's getter is null if nothing defines it; then its
    % address is the null pointer (clang's filc_weak_symbol_is_null).
    { abi_symbol(getter, S, Getter),
      local_label(Ctx, B, I, weak_null, Null),
      local_label(Ctx, B, I, weak_done, Done) },
    [ins(cmp, q, [imm(0), gotpcrel(Getter)]), ins(je, none, [sym(Null)])],
    abi_action(getter(external_getter(S), Which, D), I, B, Ctx),
    [ins(jmp, none, [sym(Done)]), label(Null),
     ins(xor, l, [reg(eax), reg(eax)]), ins(xor, l, [reg(ecx), reg(ecx)])],
    flight_store(D, Ctx),
    [label(Done)].
abi_action(getter(Target, Which, D), _, _, Ctx) -->
    { ctx_name(Ctx, Name), origin_label(Name, Which, Origin),
      target_operand(Target, Getter) },
    slot_reg_load(thread, rdi, Ctx),
    [ins(lea, q, [rip(Origin), reg(rsi)]),
     ins(call, none, [Getter]), ins(mov, q, [reg(rdx), reg(rcx)])],
    flight_store(D, Ctx).
abi_action(snapshot_cursor(Snapshot, Off, D), _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) }, flight_load(Snapshot, Ctx),
    load(const(Off), l, d, Fn),
    [ins(add, q, [reg(rdx), reg(rax)])], flight_store(D, Ctx).
abi_action(consume_va(K,P,Size,D), I,B,Ctx) -->
    flight_load(P, Ctx),
    [ins(mov, q, [reg(rax), reg(rdi)]), ins(mov, q, [reg(rcx), reg(rsi)]),
     ins(mov, l, [imm(Size), reg(edx)]), ins(mov, l, [imm(Size), reg(ecx)]),
     ins(call, none, [plt(filc_get_next_ptr_bytes_for_va_arg)])],
    va_arg_load(K, D, I, B, Ctx).
abi_action(returns_twice(D,Kind,Buf,Mask,Keys), I,B,Ctx) -->
    setjmp(D, Kind, Buf, Mask, Keys, I, B, Ctx).
abi_action(return_value(K,V), _, _, Ctx) --> ret_value(K, V, Ctx).
abi_action(return_typed(Ks,Vs), _, _, Ctx) -->
    { ctx_fn(Ctx, Fn), foldl(typed_return_word, Ks, Vs, KTs, []),
      result_registers(KTs, Rs) },
    typed_return_loads(KTs, Rs, Fn, Ctx).
abi_action(return_registers([V1,V2]), _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) }, load(V1,l,d,Fn), load(V2,l,c,Fn).
abi_action(return_buffer(Words), _, _, Ctx) -->
    slot_reg_load(retbuf, rax, Ctx), buffer_words(Words, 8, Ctx).
abi_action(success(registers), _, _, _) -->
    [ins(xor, l, [reg(eax), reg(eax)]),ins(leave, none, []),ins(ret, none, [])].
abi_action(success_buffer, _, _, _) -->
    [ins(mov, b, [imm(0), mem(0, rax)])].
abi_action(native_return, _, _, _) --> [ins(leave, none, []),ins(ret, none, [])].
abi_action(copy_filter(D,S,N,Res), I, B, Ctx) -->
    (   { ctx_copies(Ctx, inline) } -> copy_filter(D, S, N, Res, I, B, Ctx)
    ;   []
    ).
abi_action(copy_join, I, B, Ctx) -->
    (   { ctx_copies(Ctx, inline) }
    ->  { local_label(Ctx, B, I, copied, Done) }, [label(Done)]
    ;   []
    ).

/* The small-copy filter (docs/perf.md item 7a): a copy of N bytes,
   1 =< N =< 16, from S to D, done inline when the runtime's memmove would
   pass its checks and have nothing to do for aux; otherwise a jump to
   the unchanged call after it. D is in %rax:%rcx and S in %rsi:%rdi; the
   checks and the copy use %rdx and %r8. Only the call's scratch
   registers, which nothing allocates, are named. */
copy_filter(D, S, N, Res, I, B, Ctx) -->
    { ctx_fn(Ctx, Fn),
      local_label(Ctx, B, I, copy, Slow),
      local_label(Ctx, B, I, copied, Done) },
    load(D, l, a, Fn), lower_reg_load(D, rcx, Ctx),
    copy_check(rax, rcx, N, 0x0786ffffffffffff, Slow),
    load(S, l, si, Fn), lower_reg_load(S, rdi, Ctx),
    copy_check(rsi, rdi, N, 0x0000ffffffffffff, Slow),
    { copy_parts(N, Parts) },
    copy_loads(Parts, [rdx, r8]),
    copy_stores(Parts, [rdx, r8]),
    copy_result(Res, Ctx),
    [ins(jmp, none, [sym(Done)]),
     label(Slow)].

% A jump to Slow unless the pointer P with lower L may be accessed for N
% bytes (CHECK_BOUNDS_FAST: lower =< P, N =< upper - P) and the header
% word at -8(L) has none of Mask's bits: the aux pointer (low 48 bits)
% and, for the destination, READONLY | FREE | SPECIAL (CHECK_WRITE_FAST).
copy_check(P, L, N, Mask, Slow) -->
    [ins(test, q, [reg(L), reg(L)]),
     ins(jz, none, [sym(Slow)]),
     ins(cmp, q, [reg(L), reg(P)]),
     ins(jb, none, [sym(Slow)]),
     ins(mov, q, [mem(-16, L), reg(rdx)]),
     ins(sub, q, [imm(N), reg(rdx)]),
     ins(jb, none, [sym(Slow)]),
     ins(cmp, q, [reg(rdx), reg(P)]),
     ins(ja, none, [sym(Slow)]),
     ins(movabs, q, [imm(Mask), reg(rdx)]),
     ins(test, q, [reg(rdx), mem(-8, L)]),
     ins(jnz, none, [sym(Slow)])].

% copy_parts(+N, -Parts): the accesses, Bytes-Offset, that cover N bytes;
% two may overlap.
copy_parts(N, [N-0]) :- memberchk(N, [1,2,4,8]), !.
copy_parts(3, [2-0, 2-1]) :- !.
copy_parts(N, [4-0, 4-O]) :- N < 8, !, O is N - 4.
copy_parts(N, [8-0, 8-O]) :- O is N - 8.

% Every load before any store, so an overlapping memmove copies the
% source as it was.
copy_loads([], _) --> [].
copy_loads([Bytes-Off|Ps], [R|Rs]) -->
    { copy_load(Bytes, Op, S, R, Rn) },
    [ins(Op, S, [mem(Off, rsi), reg(Rn)])],
    copy_loads(Ps, Rs).
copy_stores([], _) --> [].
copy_stores([Bytes-Off|Ps], [R|Rs]) -->
    { copy_reg(Bytes, R, Rn), copy_width(Bytes, S) },
    [ins(mov, S, [reg(Rn), mem(Off, rax)])],
    copy_stores(Ps, Rs).

copy_load(1, movzb, l, R, Rn) :- copy_reg(4, R, Rn).
copy_load(2, movzw, l, R, Rn) :- copy_reg(4, R, Rn).
copy_load(4, mov, l, R, Rn) :- copy_reg(4, R, Rn).
copy_load(8, mov, q, R, Rn) :- copy_reg(8, R, Rn).
copy_width(1, b). copy_width(2, w). copy_width(4, l). copy_width(8, q).
copy_reg(1, rdx, dl). copy_reg(2, rdx, dx). copy_reg(4, rdx, edx). copy_reg(8, rdx, rdx).
copy_reg(1, r8, r8b). copy_reg(2, r8, r8w). copy_reg(4, r8, r8d). copy_reg(8, r8, r8).

% The call's result is its destination, address and lower.
copy_result(void, _) --> [].
copy_result(result(T, p), Ctx) -->
    reg_slot_store(rax, T, Ctx), reg_slot_store(rcx, lower(T), Ctx).

target_operand(implementation(F,Sig), sym(S)) :- abi_symbol(impl(Sig), F, S).
target_operand(entry(F,Sig), sym(S)) :- abi_symbol(entry(Sig), F, S).
target_operand(local_getter(F), sym(S)) :- abi_symbol(getter, F, S).
target_operand(external_getter(F), plt(S)) :- abi_symbol(getter, F, S).

% A buffered return's entry has the buffer in %rdi and the thread in
% %rsi: the buffer goes to %rax and the thread to %rdi.
entry_regs_shift(reg) --> [].
entry_regs_shift(mem(_)) -->
    [ins(mov, q, [reg(rdi), reg(rax)]),
     ins(mov, q, [reg(rsi), reg(rdi)])].

% The buffer of a buffered return, from %rax into its slot.
retbuf_store(reg, _) --> [].
retbuf_store(mem(_), Ctx) --> reg_slot_store(rax, retbuf, Ctx).

% The zeroing of the N entries of lowers[], so the GC sees no stale
% lowers.
lowers_zeroing(N, FrameBase) -->
    (   { N > 0 }
    ->  [ins(xor, l, [reg(eax), reg(eax)])],
        { N1 is N - 1,
          numlist(0, N1, Is) },
        lower_entry_stores(Is, FrameBase)
    ;   []
    ).

% The store of %rax into lowers[I] for each I in Is.
lower_entry_stores([], _) --> [].
lower_entry_stores([I|Is], FrameBase) -->
    { Off is 16 + 8 * I - FrameBase },
    [ins(mov, q, [reg(rax), mem(Off, rbp)])],
    lower_entry_stores(Is, FrameBase).

zero_words(_, 0) --> !, [].
zero_words(Off, N) -->
    [ins(mov, q, [imm(0), mem(Off, rbp)])],
    { Next is Off + 8, Rest is N - 1 }, zero_words(Next, Rest).

% The store of the c or n origin (origin_label/3) into the filc_frame.
origin_store(Ctx, Which) -->
    { ctx_name(Ctx, Name),
      ctx_frame_base(Ctx, FrameBase),
      Off is 8 - FrameBase,
      origin_label(Name, Which, Origin) },
    [ins(lea, q, [rip(Origin), reg(rax)]),
     ins(mov, q, [reg(rax), mem(Off, rbp)])].

% The pop of the filc_frame: thread->top_frame back to its parent.
frame_pop(Ctx) -->
    { ctx_frame_base(Ctx, FrameBase),
      NegFrameBase is -FrameBase,
      field(thread, top_frame, rsi, Top) },
    slot_reg_load(thread, rsi, Ctx),
    [ins(mov, q, [mem(NegFrameBase, rbp), reg(rdi)]),
     ins(mov, q, [reg(rdi), Top])].

% has_exception = 1, in %al or in the return buffer.
exception_flag(reg, _) -->
    [ins(mov, b, [imm(1), reg(al)])].
exception_flag(mem(_), Ctx) -->
    slot_reg_load(retbuf, rax, Ctx),
    [ins(mov, b, [imm(1), mem(0, rax)])].

% The failure block of function_check//1, if the function calls through
% a pointer.
not_function_block(Blocks, Ctx) -->
    (   { member(block(_, _, Insts, _), Blocks),
          member(abi(Actions), Insts),
          memberchk(dispatch(_,_,_,_,_,_,_,_), Actions) }
    ->  { special_label(Ctx, notfn, NotFn) },
        [label(NotFn),
         ins(mov, q, [reg(rax), reg(rdi)]),
         ins(mov, q, [reg(rcx), reg(rsi)]),
         ins(call, none, [plt(filc_check_function_call_fail)]),
         ins(ud2, none, [])]
    ;   []
    ).

% The failure block of jump(unreachable)//3, if a block ends in one:
% filc_error(Message, Origin) with the frame's n origin.
unreachable_block(Blocks, Ctx) -->
    (   { memberchk(block(_, _, _, unreachable), Blocks) }
    ->  { special_label(Ctx, unreachable, Unreachable),
          ctx_name(Ctx, Name),
          unreachable_message_label(Name, Message),
          origin_label(Name, n, Origin) },
        [label(Unreachable),
         ins(lea, q, [rip(Message), reg(rdi)]),
         ins(lea, q, [rip(Origin), reg(rsi)]),
         ins(call, none, [plt(filc_error)]),
         ins(ud2, none, [])]
    ;   []
    ).

% clang's message, so a nanofil panic reads as clang's does.
unreachable_message(Blocks, Name) -->
    (   { memberchk(block(_, _, _, unreachable), Blocks) }
    ->  { unreachable_message_label(Name, Message) },
        [section(rodata), label(Message),
         asciz('llvm unreachable instruction')]
    ;   []
    ).

unreachable_message_label(Name, Label) :-
    format(atom(Label), '.L~w..unreachable_msg', [Name]).

% The same registers by their amd64 short names, for load//4.
form_short_regs(reg, [d, c, r8, r9]).
form_short_regs(mem(_), [c, r8, r9]).

% Word I of a generic call's arguments or results is at thread offset
% Addr, word I of the inline buffer, with its lower at Lower, word I of
% the inline aux buffer.
generic_offsets(I, Addr, Lower) :-
    struct_field(thread, cc_inline_buffer, Buffer),
    struct_field(thread, cc_inline_aux_buffer, AuxBuffer),
    Addr is Buffer + 8 * I,
    Lower is AuxBuffer + 8 * I.

channel_offset(data(I), Off) :- generic_offsets(I, Off, _).
channel_offset(aux(I), Off) :- generic_offsets(I, _, Off).
packet_offsets(packet(Copies, Zeros), packet(Offsets, ZeroOffsets)) :-
    maplist(channel_offset, Copies, Offsets), maplist(channel_offset, Zeros, ZeroOffsets).

% Stack space for a buffered return, around a call.
ret_buffer_reservation(reg) --> [].
ret_buffer_reservation(mem(Bytes)) --> [ins(sub, q, [imm(Bytes), reg(rsp)])].

ret_buffer_release(reg) --> [].
ret_buffer_release(mem(Bytes)) --> [ins(add, q, [imm(Bytes), reg(rsp)])].

% The padding, Pad = 0 or 1 words, that keeps %rsp 16-aligned at a call
% that pushes an odd number of words.
align_pad(0) --> [].
align_pad(1) --> [ins(sub, q, [imm(8), reg(rsp)])].

% The release of Bytes of pushed stack words, if any.
stack_release(Bytes) -->
    (   { Bytes > 0 }
    ->  [ins(add, q, [imm(Bytes), reg(rsp)])]
    ;   []
    ).

%% Blocks and jumps

% Each block: its label, instructions and jump.
blocks([], _) --> [].
blocks([Block|Blocks], Ctx) -->
    block_once(Block, Blocks, Ctx),
    blocks(Blocks, Ctx).

% A block's code is its first: committing frees the choicepoints that
% would keep a large function's (sqlite3VdbeExec's) garbage alive.
% Blocks are the ones after it, for branch selection's fallthrough.
block_once(Block, Blocks, Ctx, S0, S) :- once(block_code(Block, Blocks, Ctx, S0, S)).

block_code(block(Label, _, Insts, Jump), Blocks, Ctx) -->
    { block_label(Ctx, Label, A) },
    [label(A)],
    (   { ctx_branches(Ctx, selected(Uses)) }
    ->  { next_block(Blocks, Next),
          compare_branch(Insts, Jump, Uses, Insts1, Jump1) },
        insts(Insts1, 0, Label, Ctx),
        selected_jump(Jump1, Label, Next, Ctx)
    ;   insts(Insts, 0, Label, Ctx),
        jump(Jump, Label, Ctx)
    ).

% The code of the jump that ends block From.
jump(goto(To), From, Ctx) -->
    edge(From, To, j, Ctx).
jump(branch(V, True, False), From, Ctx) -->
    { ctx_fn(Ctx, Fn),
      local_label(Ctx, From, jnz, false, FalseLabel) },
    load(V, w, a, Fn),
    [ins(test, l, [reg(eax), reg(eax)]),
     ins(jz, none, [sym(FalseLabel)])],
    edge(From, True, t, Ctx),
    [label(FalseLabel)],
    edge(From, False, f, Ctx).
jump(abi_return(Actions), B, Ctx) --> abi_actions(Actions, ret, B, Ctx).
% A reached unreachable is a Fil-C safety panic, as clang's is
% (FilPizlonator's UnreachableInst case): one shared block per function.
jump(unreachable, _, Ctx) -->
    { special_label(Ctx, unreachable, Unreachable) },
    [ins(jmp, none, [sym(Unreachable)])].

% The returned value V of class K, in %rdx, and its lower in %rcx for p.
ret_value(p, V, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, l, d, Fn),
    lower_reg_load(V, rcx, Ctx).
ret_value(w, V, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, w, d, Fn).
ret_value(l, V, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, l, d, Fn).
ret_value(K, V, Ctx) -->
    { float_class(K), ctx_fn(Ctx,Fn) },
    load(V,K,a,Fn), to_xmm(K,a,xmm0).

% A returned tuple's words as K-Word, a p value being its address and
% lower; then each loaded into its result register.
typed_return_word(p, V, [l-addr(V),l-lower(V)|W], W) :- !.
typed_return_word(K, V, [K-val(V)|W], W).
typed_return_loads([], [], _, _) --> [].
typed_return_loads([K-W|KTs], [R|Rs], Fn, Ctx) -->
    typed_return_load(W, K, R, Fn, Ctx), typed_return_loads(KTs, Rs, Fn, Ctx).
typed_return_load(val(V), K, xmm(K,X), Fn, _) --> load(V, K, a, Fn), to_xmm(K, a, X).
typed_return_load(val(V), K, gpr(G), Fn, _) --> { short_reg(G, R) }, load(V, K, R, Fn).
typed_return_load(addr(V), _, gpr(G), Fn, _) --> { short_reg(G, R) }, load(V, l, R, Fn).
typed_return_load(lower(V), _, gpr(G), _, Ctx) --> lower_reg_load(V, G, Ctx).
short_reg(rdx, d).
short_reg(rcx, c).

% The words of a buffered return, into the buffer at %rax.
buffer_words([], _, _) --> [].
buffer_words([wf(_,Word)|Words], Off, Ctx) -->
    { ctx_fn(Ctx, Fn), buffer_register(Word, R), reg_name(R,l,Reg) },
    buffer_word_load(Word, R, Fn, Ctx),
    [ins(mov, q, [reg(Reg), mem(Off, rax)])],
    { Next is Off+8 }, buffer_words(Words, Next, Ctx).
buffer_register(lower(_), c).
buffer_register(addr(_), d).
buffer_register(val(_,_), d).
% Tuple payloads occupy full eightbyte slots even for a w element.
buffer_word_load(val(_,V), R, Fn, _) --> load(V,l,R,Fn).
buffer_word_load(addr(V), R, Fn, _) --> load(V,l,R,Fn).
buffer_word_load(lower(V), R, _, Ctx) -->
    { reg_name(R,l,Reg) }, lower_reg_load(V,Reg,Ctx).

% Phi copies for the edge to Target, a label or poll(Label), then the
% pollcheck if Target asks for one, then the jump.
edge(From, Target, Tag, Ctx) -->
    edge_moves(From, Target, Tag, Ctx),
    { edge_label(Target, To),
      block_label(Ctx, To, ToLabel) },
    [ins(jmp, none, [sym(ToLabel)])].

edge_moves(From, Target, Tag, Ctx) -->
    { edge_label(Target, To),
      ctx_labels(Ctx, Labels),
      get_assoc(To, Labels, Phis),
      phrase((phi_reads(Phis, From, Ctx), phi_writes(Phis, Ctx)), Copy),
      (   maplist(copy_line, Copy) -> true
      ;   throw(nanofil_error('a phi copy contains a possible safepoint'))
      ) },
    seq(Copy),
    edge_poll(Target, From, Tag, Ctx).

% copy_line(+Line): Line is a move that cannot reach a safepoint: no
% call, poll, helper, trap or jump. Phis of different blocks share
% shadow slots and roots (filc_abi.pl's shadow_storage/8) because no
% safepoint is inside an edge's parallel copy; this keeps it so.
copy_line(ins(mov, _, [_, _])).
copy_line(ins(movabs, q, [imm(_), reg(_)])).
copy_line(ins(lea, q, [rip(_), reg(_)])).

/* Branch selection (docs/perf.md). A block whose last instruction is an
   integer comparison read only by the block's branch branches on the
   comparison's flags; a branch whose edge needs no phi copies or poll
   jumps straight to its block; an edge to the next block falls through.
   The reference above stores the comparison's boolean, tests it and
   jumps on both arms. Setjmp functions keep the reference. */

% branch_selection(+Mode, +Blocks, -Branches): reference, or
% selected(Uses), where Uses counts each temporary's occurrences in
% Blocks, its definition included.
branch_selection(reference, _, reference).
branch_selection(selected, Blocks, selected(Uses)) :-
    phrase(temp_names(Blocks), Names),
    msort(Names, Sorted),
    name_counts(Sorted, Counts),
    list_to_assoc(Counts, Uses).

temp_names(tmp(N)) --> !, [N].
temp_names(T) -->
    (   { compound(T) }
    ->  { T =.. [_|As] }, temp_name_list(As)
    ;   []
    ).
temp_name_list([]) --> [].
temp_name_list([A|As]) --> temp_names(A), temp_name_list(As).

name_counts([], []).
name_counts([N|Ns], [N-C|Cs]) :- same_names(Ns, N, 1, C, Rest), name_counts(Rest, Cs).
same_names([M|Ms], N, C0, C, Rest) :- M == N, !, C1 is C0 + 1, same_names(Ms, N, C1, C, Rest).
same_names(Rest, _, C, C, Rest).

next_block([block(L, _, _, _)|_], some(L)).
next_block([], none).

% compare_branch(+Insts, +Jump, +Uses, -Insts1, -Jump1): a last integer
% comparison that only the branch reads moves into the jump.
compare_branch(Insts, branch(tmp(D), T, F), Uses, Init, compare(C, K, Args, T, F)) :-
    once(append(Init, [let(tmp(D), w, cmp(C, K), Args)], Insts)),
    ( K == w ; K == l ),
    get_assoc(D, Uses, 2),
    !.
compare_branch(Insts, Jump, _, Insts, Jump).

selected_jump(compare(C, K, [X, Y], T, F), From, Next, Ctx) -->
    { ctx_fn(Ctx, Fn), cond_code(C, CC), att_suffix(K, S), reg_name(a, K, A) },
    load(X, K, a, Fn),
    (   { Y = const(N), integer_immediate(K, N, V) }
    ->  [ins(cmp, S, [imm(V), reg(A)])]
    ;   { reg_name(c, K, RC) },
        load(Y, K, c, Fn),
        [ins(cmp, S, [reg(RC), reg(A)])]
    ),
    selected_branch(CC, T, F, From, Next, Ctx).
selected_jump(branch(V, T, F), From, Next, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, w, a, Fn),
    [ins(test, l, [reg(eax), reg(eax)])],
    selected_branch(ne, T, F, From, Next, Ctx).
selected_jump(goto(To), From, Next, Ctx) -->
    selected_edge(From, To, j, Next, Ctx).
selected_jump(abi_return(As), From, _, Ctx) --> jump(abi_return(As), From, Ctx).
selected_jump(unreachable, From, _, Ctx) --> jump(unreachable, From, Ctx).

% The flags hold condition CC exactly when the branch goes to True.
selected_branch(CC, True, False, From, Next, Ctx) -->
    (   { Next == some(True), plain_edge(True, Ctx), plain_edge(False, Ctx) }
    ->  { block_label(Ctx, False, FalseLabel), negated(CC, NC), atom_concat(j, NC, J) },
        [ins(J, none, [sym(FalseLabel)])]
    ;   { plain_edge(True, Ctx) }
    ->  { block_label(Ctx, True, TrueLabel), atom_concat(j, CC, J) },
        [ins(J, none, [sym(TrueLabel)])],
        selected_edge(From, False, f, Next, Ctx)
    ;   { plain_edge(False, Ctx) }
    ->  { block_label(Ctx, False, FalseLabel), negated(CC, NC), atom_concat(j, NC, J) },
        [ins(J, none, [sym(FalseLabel)])],
        selected_edge(From, True, t, Next, Ctx)
    ;   { local_label(Ctx, From, jnz, false, FalseLabel), negated(CC, NC),
          atom_concat(j, NC, J) },
        [ins(J, none, [sym(FalseLabel)])],
        edge(From, True, t, Ctx),
        [label(FalseLabel)],
        selected_edge(From, False, f, Next, Ctx)
    ).

% An edge to a block without phis, and without a poll.
plain_edge(Target, Ctx) :-
    Target \= poll(_),
    ctx_labels(Ctx, Labels),
    get_assoc(Target, Labels, []).

% The edge's code without its jump when it goes to the next block.
selected_edge(From, Target, Tag, Next, Ctx) -->
    (   { edge_label(Target, To), Next == some(To) }
    ->  edge_moves(From, Target, Tag, Ctx)
    ;   edge(From, Target, Tag, Ctx)
    ).

negated(e, ne). negated(ne, e).
negated(l, ge). negated(ge, l). negated(le, g). negated(g, le).
negated(b, ae). negated(ae, b). negated(be, a). negated(a, be).

edge_poll(Target, From, Tag, Ctx) -->
    (   { Target = poll(_) }
    ->  pollcheck(Ctx, From, Tag)
    ;   []
    ).

% The pollcheck: a call of filc_pollcheck_slow if the thread's state asks
% for it.
pollcheck(Ctx, Block, Tag) -->
    { ctx_name(Ctx, Name),
      local_label(Ctx, Block, Tag, poll, NoPoll),
      origin_label(Name, n, Origin),
      field(thread, state, rdi, State) },
    slot_reg_load(thread, rdi, Ctx),
    [ins(test, b, [imm(14), State]),
     ins(jz, none, [sym(NoPoll)]),
     ins(lea, q, [rip(Origin), reg(rsi)]),
     ins(call, none, [plt(filc_pollcheck_slow)]),
     label(NoPoll)].

% The parallel copy of an edge's phis: first every incoming value into
% its phi's shadow slots (phi_reads//3), then every shadow into the phi
% (phi_writes//2).
phi_reads([], _, _) --> [].
phi_reads([phi(tmp(D), K, Pairs)|Phis], From, Ctx) -->
    { memberchk(From-V, Pairs) },
    phi_read(K, V, D, Ctx),
    phi_reads(Phis, From, Ctx).

% The incoming value V, of class K, into the shadow slots of phi tmp(D).
phi_read(p, V, D, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, l, a, Fn),
    reg_slot_store(rax, shadow(D), Ctx),
    lower_reg_load(V, rax, Ctx),
    reg_slot_store(rax, lower(shadow(D)), Ctx).
phi_read(w, V, D, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, w, a, Fn),
    reg_slot_store(rax, shadow(D), Ctx).
phi_read(l, V, D, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, l, a, Fn),
    reg_slot_store(rax, shadow(D), Ctx).
phi_read(K,V,D,Ctx) -->
    { float_class(K), ctx_fn(Ctx,Fn) },
    load(V,K,a,Fn), reg_slot_store(rax,shadow(D),Ctx).

% The second half of the parallel copy: each phi's shadow into the phi.
phi_writes([], _) --> [].
phi_writes([phi(tmp(D), K, _)|Phis], Ctx) -->
    slot_reg_load(shadow(D), rax, Ctx),
    reg_slot_store(rax, tmp(D), Ctx),
    phi_lower_write(K, D, Ctx),
    phi_writes(Phis, Ctx).

% For a p phi tmp(D), its shadow lower into its lower.
phi_lower_write(p, D, Ctx) -->
    slot_reg_load(lower(shadow(D)), rax, Ctx),
    reg_slot_store(rax, lower(tmp(D)), Ctx).
phi_lower_write(w, _, _) --> [].
phi_lower_write(l, _, _) --> [].
phi_lower_write(s, _, _) --> [].
phi_lower_write(d, _, _) --> [].

% The lower of a p value: its lowers[] entry, or 0 for a constant.
lower_reg_load(tmp(N), Reg, Ctx) --> slot_reg_load(lower(tmp(N)), Reg, Ctx).
lower_reg_load(const(_), Reg, _) --> [ins(mov, q, [imm(0), reg(Reg)])].

% A p value's address into %rax and lower into %rcx.
flight_load(V, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, l, a, Fn),
    lower_reg_load(V, rcx, Ctx).

% The flight pointer in %rax:%rcx into tmp(D) and its lower.
flight_store(D, Ctx) -->
    reg_slot_store(rax, tmp(D), Ctx),
    reg_slot_store(rcx, lower(tmp(D)), Ctx).

%% Instructions

% The code of each instruction. Invariant: Insts are the instructions
% of Block from index Index on.
insts([], _, _, _) --> [].
insts([Inst|Insts], Index, Block, Ctx) -->
    inst_once(Inst, Index, Block, Ctx),
    { Index1 is Index + 1 },
    insts(Insts, Index1, Block, Ctx).

% An instruction's code is its first, as a block's is (block_once/5):
% inst//4's clauses leave choicepoints (shared first-argument functors,
% reg_name/3), which would keep every earlier instruction of a long
% block's frames alive (libaom: 30k instructions overflowed 1 GB).
inst_once(Inst, Index, Block, Ctx, S0, S) :- once(inst(Inst, Index, Block, Ctx, S0, S)).

% inst(+Inst, +Index, +Block, +Ctx)//: the code of instruction Inst,
% the Indexth of block Block. Instructions go by their op's kind (ir.pl),
% stores and calls by their width and callee.
inst(let(tmp(D), K, Op, Args), Index, Block, Ctx) -->
    { op_kind(Op, Kind) },
    kind_inst(Kind, K, Op, Args, D, Index, Block, Ctx).
inst(flight(tmp(D), Op, [A|Args], Lower), _, _, Ctx) -->
    flight_address_load(A, a, Ctx),
    flight_lower_load(Lower, Ctx),
    flight_calculation(Op, Args, Ctx),
    flight_store(D, Ctx).
inst(fused(check(_, Size, Rights, Align), Access), Index, Block, Ctx) -->
    { access_pointer(Access, P),
      rights_write(Rights, Write) },
    flight_load(P, Ctx),
    access_check(k(Size, Write, Align), Ctx),
    raw_access(Access, Index, Block, Ctx).
% A renew (docs/m7.md, round 4): the check's bounds and alignment still
% hold, so only its temporal part is tested, the free flag, and for a
% write the read-only one, in the flags byte write_check//2 tests. A
% failure goes to the same reporter with the same pointer and origin.
inst(fused(renew(_, Size, Rights, Align), Access), Index, Block, Ctx) -->
    { access_pointer(Access, P),
      rights_write(Rights, Write),
      renew_mask(Write, Mask),
      check_fail_label(Ctx, k(Size, Write, Align), Fail) },
    flight_load(P, Ctx),
    [ins(test, b, [imm(Mask), mem(-2, rcx)]),
     ins(jnz, none, [sym(Fail)])],
    raw_access(Access, Index, Block, Ctx).
% A guarded renewal (docs/m7.md, round 5): the flight is loaded once.
% When the span test G passed, the bounds hold, and only the flags a
% renew tests and the alignment are tested here; otherwise the full
% check runs out of line (guard_slow_blocks//2). Both fail to the
% check's label with %rax:%rcx = P, so the report is the check's.
inst(fused(guarded(tmp(G), renew_if(_, Size, Rights, Align)), Access), Index, Block, Ctx) -->
    { access_pointer(Access, P),
      rights_write(Rights, Write),
      renew_mask(Write, Mask),
      check_fail_label(Ctx, k(Size, Write, Align), Fail),
      ctx_slot(Ctx, tmp(G), GOff), GDisp is -GOff,
      local_label(Ctx, Block, Index, full, Full),
      local_label(Ctx, Block, Index, access, Here) },
    flight_load(P, Ctx),
    [ins(cmp, l, [imm(0), mem(GDisp, rbp)]),
     ins(je, none, [sym(Full)]),
     ins(test, b, [imm(Mask), mem(-2, rcx)]),
     ins(jnz, none, [sym(Fail)])],
    align_check(Align, Fail),
    [label(Here)],
    raw_access(Access, Index, Block, Ctx).
inst(reused(Access), Index, Block, Ctx) -->
    { access_pointer(Access, P, Off), ctx_fn(Ctx, Fn), zero_offset(Access, Access0) },
    load(P, l, a, Fn),
    ( { Off =:= 0 } -> [] ; [ins(add, q, [imm(Off), reg(rax)])] ),
    raw_access(Access0, Index, Block, Ctx).
inst(fused(check_local(Name, Off, Size, Rights, Align), Access), I, B, Ctx) -->
    { rights_write(Rights, Write) },
    local_check(Name, Off, k(Size, Write, Align), I, B, Ctx),
    local_raw_access(Access, I, B, Ctx).
inst(abi(Actions), Index, Block, Ctx) --> abi_actions(Actions, Index, Block, Ctx).
inst(fence, _, _, _) --> [ins(mfence, none, [])].

% Check exact logical bounds without manufacturing a heap lower. Offset
% and size are the stack reporter's arguments. Address formation happens
% only after the full range/alignment check, even for constant accesses.
local_check(Name, Off, Kind, I, B, Ctx) -->
    { Kind = k(Bytes, _, Align), Mask is Align - 1,
      ctx_slot(Ctx, local(Name), local(Payload, Aux, Size, _)),
      P is -Payload, A is 8 - Aux, Limit is Size - Bytes,
      local_label(Ctx, B, I, localfail, Fail),
      local_label(Ctx, B, I, localok, Good),
      ctx_name(Ctx, FnName), check_origin_label(FnName, Kind, Origin),
      ctx_fn(Ctx, Fn) },
    load(const(Off), l, a, Fn), load(const(Size), l, c, Fn),
    load(const(Limit), l, d, Fn),
    [ins(test, q, [reg(rdx), reg(rdx)]), ins(js, none, [sym(Fail)]),
     ins(cmp, q, [reg(rdx), reg(rax)]), ins(ja, none, [sym(Fail)]),
     ins(test, q, [imm(Mask), reg(rax)]), ins(jnz, none, [sym(Fail)]),
     ins(jmp, none, [sym(Good)]), label(Fail),
     ins(mov, q, [reg(rax), reg(rdi)]), ins(mov, q, [reg(rcx), reg(rsi)]),
     ins(lea, q, [rip(Origin), reg(rdx)]),
     ins(call, none, [plt(filc_optimized_stack_access_check_fail)]),
     ins(ud2, none, []), label(Good)],
    local_address(Off, Limit, Mask, A, P).

% The addresses of the access's aux word and payload byte. The check
% has passed, so an offset outside 0..Limit or misaligned never gets
% here; any other offset is a constant displacement, which the register
% checker sees exactly (docs/perf.md item 3c). Otherwise index by %rax.
local_address(Off, Limit, Mask, A, P) -->
    { integer(Off), Off >= 0, Off =< Limit, Off /\ Mask =:= 0 }, !,
    { A1 is A + Off, P1 is P + Off },
    [ins(lea, q, [mem(A1, rbp), reg(rdx)]),
     ins(lea, q, [mem(P1, rbp), reg(rax)])].
local_address(_, _, _, A, P) -->
    [ins(lea, q, [mem(A, rbp, rax), reg(rdx)]),
     ins(lea, q, [mem(P, rbp, rax), reg(rax)])].

% kind_inst(+Kind, +K, +Op, +Args, +D, +Index, +Block, +Ctx)//: as
% inst//4, for tmp(D) =K Op Args with Op of Kind. Integer instructions go
% to amd64:compute_op//5; the pointer ones are by K, or (copy at p) by
% the operand.
kind_inst(Kind,K,Op,Args,D,_,_,Ctx) -->
    { x87_op(Kind, K, Op) }, !, x87_inst(Op, K, Args, D, Ctx).
kind_inst(float_convert,K,Op,Args,D,_,_,Ctx) --> integer_inst(Op,K,Args,D,Ctx).
kind_inst(float_to_int,K,Op,Args,D,_,_,Ctx) --> integer_inst(Op,K,Args,D,Ctx).
kind_inst(int_to_float,K,Op,Args,D,_,_,Ctx) --> integer_inst(Op,K,Args,D,Ctx).
kind_inst(cast,K,Op,Args,D,_,_,Ctx) --> integer_inst(Op,K,Args,D,Ctx).
kind_inst(additive, K, Op, Args, D, _, _, Ctx) -->
    additive_inst(K, Op, Args, D, Ctx).
kind_inst(alu, K, Op, Args, D, _, _, Ctx) -->
    integer_inst(Op, K, Args, D, Ctx).
kind_inst(shift, K, Op, Args, D, _, _, Ctx) -->
    integer_inst(Op, K, Args, D, Ctx).
kind_inst(neg, K, Op, Args, D, _, _, Ctx) -->
    integer_inst(Op, K, Args, D, Ctx).
kind_inst(copy, K, Op, Args, D, _, _, Ctx) -->
    copy_inst(K, Op, Args, D, Ctx).
% A span test (docs/m7.md, round 5): 1 when P0's lower is not null and
% lower =< P0+Lo < P0+Hi =< upper, unsigned, addresses modulo 2^64;
% else 0. It reads only what a full check reads and never traps.
kind_inst(span_test, w, span_test(Lo, Hi), [P0], D, Index, Block, Ctx) -->
    { local_label(Ctx, Block, Index, span0, Zero),
      local_label(Ctx, Block, Index, span1, Done) },
    flight_load(P0, Ctx),
    [ins(test, q, [reg(rcx), reg(rcx)]),
     ins(jz, none, [sym(Zero)])],
    span_end(Lo, rdx),
    [ins(cmp, q, [reg(rcx), reg(rdx)]),
     ins(jb, none, [sym(Zero)])],
    span_end(Hi, rax),
    [ins(cmp, q, [reg(rdx), reg(rax)]),
     ins(jbe, none, [sym(Zero)]),
     ins(cmp, q, [mem(-16, rcx), reg(rax)]),
     ins(ja, none, [sym(Zero)]),
     ins(mov, l, [imm(1), reg(eax)]),
     ins(jmp, none, [sym(Done)]),
     label(Zero),
     ins(xor, l, [reg(eax), reg(eax)]),
     label(Done)],
    reg_slot_store(rax, tmp(D), Ctx).
kind_inst(ptoi, l, _, [P], D, _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(P, l, a, Fn),
    reg_slot_store(rax, tmp(D), Ctx).
kind_inst(cmp, K, Op, Args, D, _, _, Ctx) -->
    integer_inst(Op, K, Args, D, Ctx).
kind_inst(ext, K, Op, Args, D, _, _, Ctx) -->
    integer_inst(Op, K, Args, D, Ctx).
kind_inst(alloc, p, alloc(Align), [N], D, _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(N, l, si, Fn),
    slot_reg_load(thread, rdi, Ctx),
    (   { Align >= 16 }
    ->  [ins(mov, l, [imm(Align), reg(edx)]),
         ins(call, none, [plt(filc_allocate_with_alignment)])]
    ;   [ins(call, none, [plt(filc_allocate)])]
    ),
    [ins(lea, q, [mem(16, rax), reg(rax)]),
     ins(mov, q, [reg(rax), reg(rcx)])],
    flight_store(D, Ctx).

setjmp(D, KindNo, Buf, Mask, Keys, Index, Block, Ctx) -->
    { ctx_fn(Ctx, Fn),
      ctx_slot(Ctx, lower(tmp(hidden(setjmp_buf(D)))), Off), NegOff is -Off,
      local_label(Ctx, Block, Index, setjmp_done, Done) },
    slot_reg_load(lower(setjmp_snapshot(D)), rdx, Ctx),
    setjmp_payload_copy(save, Keys, 0, Ctx),
    slot_reg_load(thread, rdi, Ctx),
    [ins(lea, q, [mem(NegOff, rbp), reg(rsi)]),
     ins(mov, l, [imm(KindNo), reg(edx)])],
    load(Mask, w, c, Fn),
    [ins(call, none, [plt(filc_jmp_buf_recreate)]),
     ins(mov, q, [reg(rax), reg(rcx)])],
    flight_store(hidden(setjmp_buf(D)), Ctx),
    checked_pointer_store(tmp(hidden(setjmp_buf(D))), Buf, Index, Block, Ctx),
    slot_reg_load(lower(tmp(hidden(setjmp_buf(D)))), rdi, Ctx),
    [ins(call, none, [plt('_setjmp')]),
     ins(test, l, [reg(eax), reg(eax)]),
     ins(jz, none, [sym(Done)])],
    slot_reg_load(lower(setjmp_snapshot(D)), rdx, Ctx),
    setjmp_payload_copy(restore, Keys, 0, Ctx),
    [label(Done)],
    reg_slot_store(rax, tmp(D), Ctx).

% RDX is the snapshot payload; RCX is scratch. EAX's full native int
% survives restoration, which contains no calls, polls or checked loads.
setjmp_payload_copy(_, [], _, _) --> [].
setjmp_payload_copy(Direction, [Key|Keys], Off, Ctx) -->
    payload_word_copy(Direction, Key, Off, Ctx),
    { Next is Off + 8 },
    setjmp_payload_copy(Direction, Keys, Next, Ctx).
payload_word_copy(save, Key, Off, Ctx) -->
    slot_reg_load(Key, rcx, Ctx),
    [ins(mov, q, [reg(rcx), mem(Off, rdx)])].
payload_word_copy(restore, Key, Off, Ctx) -->
    [ins(mov, q, [mem(Off, rdx), reg(rcx)])],
    reg_slot_store(rcx, Key, Ctx).

% integer_inst(+Op, +K, +Args, +D, +Ctx)//: the code of the integer
% instruction tmp(D) =K Op Args.
integer_inst(Op, K, Args, D, Ctx) -->
    { ctx_fn(Ctx, Fn), ctx_selection(Ctx, Selection) },
    compute_op(Selection, Op, K, Args, Fn),
    reg_slot_store(rax, tmp(D), Ctx).

% The helper returns payload and auxiliary *addresses*, not a flight
% pointer. Consume both without a safepoint, then root the loaded lower.
va_arg_load(w, D, _, _, Ctx) -->
    [ins(mov, l, [mem(0, rax), reg(eax)])],
    reg_slot_store(rax, tmp(D), Ctx).
va_arg_load(l, D, _, _, Ctx) -->
    [ins(mov, q, [mem(0, rax), reg(rax)])],
    reg_slot_store(rax, tmp(D), Ctx).
va_arg_load(x, D, _, _, Ctx) -->
    [ins(fld, t, [mem(0, rax)])], x87_pop(D, Ctx).
va_arg_load(s,D,I,B,Ctx) --> va_arg_load(w,D,I,B,Ctx).
va_arg_load(d,D,I,B,Ctx) --> va_arg_load(l,D,I,B,Ctx).
va_arg_load(p, D, Index, Block, Ctx) -->
    { local_label(Ctx, Block, Index, va_none, None),
      local_label(Ctx, Block, Index, va_have, Have) },
    [ins(xor, l, [reg(ecx), reg(ecx)]),
     ins(test, q, [reg(rdx), reg(rdx)]),
     ins(jz, none, [sym(None)]),
     ins(mov, q, [mem(0, rdx), reg(rcx)]),
     ins(test, b, [imm(1), reg(cl)]),
     ins(jz, none, [sym(Have)]),
     ins(and, q, [imm(-2), reg(rcx)]),
     ins(mov, q, [mem(8, rcx), reg(rcx)]),
     label(Have), label(None),
     ins(mov, q, [mem(0, rax), reg(rax)])],
    flight_store(D, Ctx).

/*  x87 long double (docs/float.md). An x temporary has a 16-byte wide
    slot, of which fldt and fstpt use the first 10 bytes. Each
    instruction pushes its operands on the x87 stack, computes and pops
    the stack empty again, so no value stays in an x87 register across
    instructions, calls or safepoints. Scalars and constants go through
    the red zone below %rsp: no call or signal frame can intervene
    within one instruction's sequence. */
x87_op(_, x, _).
x87_op(cmp, _, cmp(_, x)).
x87_op(float_convert, _, truncx).
x87_op(float_to_int, _, Op) :- memberchk(Op, [xtosi, xtoui]).

% x87_inst(+Op, +K, +Args, +D, +Ctx)//: tmp(D) =K Op Args, with x87.
% Operands go in reverse, so %st is the first and %st(1) the second.
x87_inst(Op, x, [A, B], D, Ctx) -->
    { memberchk(Op-I, [add-fadd, sub-fsub, mul-fmul, div-fdiv]) }, !,
    x87_push(B, Ctx), x87_push(A, Ctx),
    [ins(I, none, [reg('st(1)'), reg(st)])],
    x87_pop(D, Ctx), [ins(fstp, none, [reg('st(0)')])].
x87_inst(neg, x, [A], D, Ctx) --> !,
    x87_push(A, Ctx), [ins(fchs, none, [])], x87_pop(D, Ctx).
x87_inst(copy, x, [A], D, Ctx) --> !,
    x87_push(A, Ctx), x87_pop(D, Ctx).
x87_inst(cmp(Cond, x), w, [A, B], D, Ctx) --> !,
    x87_push(B, Ctx), x87_push(A, Ctx),
    [ins(fucomip, none, [reg('st(1)'), reg(st)]),
     ins(fstp, none, [reg('st(0)')])],
    float_condition(Cond),
    [ins(movzb, l, [reg(al), reg(eax)])],
    reg_slot_store(rax, tmp(D), Ctx).
x87_inst(ext(F), x, [A], D, Ctx) --> !,
    x87_push_float(F, A, Ctx), x87_pop(D, Ctx).
x87_inst(truncx, K, [A], D, Ctx) --> !,
    { x87_suffix(K, S, Mov), ( Mov == l -> R = eax ; R = rax ) },
    x87_push(A, Ctx),
    [ins(fstp, S, [mem(-8, rsp)]), ins(mov, Mov, [mem(-8, rsp), reg(R)])],
    reg_slot_store(rax, tmp(D), Ctx).
x87_inst(xtosi, K, [A], D, Ctx) --> !,
    x87_push(A, Ctx), x87_fisttp(K, D, Ctx).
x87_inst(xtoui, w, [A], D, Ctx) --> !,
    x87_push(A, Ctx), x87_fisttp(w, D, Ctx).
% Above 2^63, subtract 2^63, convert, and restore bit 63, as SSE2's
% unsigned qword conversion does (amd64:float_integer//4).
x87_inst(xtoui, l, [A], D, Ctx) --> !,
    x87_push(A, Ctx),
    [ins(mov, l, [imm(1593835520), mem(-12, rsp)]),
     ins(fld, s, [mem(-12, rsp)]),
     ins(fucomip, none, [reg('st(1)'), reg(st)]),
     ins(ja, none, [sym('1f')]),
     ins(fsub, s, [mem(-12, rsp)]),
     ins(fisttp, ll, [mem(-8, rsp)]),
     ins(mov, q, [mem(-8, rsp), reg(rax)]),
     ins(btc, q, [imm(63), reg(rax)]),
     ins(jmp, none, [sym('2f')]),
     label('1'),
     ins(fisttp, ll, [mem(-8, rsp)]),
     ins(mov, q, [mem(-8, rsp), reg(rax)]),
     label('2')],
    reg_slot_store(rax, tmp(D), Ctx).
x87_inst(Op, x, [A], D, Ctx) -->
    { memberchk(Op, [swtof, uwtof, sltof, ultof]), ctx_fn(Ctx, Fn) },
    x87_int_source(Op, A, Fn),
    [ins(mov, q, [reg(rax), mem(-8, rsp)]), ins(fild, ll, [mem(-8, rsp)])],
    x87_unsigned_fix(Op),
    x87_pop(D, Ctx).

% The integer operand in %rax, extended to 64 bits as Op reads it.
x87_int_source(swtof, A, Fn) --> load(A, w, a, Fn), [ins(movsl, q, [reg(eax), reg(rax)])].
x87_int_source(uwtof, A, Fn) --> load(A, w, a, Fn), [ins(mov, l, [reg(eax), reg(eax)])].
x87_int_source(sltof, A, Fn) --> load(A, l, a, Fn).
x87_int_source(ultof, A, Fn) --> load(A, l, a, Fn).

% fildll read an unsigned l with bit 63 set as negative: add 2^64,
% exactly, since the 64-bit significand holds every such sum.
x87_unsigned_fix(ultof) --> !,
    [ins(test, q, [reg(rax), reg(rax)]), ins(jns, none, [sym('1f')]),
     ins(mov, l, [imm(1602224128), mem(-12, rsp)]),
     ins(fadd, s, [mem(-12, rsp)]), label('1')].
x87_unsigned_fix(_) --> [].

% Truncate %st toward zero into tmp(D) of class K and pop it.
x87_fisttp(K, D, Ctx) -->
    { K == w -> Mov = l, R = eax ; Mov = q, R = rax },
    [ins(fisttp, ll, [mem(-8, rsp)]), ins(mov, Mov, [mem(-8, rsp), reg(R)])],
    reg_slot_store(rax, tmp(D), Ctx).

x87_suffix(s, s, l).
x87_suffix(d, l, q).

% x87_push(+V, +Ctx)//: push the x value V. A constant's 10 bytes go
% through the red zone, by %rdx, which no raw access holds.
x87_push(tmp(N), Ctx) -->
    { ctx_slot(Ctx, tmp(N), Off), Disp is -Off },
    [ins(fld, t, [mem(Disp, rbp)])].
x87_push(const(N), Ctx) -->
    { ctx_fn(Ctx, Fn), Lo is N /\ 0xffffffffffffffff, Hi is (N >> 64) /\ 0xffff },
    load(const(Lo), l, d, Fn),
    [ins(mov, q, [reg(rdx), mem(-16, rsp)]),
     ins(mov, w, [imm(Hi), mem(-8, rsp)]),
     ins(fld, t, [mem(-16, rsp)])].

% Push the s or d value V, widened exactly.
x87_push_float(F, V, Ctx) -->
    { ctx_fn(Ctx, Fn), x87_suffix(F, S, _) },
    load(V, F, a, Fn),
    [ins(mov, q, [reg(rax), mem(-8, rsp)]), ins(fld, S, [mem(-8, rsp)])].

% Pop %st into tmp(D)'s wide slot.
x87_pop(D, Ctx) -->
    { ctx_slot(Ctx, tmp(D), Off), Disp is -Off },
    [ins(fstp, t, [mem(Disp, rbp)])].

% additive_inst(+K, +Op, +Args, +D, +Ctx)//: scalar add or sub.
additive_inst(w, Op, Args, D, Ctx) --> integer_inst(Op, w, Args, D, Ctx).
additive_inst(l, Op, Args, D, Ctx) --> integer_inst(Op, l, Args, D, Ctx).
additive_inst(K,Op,Args,D,Ctx) -->
    { float_class(K) }, integer_inst(Op,K,Args,D,Ctx).

% copy_inst(+K, +Op, +Args, +D, +Ctx)//: a copy at K.
copy_inst(w, Op, Args, D, Ctx) --> integer_inst(Op, w, Args, D, Ctx).
copy_inst(l, Op, Args, D, Ctx) --> integer_inst(Op, l, Args, D, Ctx).
copy_inst(K,Op,Args,D,Ctx) -->
    { float_class(K) }, integer_inst(Op,K,Args,D,Ctx).

% Flight's inputs are all read before its destination is written. The
% second address uses %rdx, not the scalar ALU's %rcx, which holds the
% explicitly selected lower. No call or safepoint splits the pair.
flight_address_load(address(P), R, Ctx) --> !,
    { ctx_fn(Ctx, Fn) }, load(P, l, R, Fn).
flight_address_load(V, R, Ctx) -->
    { ctx_fn(Ctx, Fn) }, load(V, l, R, Fn).

flight_lower_load(lower(P), Ctx) --> lower_reg_load(P, rcx, Ctx).
flight_lower_load(none, _) --> [ins(xor, l, [reg(ecx), reg(ecx)])].

flight_calculation(copy, [], _) --> [].
flight_calculation(Op, [X], Ctx) -->
    { memberchk(Op, [add, sub]) },
    flight_address_load(X, d, Ctx),
    [ins(Op, q, [reg(rdx), reg(rax)])].

% raw_access(+Access, +Index, +Block, +Ctx)//: the code of the raw
% Access at P, the Indexth instruction of Block, after its check left P
% in %rax and its lower in %rcx.
raw_access(let(tmp(D), K, raw_load(T, 0), [_]), Index, Block, Ctx) -->
    raw_load(T, K, D, Index, Block, Ctx).
raw_access(raw_store(W, 0, V, P), Index, Block, Ctx) -->
    raw_store(W, V, P, Index, Block, Ctx).
raw_access(let(tmp(D), p, raw_load_pointer(0, Effects), [_]), I, B, Ctx) -->
    pointer_load_effects(Effects, I, B, Ctx),
    flight_store(D, Ctx).
raw_access(raw_store_pointer(0, V, P, Effects), I, B, Ctx) -->
    pointer_store_effects(Effects, V, P, I, B, Ctx).
raw_access(let(tmp(D), K, raw_cas(T, 0), [_, E, N]), _, _, Ctx) -->
    raw_cas(T, K, D, E, N, Ctx).

% raw_cas(+T, +K, +D, +E, +N, +Ctx)//: the cas(T) of Expected E and New
% N at the checked address in %rax (lower in %rcx), its old value into
% tmp(D) at class K (ir.pl). An integer is lock cmpxchg on the address
% in %rdx, Expected in %rax and New in %rcx; %rax is then old, extended
% as load(T) would. A pointer is Fil-C's
% filc_strong_cas_ptr_with_manual_tracking(thread, filc_ptr dest,
% offset, filc_ptr expected, filc_ptr new), as clang calls it: dest in
% %rsi/%rdx, offset 0 in %rcx, Expected's pair in %r8/%r9 and New's on
% the stack, the old pair back in %rax/%rdx. The helper checks again,
% ensures aux (it may exit), barriers New and boxes the slot; P and New
% stay rooted in their slots, and flight_store roots the result at once.
raw_cas(p, p, D, E, N, Ctx) --> !,
    { ctx_fn(Ctx, Fn) },
    [ins(mov, q, [reg(rax), reg(rsi)]),
     ins(mov, q, [reg(rcx), reg(rdx)])],
    origin_store(Ctx, c),
    slot_reg_load(thread, rdi, Ctx),
    load(E, l, r8, Fn),
    lower_reg_load(E, r9, Ctx),
    load(N, l, a, Fn),
    lower_reg_load(N, rcx, Ctx),
    [ins(sub, q, [imm(16), reg(rsp)]),
     ins(mov, q, [reg(rax), mem(0, rsp)]),
     ins(mov, q, [reg(rcx), mem(8, rsp)]),
     ins(xor, l, [reg(ecx), reg(ecx)]),
     ins(call, none, [plt(filc_strong_cas_ptr_with_manual_tracking)]),
     ins(add, q, [imm(16), reg(rsp)]),
     ins(mov, q, [reg(rdx), reg(rcx)])],
    flight_store(D, Ctx).
raw_cas(T, K, D, E, N, Ctx) -->
    { ctx_fn(Ctx, Fn), cas_operand(T, S, New) },
    [ins(mov, q, [reg(rax), reg(rdx)])],
    load(E, K, a, Fn),
    load(N, K, c, Fn),
    [ins('lock cmpxchg', S, [reg(New), mem(0, rdx)])],
    (   { T \== l, ext_insn(T, K, Ext) } -> [Ext] ; [] ),
    reg_slot_store(rax, tmp(D), Ctx).

% cas_operand(?T, ?S, ?New): a cas of type T is cmpxchg with suffix S,
% New in the part New of %rcx.
cas_operand(l, q, rcx).
cas_operand(sw, l, ecx). cas_operand(uw, l, ecx).
cas_operand(sh, w, cx).  cas_operand(uh, w, cx).
cas_operand(sb, b, cl).  cas_operand(ub, b, cl).

% %rax is the checked payload address, %rdx its explicit aux word.
% Neither register is an ordinary root. Only loaded/stored *contents*
% have heap lowers, and no helper or safepoint splits these operations.
local_raw_access(let(tmp(D), p, raw_load_pointer(0, Es), [_]), _, _, Ctx) --> !,
    local_load_effects(Es), flight_store(D, Ctx).
local_raw_access(raw_store_pointer(0, V, _, Es), _, _, Ctx) --> !,
    local_store_effects(Es, V, Ctx).
local_raw_access(Access, I, B, Ctx) --> raw_access(Access, I, B, Ctx).

local_load_effects([]) --> [].
local_load_effects([E|Es]) --> local_load_effect(E), local_load_effects(Es).
local_load_effect(aux_read) --> [ins(mov, q, [mem(0, rdx), reg(rcx)])].
local_load_effect(address_read) --> [ins(mov, q, [mem(0, rax), reg(rax)])].

local_store_effects([], _, _) --> [].
local_store_effects([E|Es], V, Ctx) -->
    local_store_effect(E, V, Ctx), local_store_effects(Es, V, Ctx).
local_store_effect(lower_write, V, Ctx) -->
    lower_reg_load(V, rcx, Ctx), [ins(mov, q, [reg(rcx), mem(0, rdx)])].
local_store_effect(address_write, V, Ctx) -->
    { ctx_fn(Ctx, Fn) }, load(V, l, si, Fn),
    [ins(mov, q, [reg(rsi), mem(0, rax)])].

rights_write(read, 0).
rights_write(write, 1).

% The effect list determines execution; only its caller publishes the
% result. No-aux jumps to lower_resolve's null arm. Resolving a box reads
% only its lower: address_read always reads the primary payload.
pointer_load_effects([], _, _, _) --> [].
pointer_load_effects([E|Es], I, B, Ctx) -->
    pointer_load_effect(E, I, B, Ctx), pointer_load_effects(Es, I, B, Ctx).

pointer_load_effect(aux_read, Index, Block, Ctx) -->
    { local_label(Ctx, Block, Index, nolower, NoLower) },
    aux_of_lower,
    [ins(jz, none, [sym(NoLower)]),
     ins(mov, q, [reg(rax), reg(rsi)]),
     ins(sub, q, [reg(rcx), reg(rsi)]),
     ins(mov, q, [mem(0, rdx, rsi), reg(rsi)])].
pointer_load_effect(lower_resolve, Index, Block, Ctx) -->
    { local_label(Ctx, Block, Index, nolower, NoLower),
      local_label(Ctx, Block, Index, have, Have) },
    [ins(test, b, [imm(1), reg(sil)]),
     ins(jz, none, [sym(Have)]),
     ins(and, q, [imm(-2), reg(rsi)]),
     ins(mov, q, [mem(8, rsi), reg(rsi)]),
     ins(jmp, none, [sym(Have)]),
     label(NoLower),
     ins(xor, l, [reg(esi), reg(esi)]),
     label(Have)].
% Fil-C's filc_load_ptr_atomic_with_manual_tracking_outline(filc_ptr):
% the checked pair in %rdi/%rsi, the result pair in %rax/%rdx. The pair
% leaves %rax/%rcx before origin_store, which uses %rax. The helper takes
% no thread and cannot exit; flight_store roots the result at once, as
% clang's frame slot does (no tracking call).
pointer_load_effect(atomic_read, _, _, Ctx) -->
    [ins(mov, q, [reg(rax), reg(rdi)]),
     ins(mov, q, [reg(rcx), reg(rsi)])],
    origin_store(Ctx, c),
    [ins(call, none, [plt(filc_load_ptr_atomic_with_manual_tracking_outline)]),
     ins(mov, q, [reg(rdx), reg(rcx)])].
pointer_load_effect(address_read, _, _, _) -->
    [ins(mov, q, [mem(0, rax), reg(rax)]),
     ins(mov, q, [reg(rsi), reg(rcx)])].

% raw_load(+T, +K, +D, +Index, +Block, +Ctx)//: a scalar load of type
% T at K into tmp(D). Pointer loads require their explicit effect list.
raw_load(l, K, D, _, _, Ctx) --> integer_load(l, K, D, Ctx).
raw_load(x, x, D, _, _, Ctx) --> [ins(fld, t, [mem(0, rax)])], x87_pop(D, Ctx).
raw_load(s, K, D, _, _, Ctx) --> integer_load(s, K, D, Ctx).
raw_load(d, K, D, _, _, Ctx) --> integer_load(d, K, D, Ctx).
raw_load(sw, K, D, _, _, Ctx) --> integer_load(sw, K, D, Ctx).
raw_load(uw, K, D, _, _, Ctx) --> integer_load(uw, K, D, Ctx).
raw_load(sh, K, D, _, _, Ctx) --> integer_load(sh, K, D, Ctx).
raw_load(uh, K, D, _, _, Ctx) --> integer_load(uh, K, D, Ctx).
raw_load(sb, K, D, _, _, Ctx) --> integer_load(sb, K, D, Ctx).
raw_load(ub, K, D, _, _, Ctx) --> integer_load(ub, K, D, Ctx).

integer_load(T, K, D, Ctx) -->
    { load_insn(T, K, LoadInsn) },
    [LoadInsn],
    reg_slot_store(rax, tmp(D), Ctx).

% checked_pointer_store(+V, +A, +Index, +Block, +Ctx)//: a store of the
% pointer V at A with its check, for an instruction whose store is
% internal (setjmp's jmp_buf).
checked_pointer_store(V, A, Index, Block, Ctx) -->
    { pointer_memory_effects(store, Effects) },
    flight_load(A, Ctx),
    access_check(k(8, 1, 8), Ctx),
    pointer_store_effects(Effects, V, A, Index, Block, Ctx).

% A pointer store may exit during ensure-aux. Reload both rooted inputs
% after the helpers, before writing the lower and then the address.
pointer_store_effects([], _, _, _, _, _) --> [].
pointer_store_effects([E|Es], V, A, I, B, Ctx) -->
    pointer_store_effect(E, V, A, I, B, Ctx),
    pointer_store_effects(Es, V, A, I, B, Ctx).

pointer_store_effect(aux_ensure, _, _, Index, Block, Ctx) -->
    { local_label(Ctx, Block, Index, haveaux, HaveAux) },
    aux_of_lower,
    [ins(jnz, none, [sym(HaveAux)])],
    slot_reg_load(thread, rdi, Ctx),
    [ins(lea, q, [mem(-16, rcx), reg(rsi)]),
     ins(call, none, [plt(filc_object_ensure_aux_ptr_outline)]),
     ins(mov, q, [reg(rax), reg(rdx)]),
     label(HaveAux)],
    reg_slot_store(rdx, aux, Ctx).
pointer_store_effect(lower_barrier, V, _, Index, Block, Ctx) -->
    { local_label(Ctx, Block, Index, nobarrier, NoBarrier) },
    lower_reg_load(V, rsi, Ctx),
    [ins(test, q, [reg(rsi), reg(rsi)]),
     ins(jz, none, [sym(NoBarrier)]),
     ins(mov, q, [gotpcrel(filc_current_marking_state), reg(rax)]),
     ins(cmp, l, [imm(0), mem(0, rax)]),
     ins(je, none, [sym(NoBarrier)])],
    slot_reg_load(thread, rdi, Ctx),
    [ins(call, none, [plt(filc_store_barrier_for_lower_slow)]),
     label(NoBarrier)].
pointer_store_effect(rooted_reload, V, A, _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    flight_load(A, Ctx),
    slot_reg_load(aux, rdx, Ctx),
    [ins(mov, q, [reg(rax), reg(r8)]),
     ins(sub, q, [reg(rcx), reg(r8)])],
    lower_reg_load(V, rsi, Ctx),
    load(V, l, r9, Fn).
% Fil-C's filc_store_ptr_atomic_outline(thread, filc_ptr dest, filc_ptr
% value): the checked destination in %rsi/%rdx, the value from its
% rooted slots in %rcx/%r8. The helper checks again, ensures aux (it may
% exit), barriers the value, boxes the slot and stores the pair
% atomically, then the address; V stays rooted throughout.
pointer_store_effect(atomic_write, V, _, _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    [ins(mov, q, [reg(rax), reg(rsi)]),
     ins(mov, q, [reg(rcx), reg(rdx)])],
    origin_store(Ctx, c),
    slot_reg_load(thread, rdi, Ctx),
    load(V, l, c, Fn),
    lower_reg_load(V, r8, Ctx),
    [ins(call, none, [plt(filc_store_ptr_atomic_outline)])].
pointer_store_effect(lower_write, _, _, _, _, _) -->
    [ins(mov, q, [reg(rsi), mem(0, rdx, r8)])].
pointer_store_effect(address_write, _, _, _, _, _) -->
    [ins(mov, q, [reg(r9), mem(0, rax)])].

% Scalar stores have no aux or barrier effects.
raw_store(b, V, _, _, _, Ctx) --> integer_store(b, V, Ctx).
raw_store(h, V, _, _, _, Ctx) --> integer_store(h, V, Ctx).
raw_store(w, V, _, _, _, Ctx) --> integer_store(w, V, Ctx).
raw_store(l, V, _, _, _, Ctx) --> integer_store(l, V, Ctx).
raw_store(s, V, _, _, _, Ctx) --> integer_store(s, V, Ctx).
raw_store(d, V, _, _, _, Ctx) --> integer_store(d, V, Ctx).
raw_store(x, V, _, _, _, Ctx) --> x87_push(V, Ctx), [ins(fstp, t, [mem(0, rax)])].

% The code of a store of the integer V of width W at %rax.
integer_store(W, V, Ctx) -->
    { ctx_fn(Ctx, Fn),
      width_value_class(W, ValueK),
      store_insn(W, d, StoreInsn) },
    load(V, ValueK, d, Fn),
    [StoreInsn].

% width_value_class(?W, ?K): an integer store of width W reads its value
% at class K.
width_value_class(b, w).
width_value_class(h, w).
width_value_class(w, w).
width_value_class(l, l).
width_value_class(s,s).
width_value_class(d,d).

/* A call through an already checked function, whose lower is in the
   aux slot. The fast entry if the signature matches the call site's,
   else the generic entry with every argument as an 8-byte word at
   thread+128+8i and its lower at thread+384+8i (docs/abi-findings.md). */
indirect_call(Sig, Form, Words, result(_,Channels), ArgsSize, Cells,
              GenericResult, Index, Block, Ctx) -->
    { ctx_fn(Ctx, Fn),
      special_label(Ctx, exc, Exc),
      local_label(Ctx, Block, Index, generic, Generic),
      local_label(Ctx, Block, Index, done, Done),
      local_label(Ctx, Block, Index, retok, RetOk),
      field(function_object, signature, rcx, FoSig),
      field(function_object, generic_entry, rsi, FoGeneric) },
    [ins(movabs, q, [imm(Sig), reg(rsi)]),
     ins(cmp, q, [reg(rsi), FoSig]),
     ins(jne, none, [sym(Generic)])],
    fast_call(Form, Words, indirect, Ctx),
    fast_result(Form, Channels, Ctx),
    [ins(jmp, none, [sym(Done)]),
     label(Generic)],
    { local_label(Ctx, Block, Index, outline, Outline) },
    outline_ensure(ArgsSize, Outline, Ctx),
    generic_call_args(Cells, Fn, Ctx),
    slot_reg_load(thread, rdi, Ctx),
    slot_reg_load(aux, rsi, Ctx),
    [ins(mov, l, [imm(ArgsSize), reg(edx)]),
     ins(call, q, [ind(FoGeneric)]),
     ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Exc)])],
    generic_results(GenericResult, RetOk, Ctx),
    [label(Done)].

% The generic result cells, after the product's required-size check.
generic_results(receive_generic(0, []), _, _) --> [].
generic_results(receive_generic(Need, [Cell|Cells]), RetOk, Ctx) -->
    slot_reg_load(thread, rsi, Ctx),
    rets_check(Need, RetOk),
    generic_slot_copies([Cell|Cells], Ctx).

% Arguments, the entry registers and the call itself, for the fast
% convention in form Form; Callee is direct(Symbol) or indirect (through
% the aux slot).
fast_call(Form, Ts, Callee, Ctx) -->
    { ctx_fn(Ctx, Fn),
      typed_locations(Ts, Form, Ls, NS, _),
      stack_bytes(NS, Pop) },
    reserve_stack(Pop),
    typed_stack_args(Ts, Ls, Fn, Ctx),
    typed_register_args(Ts, Ls, Fn, Ctx),
    entry_call(Form, Callee, Pop, Ctx),
    stack_release(Pop).
% The entry registers and the call of the fast entry of Callee. Pop is
% the stack words' size, which a buffered return's buffer sits above.
entry_call(reg, direct(Target), _, Ctx) -->
    slot_reg_load(thread, rdi, Ctx),
    [ins(xor, l, [reg(esi), reg(esi)]),
     ins(call, none, [Target])].
entry_call(reg, indirect, _, Ctx) -->
    slot_reg_load(thread, rdi, Ctx),
    slot_reg_load(aux, rsi, Ctx),
    { field(function_object, fast_entry, rsi, Fast) },
    [ins(call, q, [ind(Fast)])].
entry_call(mem(_), direct(Target), Pop, Ctx) -->
    slot_reg_load(thread, rsi, Ctx),
    [ins(lea, q, [mem(Pop, rsp), reg(rdi)]),
     ins(xor, l, [reg(edx), reg(edx)]),
     ins(call, none, [Target])].
entry_call(mem(_), indirect, Pop, Ctx) -->
    slot_reg_load(thread, rsi, Ctx),
    slot_reg_load(aux, rdx, Ctx),
    { field(function_object, fast_entry, rdx, Fast) },
    [ins(lea, q, [mem(Pop, rsp), reg(rdi)]),
     ins(call, q, [ind(Fast)])].

% has_exception, then the result slots from %rdx:%rcx or the buffer.
fast_result(reg, float(K,T), Ctx) -->
    { special_label(Ctx,exc,Exc) },
    [ins(test,b,[imm(1),reg(al)]),ins(jnz,none,[sym(Exc)])],
    from_xmm(K,xmm0,a), reg_slot_store(rax,T,Ctx).
fast_result(reg, typed(KTs), Ctx) -->
    { special_label(Ctx, exc, Exc) },
    [ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Exc)])],
    { result_registers(KTs, Rs) },
    typed_result_stores(KTs, Rs, Ctx).
fast_result(reg, slots(Slots), Ctx) -->
    { special_label(Ctx, exc, Exc) },
    [ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Exc)])],
    reg_slot_stores(Slots, [rdx, rcx], Ctx).
fast_result(mem(_), slots(Slots), Ctx) -->
    { special_label(Ctx, exc, Exc) },
    [ins(cmp, b, [imm(0), mem(0, rsp)]),
     ins(jne, none, [sym(Exc)])],
    buffer_slot_copies(Slots, 8, Ctx).

% result_registers(+KTs, -Rs): the register of each K-Slot word of a
% returned tuple, in order: integer words in %rdx then %rcx, float
% words in %xmm0 then %xmm1, as LLVM returns {i1, ...}.
result_registers(KTs, Rs) :- result_registers(KTs, [rdx, rcx], [xmm0, xmm1], Rs).
result_registers([], _, _, []).
result_registers([K-_|KTs], Gs, [X|Xs], [xmm(K,X)|Rs]) :-
    float_class(K), !, result_registers(KTs, Gs, Xs, Rs).
result_registers([_|KTs], [G|Gs], Xs, [gpr(G)|Rs]) :-
    result_registers(KTs, Gs, Xs, Rs).

% Integer registers first: a float word goes into its slot through %rax.
typed_result_stores(KTs, Rs, Ctx) -->
    typed_result_gprs(KTs, Rs, Ctx), typed_result_xmms(KTs, Rs, Ctx).
typed_result_gprs([], [], _) --> [].
typed_result_gprs([_-T|KTs], [R|Rs], Ctx) -->
    ( { R = gpr(G) } -> reg_slot_store(G, T, Ctx) ; [] ),
    typed_result_gprs(KTs, Rs, Ctx).
typed_result_xmms([], [], _) --> [].
typed_result_xmms([_-T|KTs], [R|Rs], Ctx) -->
    (   { R = xmm(K, X) } -> from_xmm(K, X, a), reg_slot_store(rax, T, Ctx)
    ;   []
    ),
    typed_result_xmms(KTs, Rs, Ctx).

% The store of each register into the matching slot.
reg_slot_stores([], _, _) --> [].
reg_slot_stores([Slot|Slots], [Reg|Regs], Ctx) -->
    reg_slot_store(Reg, Slot, Ctx),
    reg_slot_stores(Slots, Regs, Ctx).

% The copy of each buffer word into its slot; Slots start at Off(%rsp).
buffer_slot_copies([], _, _) --> [].
buffer_slot_copies([Slot|Slots], Off, Ctx) -->
    [ins(mov, q, [mem(Off, rsp), reg(rax)])],
    reg_slot_store(rax, Slot, Ctx),
    { Off1 is Off + 8 },
    buffer_slot_copies(Slots, Off1, Ctx).

% A generic return's words, from the thread at %rsi, into the slots.
generic_slot_copies([], _) --> [].
generic_slot_copies([cell(I, _, T, Lower)|Cells], Ctx) -->
    { generic_offsets(I, Off, LowerOff) },
    [ins(mov, q, [mem(Off, rsi), reg(rax)])],
    reg_slot_store(rax, T, Ctx),
    generic_lower_slot_copy(Lower, LowerOff, Ctx),
    generic_slot_copies(Cells, Ctx).

% For a p word at thread offset Off, its lower into lower(T).
generic_lower_slot_copy(lower(T), LowerOff, Ctx) -->
    [ins(mov, q, [mem(LowerOff, rsi), reg(rax)])],
    reg_slot_store(rax, lower(T), Ctx).
generic_lower_slot_copy(none, _, _) --> [].

% The check that the generic return size in %rdx is at least Need, with
% a call of filc_cc_rets_check_failure if it is not.
rets_check(Need, RetOk) -->
    [ins(cmp, q, [imm(Need), reg(rdx)]),
     ins(jae, none, [sym(RetOk)]),
     ins(mov, q, [reg(rdx), reg(rdi)]),
     ins(mov, l, [imm(Need), reg(esi)]),
     ins(xor, l, [reg(edx), reg(edx)]),
     ins(call, none, [plt(filc_cc_rets_check_failure)]),
     ins(ud2, none, []),
     label(RetOk)].

% The store of each argument into the thread's generic argument area.
% Invariant: Args are the arguments from argument I on.
generic_call_args([], _, _) --> [].
generic_call_args([cell(I, K, V, LowerSource)|Cells], Fn, Ctx) -->
    load(V, K, a, Fn),
    flight_lower_load(LowerSource, Ctx),
    slot_reg_load(thread, rdx, Ctx),
    cell_stores(I, rdx),
    generic_call_args(Cells, Fn, Ctx).

% cell_stores(+I, +Thread)//: argument cell I from %rax, its lower from
% %rcx, with the thread in register Thread: in the inline buffers, or
% for a cell past their 256 bytes in the outline ones (clobbering
% %rsi), as storeCC writes them.
cell_stores(I, T) -->
    { inline_cells(N), I < N }, !,
    { generic_offsets(I, Addr, Lower) },
    [ins(mov, q, [reg(rax), mem(Addr, T)]),
     ins(mov, q, [reg(rcx), mem(Lower, T)])].
cell_stores(I, T) -->
    { inline_cells(N), Off is 8 * (I - N),
      field(thread, cc_outline_buffer, T, Buf),
      field(thread, cc_outline_aux_buffer, T, AuxBuf) },
    [ins(mov, q, [Buf, reg(rsi)]), ins(mov, q, [reg(rax), mem(Off, rsi)]),
     ins(mov, q, [AuxBuf, reg(rsi)]), ins(mov, q, [reg(rcx), mem(Off, rsi)])].

inline_cells(32).

% outline_ensure(+Size, +Ctx)//: for an argument packet of Size bytes
% past the 256 inline ones, make the thread's outline buffers hold the
% rest (filc_thread_ensure_cc_outline_buffer), before any cell is set.
outline_ensure(Size, Ok, Ctx) -->
    (   { Size > 256 }
    ->  slot_reg_load(thread, rdi, Ctx), outline_ensure_rdi(Size, Ok)
    ;   []
    ).
outline_ensure_rdi(Size, Ok) -->
    (   { Size > 256 }
    ->  { Need is Size - 256,
          field(thread, cc_outline_size, rdi, Have) },
        [ins(cmp, q, [imm(Need), Have]), ins(jae, none, [sym(Ok)]),
         ins(mov, q, [imm(Need), reg(rsi)]),
         ins(call, none, [plt(filc_thread_ensure_cc_outline_buffer_slow)]),
         label(Ok)]
    ;   []
    ).

% With a flight pointer in %rax:%rcx, jump to Fail unless it points at a
% function object. Clobbers %rdx, %rsi and %rdi.
function_check(Fail) -->
    { aux_bits([special_type], TypeMask),
      aux_bits([function], Function),
      aux_pointer_mask(Mask) },
    [ins(test, q, [reg(rcx), reg(rcx)]),
     ins(jz, none, [sym(Fail)]),
     ins(mov, q, [mem(-8, rcx), reg(rdx)]),
     ins(movabs, q, [imm(TypeMask), reg(rsi)]),
     ins(and, q, [reg(rdx), reg(rsi)]),
     ins(movabs, q, [imm(Function), reg(rdi)]),
     ins(cmp, q, [reg(rdi), reg(rsi)]),
     ins(jne, none, [sym(Fail)]),
     ins(movabs, q, [imm(Mask), reg(rsi)]),
     ins(and, q, [reg(rsi), reg(rdx)]),
     ins(cmp, q, [reg(rdx), reg(rax)]),
     ins(jne, none, [sym(Fail)])].

% The aux pointer of the object at lower %rcx into %rdx, setting ZF if
% it has none.
aux_of_lower -->
    { aux_pointer_mask(Mask) },
    [ins(mov, q, [mem(-8, rcx), reg(rdx)]),
     ins(movabs, q, [imm(Mask), reg(rsi)]),
     ins(and, q, [reg(rsi), reg(rdx)])].


% A word into register R, an amd64 register short name (a, d, c, r8...).
word_reg_load(addr(V), R, Fn, _) --> load(V, l, R, Fn).
word_reg_load(val(K, V), R, Fn, _) --> load(V, K, R, Fn).
word_reg_load(lower(V), R, _, Ctx) -->
    { reg_name(R, l, RN) },
    lower_reg_load(V, RN, Ctx).

%% The fast convention as data. A signature is a list of words
%% wf(Class, Source): one per w, l, s or d value and two (address, then
%% lower, both l) per p. typed_locations/5 places each word: integer
%% words in the form's registers, s and d in %xmm0-7, the rest in stack
%% words stack(I) at 8I(%rsp) at the call. Entries, call sites, the
%% generic entry, the variadic adapter and external thunks all read
%% this one placement, so they agree by construction.
typed_locations(Ts,Form,Ls,NS,NX) :-
    findall(K,member(wf(K,_),Ts),Ks), form_short_regs(Form,Rs),
    bank_locations(Ks,Rs,Ls,NS,NX).
% stack_bytes(+NS, -Bytes): NS stack words take Bytes, keeping %rsp
% 16-aligned at the call.
stack_bytes(NS, Bytes) :- Bytes is (NS + 1) // 2 * 16.

reserve_stack(0) --> [].
reserve_stack(N) --> { N>0 }, [ins(sub,q,[imm(N),reg(rsp)])].

typed_incoming([],[],_) --> [].
typed_incoming([wf(K,T)|Ts],[L|Ls],Ctx) -->
    incoming_word(L,K,T,Ctx), typed_incoming(Ts,Ls,Ctx).

% An integer register word goes straight to its slot; others via %rax.
incoming_word(reg(R),_,T,Ctx) --> !,
    { reg_name(R,l,RN) }, reg_slot_store(RN,T,Ctx).
incoming_word(L,K,T,Ctx) --> incoming_bits(L,K), reg_slot_store(rax,T,Ctx).
incoming_bits(reg(R),_) -->
    { reg_name(R,l,RN) }, [ins(mov,q,[reg(RN),reg(rax)])].
incoming_bits(xreg(X),K) --> from_xmm(K,X,a).
incoming_bits(stack(I),K) -->
    { O is 16+8*I, att_suffix(K,S), reg_name(a,K,A) },
    [ins(mov,S,[mem(O,rbp),reg(A)])].

typed_stack_args([],[],_,_) --> [].
typed_stack_args([wf(_,W)|Ts],[L|Ls],Fn,Ctx) -->
    ( { L=stack(I), O is 8*I }
    -> word_reg_load(W,a,Fn,Ctx), [ins(mov,q,[reg(rax),mem(O,rsp)])]
    ; [] ), typed_stack_args(Ts,Ls,Fn,Ctx).
typed_register_args([],[],_,_) --> [].
typed_register_args([wf(K,W)|Ts],[L|Ls],Fn,Ctx) -->
    typed_register_arg(L,K,W,Fn,Ctx), typed_register_args(Ts,Ls,Fn,Ctx).
typed_register_arg(stack(_),_,_,_,_) --> [].
typed_register_arg(reg(R),_,W,Fn,Ctx) --> word_reg_load(W,R,Fn,Ctx).
typed_register_arg(xreg(X),K,W,Fn,Ctx) -->
    word_reg_load(W,a,Fn,Ctx), to_xmm(K,a,X).

% Adapter sources are operands (thread/snapshot/saved stack), not IR
% values. Load all stack words first, then registers; only RAX is scratch.
adapter_stack([],[],_) --> [].
adapter_stack([wf(K,W)|Ts],[L|Ls],G) -->
    ( { L=stack(I), O is 8*I }
    -> adapter_load(K,W,G), [ins(mov,q,[reg(rax),mem(O,rsp)])]
    ; [] ), adapter_stack(Ts,Ls,G).
adapter_registers([],[],_) --> [].
adapter_registers([wf(K,W)|Ts],[L|Ls],G) -->
    adapter_register(L,K,W,G), adapter_registers(Ts,Ls,G).
adapter_register(stack(_),_,_,_) --> [].
adapter_register(reg(R),K,mem(O,B),_) -->
    { K \== s }, !, { reg_name(R,l,RN) },
    [ins(mov,q,[mem(O,B),reg(RN)])].
adapter_register(reg(R),K,W,G) -->
    adapter_load(K,W,G), { reg_name(R,l,RN) },
    [ins(mov,q,[reg(rax),reg(RN)])].
adapter_register(xreg(X),K,W,G) --> adapter_load(K,W,G), to_xmm(K,a,X).
adapter_load(K,W,G) -->
    snapshot_load(W,G),
    ( { K == s } -> [ins(mov,l,[reg(eax),reg(eax)])] ; [] ).

% Physical operands for the already flattened adapter sources.
adapter_word(Area, wf(K,Source), wf(K,Operand)) :-
    adapter_operand(Area, Source, Operand).
adapter_operand(thread, Source, mem(Off,rbx)) :- channel_offset(Source,Off).
adapter_operand(snapshot, data(I), mem(Off,r12)) :- Off is 8*I.
adapter_operand(snapshot, aux(I), snapshot_lower(Off)) :- Off is 8*I.
adapter_operand(snapshot, snapshot, reg(r12)).
saved_operand(saved(I), mem(Off,rbp)) :- Off is -32-8*I.


/* thunk(+Product)//: the lowered weak thunk resolves its symbol through
   the getter and calls the fast entry when the supplied signature matches,
   else transports its generic cells and result channels. Every incoming word,
   integer or XMM, is saved below rbp before the getter can exit or
   clobber caller-saved registers; rbx holds the thread (r12 the return
   buffer) and -24(%rbp) the function object. Pointer authority stays
   rooted by the caller. */
thunk(thunk(F,Ref,Sig,Ts,Cells,ArgsSize,Result,Need)) -->
    { abi_symbol(entry(Sig),F,FI), abi_symbol(getter,F,Getter),
      atom_concat('.L',FI,G),atom_concat(G,'.generic',Generic),
      atom_concat(G,'.out',Out),atom_concat(G,'.fail',Fail),
      atom_concat(G,'.retok',RetOk),atom_concat(G,'.exc',Exc),
      Result = adapter_result(Return,Channel,_,Packet),
      target_form(Return,Form), packet_offsets(Packet,packet(Srcs,_)),
      typed_locations(Ts,Form,Ls,NS,_), stack_bytes(NS, Pop),
      saved_words(Ts,0,Saved),length(Ts,NW),Alloc is ((8+8*NW+15)//16)*16,
      field(function_object,generic_entry,rsi,GenericEntry),
      ( Sig = never(_) -> never_signature(SigV) ; SigV = Sig ) },
    [section(text),p2align(4)],
    ( { Ref == local } -> [] ; [hidden(FI),weak(FI)] ),
    [type(FI,function),label(FI),
     ins(push,q,[reg(rbp)]),ins(mov,q,[reg(rsp),reg(rbp)]),
     ins(push,q,[reg(rbx)]),ins(push,q,[reg(r12)]),
     ins(sub,q,[imm(Alloc),reg(rsp)])],
    mixed_thunk_thread(Form), save_mixed_words(Ts,Ls,Saved),
    thunk_getter(Ref,Getter,G),
    function_check(Fail),
    { field(function_object,signature,rcx,Signature) },
    [ins(mov,q,[reg(rcx),mem(-24,rbp)]),
     ins(movabs,q,[imm(SigV),reg(rsi)]),ins(cmp,q,[reg(rsi),Signature]),
     ins(jne,none,[sym(Generic)])],
    reserve_stack(Pop),adapter_stack(Saved,Ls,G),adapter_registers(Saved,Ls,G),
    mixed_thunk_call(Form),
    [ins(jmp,none,[sym(Out)]),label(Generic)],
    thunk_outline_ensure(ArgsSize,G),
    saved_generic(Cells),
    [ins(mov,q,[reg(rbx),reg(rdi)]),ins(mov,q,[mem(-24,rbp),reg(rsi)]),
     ins(mov,l,[imm(ArgsSize),reg(edx)]),
     ins(call,q,[ind(GenericEntry)]),ins(test,b,[imm(1),reg(al)])],
    thunk_generic_return(Form,Channel,Need,Srcs,Out,RetOk,Exc),
    [label(Fail),ins(mov,q,[reg(rax),reg(rdi)]),ins(mov,q,[reg(rcx),reg(rsi)]),
     ins(call,none,[plt(filc_check_function_call_fail)]),ins(ud2,none,[]),
     label(Out),ins(lea,q,[mem(-16,rbp),reg(rsp)]),
     ins(pop,q,[reg(r12)]),ins(pop,q,[reg(rbx)]),ins(pop,q,[reg(rbp)]),
     ins(ret,none,[]),size(FI)].

% The callee's function object in %rax:%rcx. A weak declaration's
% getter may be null, and then so is the object: the function check
% fails, as clang's thunk does.
thunk_getter(local,Getter,G) --> thunk_getter(strong,Getter,G).
thunk_getter(strong,Getter,_) -->
    [ins(xor,l,[reg(esi),reg(esi)]),ins(call,none,[plt(Getter)]),
     ins(mov,q,[reg(rdx),reg(rcx)])].
thunk_getter(weak,Getter,G) -->
    { atom_concat(G,'.null',Null), atom_concat(G,'.got',Got) },
    [ins(cmp,q,[imm(0),gotpcrel(Getter)]),ins(je,none,[sym(Null)])],
    thunk_getter(strong,Getter,G),
    [ins(jmp,none,[sym(Got)]),label(Null),
     ins(xor,l,[reg(eax),reg(eax)]),ins(xor,l,[reg(ecx),reg(ecx)]),label(Got)].

saved_words([],_,[]).
saved_words([wf(K,_)|Ts],I,[wf(K,mem(O,rbp))|Ss]) :-
    O is -32-8*I,I1 is I+1,saved_words(Ts,I1,Ss).
mixed_thunk_thread(reg) --> [ins(mov,q,[reg(rdi),reg(rbx)])].
mixed_thunk_thread(mem(_)) -->
    [ins(mov,q,[reg(rdi),reg(r12)]),ins(mov,q,[reg(rsi),reg(rbx)]),
     ins(mov,q,[reg(rsi),reg(rdi)])].
save_mixed_words([],[],[]) --> [].
% A thunk copies an integer stack word whole, as a register one: w and l
% share a signature digit, so one emitted for a 32-bit call also serves
% another object's 64-bit calls (the linker keeps one weak thunk).
save_mixed_words([wf(K0,_)|Ts],[L|Ls],[wf(_,W)|Ss]) -->
    { K0 == w -> K = l ; K = K0 },
    incoming_bits(L,K),[ins(mov,q,[reg(rax),W])],save_mixed_words(Ts,Ls,Ss).
mixed_thunk_call(reg) -->
    { field(function_object,fast_entry,rsi,Fast) },
    [ins(mov,q,[reg(rbx),reg(rdi)]),ins(mov,q,[mem(-24,rbp),reg(rsi)]),
     ins(call,q,[ind(Fast)])].
mixed_thunk_call(mem(_)) -->
    { field(function_object,fast_entry,rdx,Fast) },
    [ins(mov,q,[reg(r12),reg(rdi)]),ins(mov,q,[reg(rbx),reg(rsi)]),
     ins(mov,q,[mem(-24,rbp),reg(rdx)]),ins(call,q,[ind(Fast)])].
thunk_outline_ensure(ArgsSize,G) -->
    (   { ArgsSize > 256 }
    ->  { atom_concat(G,'.outline',Outline) },
        [ins(mov,q,[reg(rbx),reg(rdi)])], outline_ensure_rdi(ArgsSize,Outline)
    ;   []
    ).

% Inline cells go straight to the thread at %rbx; later ones through
% cell_stores//2 into the outline buffers.
saved_generic([]) --> [].
saved_generic([cell(I,_,Data,saved(L))|Cells]) -->
    { inline_cells(N), I < N }, !,
    { generic_offsets(I,AO,LO), saved_operand(Data,A), saved_operand(saved(L),Lower) },
    operand_thread_store(A,AO),operand_thread_store(Lower,LO),saved_generic(Cells).
saved_generic([cell(I,K,Data,none)|Cells]) -->
    { inline_cells(N), I < N }, !,
    { generic_offsets(I,AO,LO), saved_operand(Data,W) },
    adapter_load(K,W,unused),
    [ins(mov,q,[reg(rax),mem(AO,rbx)]),ins(mov,q,[imm(0),mem(LO,rbx)])],
    saved_generic(Cells).
saved_generic([cell(I,_,Data,saved(L))|Cells]) -->
    { saved_operand(Data,mem(AD,AB)), saved_operand(saved(L),mem(LD,LB)) },
    [ins(mov,q,[mem(AD,AB),reg(rax)]),ins(mov,q,[mem(LD,LB),reg(rcx)]),
     ins(mov,q,[reg(rbx),reg(rdx)])],
    cell_stores(I,rdx), saved_generic(Cells).
saved_generic([cell(I,K,Data,none)|Cells]) -->
    { saved_operand(Data,W) },
    adapter_load(K,W,unused),
    [ins(xor,l,[reg(ecx),reg(ecx)]),ins(mov,q,[reg(rbx),reg(rdx)])],
    cell_stores(I,rdx), saved_generic(Cells).

%% Access checks: k(Size, Write, Align), with the pointer in %rax and its
%% lower in %rcx, which the failure block passes on.

% A jump to the kind's failure block unless the pointer may be accessed:
% lower not 0, lower =< ptr =< upper - Size, the object's flags
% permitting a write if Write is 1, and ptr 8-aligned if Align is 8.
access_check(k(Size, Write, Align), Ctx) -->
    { check_fail_label(Ctx, k(Size, Write, Align), Fail),
      ctx_selection(Ctx, Selection) },
    [ins(test, q, [reg(rcx), reg(rcx)]),
     ins(jz, none, [sym(Fail)]),
     ins(cmp, q, [reg(rcx), reg(rax)]),
     ins(jb, none, [sym(Fail)]),
     ins(mov, q, [mem(-16, rcx), reg(rdx)]),
     ins(sub, q, [imm(Size), reg(rdx)])],
    borrow_check(Selection, Size, Fail),
    [ins(cmp, q, [reg(rdx), reg(rax)]),
     ins(ja, none, [sym(Fail)])],
    write_check(Write, Fail),
    align_check(Align, Fail).

% The borrow test of upper - Size. Local selection drops it for Size =<
% 16: a nonnull lower has its 16-byte header below it and upper >= lower,
% so upper >= 16 >= Size (docs/perf.md, item 6a). Checked IR may state
% larger sizes (tests/filc/check-range.ir), which keep it.
borrow_check(Selection, Size, Fail) -->
    (   { Selection == local, Size =< 16 } -> []
    ;   [ins(jb, none, [sym(Fail)])]
    ).

% span_end(+Off, +Reg)//: Reg = %rax + Off, modulo 2^64, leaving %rax;
% an offset beyond 32 bits goes through %rsi, a scratch register no
% temporary is homed in.
span_end(Off, Reg) -->
    (   { Off >= -2147483648, Off =< 2147483647 }
    ->  [ins(lea, q, [mem(Off, rax), reg(Reg)])]
    ;   { U is Off mod 18446744073709551616 },
        [ins(movabs, q, [imm(U), reg(rsi)]),
         ins(lea, q, [mem(0, rax, rsi), reg(Reg)])]
    ).

% guard_slow_blocks(+Blocks, +Ctx)//: for each guarded renewal, the full
% check it runs when its span test failed, out of line, then back to its
% access. %rax:%rcx still hold P from its flight load.
guard_slow_blocks(Blocks, Ctx) -->
    { findall(slow(L, I, K),
              ( member(block(L, _, Is, _), Blocks),
                nth0(I, Is, fused(guarded(_, renew_if(_, Size, Rights, Align)), _)),
                rights_write(Rights, W), K = k(Size, W, Align) ),
              Slows) },
    guard_slows(Slows, Ctx).

guard_slows([], _) --> [].
guard_slows([slow(L, I, K)|Slows], Ctx) -->
    { local_label(Ctx, L, I, full, Full),
      local_label(Ctx, L, I, access, Here) },
    [label(Full)],
    access_check(K, Ctx),
    [ins(jmp, none, [sym(Here)])],
    guard_slows(Slows, Ctx).

% renew_mask(+Write, -Mask): the flags a renew tests, FREE (4) and, for a
% write, READONLY (2) (filc_runtime.h).
renew_mask(0, 4).
renew_mask(1, 6).

% For a write (Write = 1), a check of the object's read-only flags.
write_check(0, _) --> [].
write_check(1, Fail) -->
    [ins(test, b, [imm(6), mem(-2, rcx)]),
     ins(jnz, none, [sym(Fail)])].

% For Align = 2, 4 or 8, a check that the pointer is so aligned.
align_check(1, _) --> [].
align_check(2, Fail) -->
    [ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Fail)])].
align_check(4, Fail) -->
    [ins(test, b, [imm(3), reg(al)]),
     ins(jnz, none, [sym(Fail)])].
align_check(8, Fail) -->
    [ins(test, b, [imm(7), reg(al)]),
     ins(jnz, none, [sym(Fail)])].

% The labels of a check kind's failure block and origin.
check_fail_label(Ctx, k(Size, Write, Align), Label) :-
    ctx_name(Ctx, Name),
    label_atom(['.L', Name, '..fail.', Size, '.', Write, '.', Align], Label).

check_origin_label(Name, k(Size, Write, Align), Label) :-
    format(atom(Label), '.L~w..chk.~w.~w.~w', [Name, Size, Write, Align]).

% The distinct check kinds the function's accesses need.
access_check_kinds(Blocks, Kinds) :-
    findall(Kind,
            (   member(block(_, _, Insts, _), Blocks),
                member(Inst, Insts),
                inst_check_kind(Inst, Kind)
            ),
            Kinds0),
    sort(Kinds0, Kinds).

% inst_check_kind(+Inst, -Kind): Inst's access needs a check of Kind;
% fails if Inst does not access memory.
inst_check_kind(fused(check(_, Size, Rights, Align), _), k(Size, Write, Align)) :-
    rights_write(Rights, Write).
inst_check_kind(fused(renew(_, Size, Rights, Align), _), k(Size, Write, Align)) :-
    rights_write(Rights, Write).
inst_check_kind(fused(guarded(_, renew_if(_, Size, Rights, Align)), _), k(Size, Write, Align)) :-
    rights_write(Rights, Write).
inst_check_kind(fused(check_local(_, _, Size, Rights, Align), _), k(Size, Write, Align)) :-
    rights_write(Rights, Write).
inst_check_kind(abi(Actions), k(8, 1, 8)) :-
    memberchk(returns_twice(_,_,_,_,_), Actions).

% A failure block for each check kind, calling the runtime's reporter.
check_fail_blocks([], _) --> [].
check_fail_blocks([Kind|Kinds], Ctx) -->
    { check_fail_label(Ctx, Kind, Fail),
      ctx_name(Ctx, Name),
      check_origin_label(Name, Kind, Origin) },
    [label(Fail),
     ins(mov, q, [reg(rax), reg(rdi)]),
     ins(mov, q, [reg(rcx), reg(rsi)]),
     ins(lea, q, [rip(Origin), reg(rdx)]),
     ins(call, none, [plt(filc_optimized_access_check_fail)]),
     ins(ud2, none, [])],
    check_fail_blocks(Kinds, Ctx).

%% Function objects: every function gets a getter, a generic entry and a
%% function object, so its address can be taken; exported ones also get
%% the FI alias and a global getter.

% Generic-only public entry, with a private fast body. Promotion is the
% only exiting call before the body roots the hidden snapshot parameter.
variadic_object(Name, Linkage, Adapter, Impl) -->
    { abi_symbol(function_object, Name, FO),
      abi_symbol(getter, Name, Getter),
      abi_symbol(impl(0), Name, Generic),
      abi_symbol(entry(0), Name, FI),
      atom_concat(Generic, '.body', BodyObject) },
    linkage_alias(Linkage, FI, Generic, Getter),
    object_getter(Getter, FO),
    variadic_adapter(Generic, BodyObject, Adapter),
    [section(data_rel_ro), p2align(4), label(BodyObject), quad(Impl)],
    function_object_data(FO, 0, Generic, 0).

variadic_adapter(Generic, BodyObject, promote_incoming(Need,Words,Result)) -->
    { Result = adapter_result(Return,Channel,RetSize,Packet),
      target_form(Return, Form), packet_offsets(Packet, PlacedPacket),
      maplist(adapter_word(snapshot), Words, Ts),
      typed_locations(Ts, Form, Ls, NS, _),
      stack_bytes(NS, Pop),
      atom_concat(Generic, '.short', Short),
      atom_concat(Generic, '.done', Done) },
    [section(text), type(Generic, function), label(Generic),
     ins(push, q, [reg(rbx)]), ins(push, q, [reg(r12)]),
     ins(push, q, [reg(r13)]),
     ins(cmp, q, [imm(Need), reg(rdx)]),
     ins(jb, none, [sym(Short)]),
     ins(mov, q, [reg(rdi), reg(rbx)]),
     ins(mov, q, [reg(rdx), reg(rsi)]),
     ins(call, none, [plt(filc_promote_args_to_heap)]),
     ins(mov, q, [reg(rax), reg(r12)]),
     ins(xor, l, [reg(r13d), reg(r13d)]),
     ins(test, q, [reg(rdx), reg(rdx)])],
    { atom_concat(Generic, '.aux', Aux),
      aux_pointer_mask(Mask) },
    [ins(jz, none, [sym(Aux)]),
     ins(mov, q, [mem(-8, rdx), reg(r13)]),
     ins(movabs, q, [imm(Mask), reg(rax)]),
     ins(and, q, [reg(rax), reg(r13)]), label(Aux)],
    ret_buffer_reservation(Form),
    reserve_stack(Pop),
    adapter_stack(Ts, Ls, Generic),
    adapter_registers(Ts, Ls, Generic),
    [ins(mov, q, [reg(rbx), reg(rdi)]),
     ins(lea, q, [rip(BodyObject), reg(rsi)])],
    generic_entry_call(Form, Channel, PlacedPacket, Pop, RetSize, Done),
    [ins(pop, q, [reg(r13)]), ins(pop, q, [reg(r12)]),
     ins(pop, q, [reg(rbx)]), ins(ret, none, []),
     label(Short), ins(mov, q, [reg(rdx), reg(rdi)]),
     ins(mov, l, [imm(Need), reg(esi)]),
     ins(xor, l, [reg(edx), reg(edx)]),
     ins(call, none, [plt(filc_cc_args_check_failure)]),
     ins(ud2, none, [])].

snapshot_load(reg(R), _) --> [ins(mov, q, [reg(R), reg(rax)])].
snapshot_load(mem(O, R), _) --> [ins(mov, q, [mem(O, R), reg(rax)])].
snapshot_load(snapshot_lower(O), G) -->
    { format(atom(NoAux), '~w.lower.~w', [G, O]) },
    [ins(xor, l, [reg(eax), reg(eax)]),
     ins(test, q, [reg(r13), reg(r13)]),
     ins(jz, none, [sym(NoAux)]),
     ins(mov, q, [mem(O, r13), reg(rax)]), label(NoAux)].

function_object(Name, Linkage, Adapter, Sig, Impl) -->
    { abi_symbol(entry(Sig), Name, FI),
      abi_symbol(function_object, Name, FO),
      abi_symbol(getter, Name, Getter),
      format(atom(Generic), '.L~w..generic', [Name]) },
    linkage_alias(Linkage, FI, Impl, Getter),
    object_getter(Getter, FO),
    generic_entry(Generic, Adapter),
    local_entry(Linkage, Impl, Fast),
    [section(data_rel_ro), p2align(4)],
    function_object_data(FO, Fast, Generic, Sig).

% local_entry(+Linkage, +Impl, -Fast)//: the symbol a function object
% names its fast entry by. A global Impl is preemptible, so the dynamic
% linker would bind the object's word to the first definition of that
% name it loaded: every HDF5 plugin netcdf opens with RTLD_GLOBAL
% defines H5PLget_plugin_info, and each one's object called the first
% one's. clang's names a local alias, .L<Impl>.local, bound at link
% time (docs/abi-findings.md, *Function objects name a local alias*).
local_entry(local, Impl, Impl) --> !.
local_entry(_, Impl, Fast) -->
    { format(atom(Fast), '.L~w.local', [Impl]) },
    [type(Fast, function), set(Fast, Impl)].

% alias_getter(+Symbols, +Name, +Linkage, +Target)//: an alias's getter
% returns its target's getter's result, so the alias's function or data
% object is the target's, as Fil-C's (filc_alias_global): it calls the
% target's getter, directly when the target is local, else through the
% PLT, with the stack kept 16-aligned.
alias_getter(Symbols, Name, Linkage, Target) -->
    { abi_symbol(getter, Name, Getter), abi_symbol(getter, Target, TG),
      (   ( func_named(Symbols, Target, func(_, local, _, _, _))
          ; ir:data_item(Symbols, Target, data(_, L, _, _)), memberchk(L, [local, ro(local)]) )
      ->  Op = sym(TG)
      ;   Op = plt(TG)
      ) },
    [section(text)],
    linkage_globl(Linkage, Getter),
    [type(Getter, function), label(Getter),
     ins(push, q, [reg(rax)]),
     ins(call, none, [Op]),
     ins(pop, q, [reg(rcx)]),
     ins(ret, none, [])].

% The getter of a function object FO: its flight pointer, whose lower is
% its address, in %rax:%rdx.
object_getter(Getter, FO) -->
    [type(Getter, function), label(Getter),
     ins(lea, q, [rip(FO+16), reg(rax)]),
     ins(mov, q, [reg(rax), reg(rdx)]),
     ins(ret, none, [])].

% The function object FO with the entries Fast and Generic (symbols, or
% 0 for none) and signature Sig. Its header has upper = lower, so it
% cannot be read or written, and an aux word that points at itself.
function_object_data(FO, Fast, Generic, Sig) -->
    { aux_bits([global, readonly, function], Flags) },
    [type(FO, object), label(FO),
     quad(FO+16),
     quad(FO+16+Flags),
     quad(Fast),
     quad(Generic),
     quad(Sig),
     size(FO, 40)].

% An exported function's FI alias of Impl and its global Getter.
linkage_alias(export, FI, Impl, Getter) -->
    [globl(FI), type(FI, function), set(FI, Impl), globl(Getter)].
linkage_alias(local, _, _, _) --> [].
% A weak function has a weak getter and no FI alias, as clang's: callers
% elsewhere go through their thunks to whichever definition the linker
% keeps.
linkage_alias(weak, _, _, Getter) --> [weak(Getter)].

% The .globl of S if its linkage is export.
linkage_globl(export, S) --> [globl(S)].
linkage_globl(local, _) --> [].
linkage_globl(weak, S) --> [weak(S)].

%% Data objects, as clang lays out globals (docs/abi-findings.md):
%% DO_d = {upper, aux} then the payload rounded up to 8 bytes, a 16-byte
%% cache GP_d, an aux array DA_d if the payload holds pointers, and a
%% getter whose slow path registers the object and runs the relocations
%% that fill in its pointers. A payload aligned to more than 16 has
%% Align - 16 zero bytes before DO_d, so that DO_d + 16 is aligned.

data_object(Name, Linkage0, Align, Items) -->
    { linkage_flags(Linkage0, Linkage, Flags),
      abi_symbol(data_object, Name, DO),
      abi_symbol(data_aux, Name, DA),
      format(atom(GP), '.LpizlonatedGP_~w', [Name]),
      abi_symbol(getter, Name, Getter),
      format(atom(Relocs), '.Lpizlonated_~w..relocs', [Name]),
      format(atom(Slow), '.Lpizlonated_~w..slow', [Name]),
      format(atom(Inited), '.Lpizlonated_~w..inited', [Name]),
      foldl(payload_item, Items, Payload, 0-[], Size0-Rs0),
      reverse(Rs0, Rs),
      Size is (Size0 + 7) // 8 * 8,
      Pad is Size - Size0,
      relocs_aux_word(Rs, Flags, DA, AuxWord),
      Total is 16 + Size,
      PayloadAlign is max(Align, 16), Front is PayloadAlign - 16,
      Log is msb(PayloadAlign),
      % clang's section: a const object or string literal without
      % pointers is read-only (.data.rel.ro), where glibc's fortified
      % printf accepts a %n format; one with pointers stays in .data, as
      % the getter's relocations write its payload at run time (the
      % readonly flag in its aux word still refuses stores).
      (   memberchk(readonly, Flags), Rs == [] -> Section = data_rel_ro
      ;   Section = data
      ) },
    [section(Section), p2align(Log)],
    (   { Front > 0 }
    ->  [zero(Front)]
    ;   []
    ),
    [type(DO, object), label(DO),
     quad(DO+16+Size), quad(AuxWord)],
    seq(Payload),
    (   { Pad > 0 }
    ->  [zero(Pad)]
    ;   []
    ),
    [size(DO, Total)],
    [section(bss), p2align(4), label(GP), zero(16)],
    aux_array(Rs, DA, Size, Relocs, Name),
    [section(text), p2align(4)],
    linkage_globl(Linkage, Getter),
    [type(Getter, function), label(Getter),
     ins(mov, q, [rip(GP), reg(rax)]),
     ins(mov, q, [rip(GP+8), reg(rdx)]),
     ins(test, q, [reg(rax), reg(rax)]),
     ins(jz, none, [sym(Slow)]),
     ins(test, q, [reg(rdx), reg(rdx)]),
     ins(jz, none, [sym(Slow)]),
     ins(ret, none, []),
     label(Slow),
     ins(push, q, [reg(rbx)]),
     ins(mov, q, [reg(rdi), reg(rbx)]),
     ins(lea, q, [rip(GP), reg(rdx)]),
     ins(lea, q, [rip(DO), reg(rcx)]),
     ins(call, none, [plt(filc_global_initialization_start)]),
     ins(test, b, [imm(1), reg(al)]),
     ins(jz, none, [sym(Inited)])],
    relocations_call(Rs, DO, Relocs),
    [ins(mov, q, [reg(rbx), reg(rdi)]),
     ins(call, none, [plt(filc_global_initialization_end)]),
     label(Inited),
     ins(pop, q, [reg(rbx)]),
     ins(lea, q, [rip(DO+16), reg(rax)]),
     ins(mov, q, [reg(rax), reg(rdx)]),
     ins(ret, none, [])].

%% Thread-local data, as clang lays it out (docs/abi-findings.md,
%% *Thread-local variables*): a .tbss word TP_d holding this thread's
%% payload address, null until the thread first asks, and a getter that
%% returns it or calls the slow path GS_d. GS_d allocates the thread's
%% object with filc_allocate_thread_local (which roots it in the thread),
%% copies the initializer's bytes from a template TI_d and runs its
%% relocations, as a global's slow path does, then sets TP_d.

thread_local_object(Name, Linkage, Align, Items) -->
    { abi_symbol(getter, Name, Getter),
      format(atom(TP), 'pizlonatedTP_~w', [Name]),
      format(atom(Slow), '.LpizlonatedGS_~w', [Name]),
      format(atom(Template), '.LpizlonatedTI_~w', [Name]),
      format(atom(Relocs), '.Lpizlonated_~w..relocs', [Name]),
      format(atom(Ensure), '.Lpizlonated_~w..ensure', [Name]),
      foldl(payload_item, Items, Payload, 0-[], Size-Rs0),
      reverse(Rs0, Rs),
      (   Rs == [] -> Allocate = filc_allocate_thread_local
      ;   Allocate = filc_allocate_thread_local_with_ptrs
      ) },
    [section(tbss), p2align(3)],
    linkage_globl(Linkage, TP),
    [type(TP, object), label(TP), zero(8), size(TP, 8)],
    (   { template_needed(Items) }
    ->  [section(rodata), p2align(4), label(Template)], seq(Payload),
        { Copy = [ins(lea, q, [mem(16, r12), reg(rdi)]),
                  ins(lea, q, [rip(Template), reg(rsi)]),
                  ins(mov, q, [imm(Size), reg(rcx)]),
                  ins('rep movsb', none, [])] }
    ;   { Copy = [] }
    ),
    (   { Rs == [] }
    ->  { RelocsCall = [] }
    ;   [section(data_rel_ro), p2align(4), label(Relocs)],
        relocations(Rs, Name),
        { length(Rs, NRelocs),
          RelocsCall = [ins(mov, q, [reg(rbx), reg(rdi)]),
                        ins(mov, q, [reg(r12), reg(rsi)]),
                        ins(lea, q, [rip(Relocs), reg(rdx)]),
                        ins(mov, l, [imm(NRelocs), reg(ecx)]),
                        ins(call, none, [plt(filc_execute_constant_relocations)])] }
    ),
    [section(text), p2align(4)],
    linkage_globl(Linkage, Getter),
    [type(Getter, function), label(Getter),
     ins(mov, q, [gottpoff(TP), reg(rax)]),
     ins(mov, q, [fs(mem(0, rax)), reg(rax)]),
     ins(test, q, [reg(rax), reg(rax)]),
     ins(jz, none, [sym(Ensure)]),
     ins(mov, q, [reg(rax), reg(rdx)]),
     ins(ret, none, []),
     label(Ensure),
     ins(sub, q, [imm(8), reg(rsp)]),
     ins(call, none, [sym(Slow)]),
     ins(add, q, [imm(8), reg(rsp)]),
     ins(mov, q, [reg(rax), reg(rdx)]),
     ins(ret, none, []),
     p2align(4), type(Slow, function), label(Slow),
     ins(push, q, [reg(rbx)]),
     ins(push, q, [reg(r12)]),
     ins(sub, q, [imm(8), reg(rsp)]),
     ins(mov, q, [reg(rdi), reg(rbx)]),
     ins(mov, q, [imm(Size), reg(rsi)]),
     ins(mov, q, [imm(Align), reg(rdx)]),
     ins(call, none, [plt(Allocate)]),
     ins(mov, q, [reg(rax), reg(r12)])],
    seq(Copy),
    seq(RelocsCall),
    [ins(lea, q, [mem(16, r12), reg(rax)]),
     ins(mov, q, [gottpoff(TP), reg(rcx)]),
     ins(mov, q, [reg(rax), fs(mem(0, rcx))]),
     ins(add, q, [imm(8), reg(rsp)]),
     ins(pop, q, [reg(r12)]),
     ins(pop, q, [reg(rbx)]),
     ins(ret, none, [])].

% template_needed(+Items): some byte of data Items is not zero, so the
% fresh (zeroed) object needs a copy of them.
template_needed(Items) :-
    member(Item, Items),
    (   Item = item(_, const(N)), N =\= 0
    ;   Item = item(b, str(Cs)), member(C, Cs), char_code(C, Code), Code =\= 0
    ),
    !.

% relocs_aux_word(+Rs, +Flags, +DA, -AuxWord): AuxWord is the aux word
% of a global data object with relocations Rs and other flags Flags: its
% flags, and its static aux array DA if it holds pointers.
relocs_aux_word([], Flags, _, Bits) :-
    aux_bits([global|Flags], Bits).
relocs_aux_word([_|_], Flags, DA, DA+Bits) :-
    aux_bits([global, global_aux|Flags], Bits).

% The aux array DA of Size bytes and the relocation table Relocs, if
% there are relocations Rs.
aux_array([], _, _, _, _) --> [].
aux_array([R|Rs], DA, Size, Relocs, Name) -->
    [p2align(4), label(DA), zero(Size)],
    [section(data_rel_ro), p2align(4), label(Relocs)],
    relocations([R|Rs], Name).

% The getter's call that runs the relocations Rs, if there are any, of
% data object DO from the table Relocs.
relocations_call([], _, _) --> [].
relocations_call([R|Rs], DO, Relocs) -->
    { length([R|Rs], NRelocs) },
    [ins(mov, q, [reg(rbx), reg(rdi)]),
     ins(lea, q, [rip(DO), reg(rsi)]),
     ins(lea, q, [rip(Relocs), reg(rdx)]),
     ins(mov, l, [imm(NRelocs), reg(ecx)]),
     ins(call, none, [plt(filc_execute_constant_relocations)])].

% linkage_flags(+Linkage0, -Linkage, -Flags): a data object of linkage
% Linkage0 has linkage Linkage and, if read-only, the flag readonly.
linkage_flags(ro(Linkage), Linkage, [readonly]).
linkage_flags(export, export, []).
linkage_flags(local, local, []).
linkage_flags(weak, weak, []).

% payload_item(+Item, -Line, +Off0-Rs0, -Off-Rs): Line is the payload
% directive of Item at offset Off0, and Rs adds to Rs0 a relocation
% r(Offset, Symbol, Addend) if Item is a pointer, whose slot stays 0
% until the relocation fills it in. Off is the offset after Item.
payload_item(zero(N), zero(N), Off0-Rs, Off-Rs) :-
    Off is Off0 + N.
payload_item(item(W, Value), Line, S0, S) :-
    value_payload(Value, W, Line, S0, S).

% value_payload(+Value, +W, -Line, +Off0-Rs0, -Off-Rs): as payload_item/4
% for item(W, Value).
value_payload(str(Cs), b, ascii(Cs), Off0-Rs, Off-Rs) :-
    length(Cs, N),
    Off is Off0 + N.
value_payload(sym(S, Addend), p, quad(0), Off0-Rs,
              Off-[r(Off0, S, Addend)|Rs]) :-
    (   Off0 mod 8 =:= 0
    ->  true
    ;   throw(nanofil_error('pointer data item is not 8-aligned'))
    ),
    Off is Off0 + 8.
value_payload(const(N), x, byte(Bs), Off0-Rs, Off-Rs) :- !,
    numlist(0, 9, Is),
    findall(B, ( member(I, Is), B is (N >> (8 * I)) /\ 255 ), Bs),
    Off is Off0 + 10.
value_payload(const(N), W, Directive, Off0-Rs, Off-Rs) :-
    width_bytes(W, Bytes),
    Bits is 8 * Bytes,
    U is N mod (1 << Bits),
    memberchk(Bytes-Directive,
              [1-byte([U]), 2-short(U), 4-long(U), 8-quad(U)]),
    Off is Off0 + Bytes.

% Each relocation is {u64 offset, u32 kind, pad, target}: kind 0 calls a
% getter, kind 1 a constexpr node {u32 add-immediate = 0, u32 0, getter,
% u64 addend}.
relocations(Rs, Name) -->
    reloc_entries(Rs, 0, Name),
    reloc_nodes(Rs, 0, Name).

% The relocation table. Invariant: Rs are the relocations from the Ith.
reloc_entries([], _, _) --> [].
reloc_entries([r(Off, S, Addend)|Rs], I, Name) -->
    { abi_symbol(getter, S, Getter) },
    (   { Addend =:= 0 }
    ->  [quad(Off), long(0), zero(4), quad(Getter)]
    ;   { reloc_node(Name, I, Node) },
        [quad(Off), long(1), zero(4), quad(Node)]
    ),
    { I1 is I + 1 },
    reloc_entries(Rs, I1, Name).

% The constexpr node of each relocation with an addend. Invariant: Rs
% are the relocations from the Ith.
reloc_nodes([], _, _) --> [].
reloc_nodes([r(_, S, Addend)|Rs], I, Name) -->
    (   { Addend =:= 0 }
    ->  []
    ;   { abi_symbol(getter, S, Getter),
          reloc_node(Name, I, Node),
          U is Addend mod 18446744073709551616 },
        [label(Node), long(0), long(0), quad(Getter), quad(U)]
    ),
    { I1 is I + 1 },
    reloc_nodes(Rs, I1, Name).

% reloc_node(+Name, +I, -Node): Node labels the constexpr node of
% relocation I of data object Name.
reloc_node(Name, I, Node) :-
    format(atom(Node), '.Lpizlonated_~w..node~w', [Name, I]).

% thunk_generic_return(+Form, +RetKs, +Need, +GWs, +Out, +RetOk,
% +GenericExc)//: the return, in form Form, of the generic entry's
% result words GWs, of classes RetKs and Need bytes, then a jump to Out.
thunk_generic_return(reg, RetKs, Need, GWs, Out, RetOk, _) -->
    [ins(jnz, none, [sym(Out)])],
    thunk_generic_reg_words(RetKs, Need, GWs, RetOk),
    [ins(xor, l, [reg(eax), reg(eax)]),
     ins(jmp, none, [sym(Out)])].
thunk_generic_return(mem(_), _, Need, Srcs, Out, RetOk, GenericExc) -->
    [ins(jnz, none, [sym(GenericExc)])],
    rets_check(Need, RetOk),
    thunk_buffer_copies(Srcs, 8),
    [ins(mov, b, [imm(0), mem(0, r12)]),
     ins(mov, q, [reg(r12), reg(rax)]),
     ins(jmp, none, [sym(Out)]),
     label(GenericExc),
     ins(mov, b, [imm(1), mem(0, r12)]),
     ins(mov, q, [reg(r12), reg(rax)]),
     ins(jmp, none, [sym(Out)])].

% The result words, if RetKs has any, in %rdx:%rcx.
thunk_generic_reg_words(void, _, _, _) --> [].
thunk_generic_reg_words(float(K),Need,[Off],RetOk) -->
    { att_suffix(K,S),reg_name(d,K,R) },
    rets_check(Need,RetOk),
    [ins(mov,S,[mem(Off,rbx),reg(R)])],to_xmm(K,d,xmm0).
thunk_generic_reg_words(typed(Ks), Need, Srcs, RetOk) -->
    { foldl(typed_ret_kind, Ks, KTs, []), result_registers(KTs, Rs) },
    rets_check(Need, RetOk),
    thunk_typed_loads(Rs, Srcs).
thunk_generic_reg_words(words, Need, Srcs, RetOk) -->
    rets_check(Need, RetOk),
    thunk_reg_loads(Srcs, [rdx, rcx]).

thunk_typed_loads([], []) --> [].
thunk_typed_loads([R|Rs], [Off|Offs]) -->
    (   { R = gpr(G) } -> [ins(mov, q, [mem(Off, rbx), reg(G)])]
    ;   { R = xmm(K, X) },
        [ins(mov, q, [mem(Off, rbx), reg(rax)])], to_xmm(K, a, X)
    ),
    thunk_typed_loads(Rs, Offs).

% The load of each generic return word, at thread offset Off, into its
% register.
thunk_reg_loads([], _) --> [].
thunk_reg_loads([Off|Offs], [Reg|Regs]) -->
    [ins(mov, q, [mem(Off, rbx), reg(Reg)])],
    thunk_reg_loads(Offs, Regs).

% The copy of each generic return word, at thread offset Src, into the return
% buffer at Off(%r12).
thunk_buffer_copies([], _) --> [].
thunk_buffer_copies([Src|Srcs], Off) -->
    [ins(mov, q, [mem(Src, rbx), reg(rax)]),
     ins(mov, q, [reg(rax), mem(Off, r12)])],
    { Off1 is Off + 8 },
    thunk_buffer_copies(Srcs, Off1).

% The operand Word into the thread at offset Off, through %rax if it is
% in memory.
operand_thread_store(reg(R), Off) -->
    [ins(mov, q, [reg(R), mem(Off, rbx)])].
operand_thread_store(mem(D, B), Off) -->
    [ins(mov, q, [mem(D, B), reg(rax)]),
     ins(mov, q, [reg(rax), mem(Off, rbx)])].

/* The generic entry: {i1, i64 ret_size} (thread, callee_lower, args_size).
   Argument i is 8 bytes at thread+128+8i, with its lower (for p) at
   thread+384+8i, and so is result word i. It calls the fast entry
   through callee_lower, with a buffer on the stack for a buffered
   return. */
generic_entry(Generic, adapt(Need,Words,Result)) -->
    { Result = adapter_result(Return,Channel,RetSize,Packet),
      target_form(Return,Form), packet_offsets(Packet,PlacedPacket),
      maplist(adapter_word(thread),Words,Ts),typed_locations(Ts,Form,Ls,NS,_),
      stack_bytes(NS, Pop),
      atom_concat(Generic,'.short',Short),atom_concat(Generic,'.done',Done) },
    [section(text),label(Generic),ins(push,q,[reg(rbx)]),
     ins(cmp,q,[imm(Need),reg(rdx)]),ins(jb,none,[sym(Short)]),
     ins(mov,q,[reg(rdi),reg(rbx)])],
    ret_buffer_reservation(Form), reserve_stack(Pop),
    adapter_stack(Ts,Ls,Generic),adapter_registers(Ts,Ls,Generic),
    generic_entry_call(Form,Channel,PlacedPacket,Pop,RetSize,Done),
    [ins(pop,q,[reg(rbx)]),ins(ret,none,[]),label(Short),
     ins(mov,q,[reg(rdx),reg(rdi)]),ins(mov,l,[imm(Need),reg(esi)]),
     ins(xor,l,[reg(edx),reg(edx)]),
     ins(call,none,[plt(filc_cc_args_check_failure)]),ins(ud2,none,[])].
/* generic_entry_call(+Form, +Channel, +Packet, +Pop, +RetSize, +Done)//:
   call the fast entry in placed Form, then transport Channel into the
   placed Packet and return RetSize in %edx. Pop is the native stack
   argument size. Exceptions skip all result reads and size production. */
generic_entry_call(reg, Channel, Packet, Pop, RetSize, Done) -->
    { field(function_object, fast_entry, rsi, Fast) },
    [ins(call, q, [ind(Fast)])],
    stack_release(Pop),
    [ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Done)])],
    generic_reg_results(Channel, Packet),
    [ins(mov, l, [imm(RetSize), reg(edx)]),
     label(Done)].
generic_entry_call(mem(Bytes), _, packet(Dests,Zeros), Pop, RetSize, Done) -->
    { field(function_object, fast_entry, rdx, Fast) },
    [ins(mov, q, [reg(rsi), reg(rdx)]),
     ins(mov, q, [reg(rbx), reg(rsi)]),
     ins(lea, q, [mem(Pop, rsp), reg(rdi)]),
     ins(call, q, [ind(Fast)])],
    stack_release(Pop),
    [ins(mov, b, [mem(0, rsp), reg(al)]),
     ins(test, b, [reg(al), reg(al)]),
     ins(jnz, none, [sym(Done)])],
    generic_buffer_copies(Dests, 8),
    generic_zeroings(Zeros),
    [ins(mov, l, [imm(RetSize), reg(edx)]),
     ins(xor, l, [reg(eax), reg(eax)]),
     label(Done)],
    ret_buffer_release(mem(Bytes)).

% The result words from %rdx:%rcx at their thread offsets; a void result
% is one zero word.
generic_reg_results(void, packet([],Zeros)) --> generic_zeroings(Zeros).
generic_reg_results(float(K), packet([Off],[Lower])) -->
    from_xmm(K,xmm0,d),
    [ins(mov,q,[reg(rdx),mem(Off,rbx)]),
     ins(mov,q,[imm(0),mem(Lower,rbx)])].
generic_reg_results(typed(Ks), packet(Dests,Zeros)) -->
    { foldl(typed_ret_kind, Ks, KTs, []), result_registers(KTs, Rs) },
    generic_typed_gprs(Rs, Dests), generic_typed_xmms(Rs, Dests),
    [ins(xor, l, [reg(eax), reg(eax)])],
    generic_zeroings(Zeros).
generic_reg_results(words, packet(Dests,Zeros)) -->
    generic_reg_stores(Dests, [rdx, rcx]),
    generic_zeroings(Zeros).

typed_ret_kind(p, [l-x,l-x|W], W) :- !.
typed_ret_kind(K, [K-x|W], W).
generic_typed_gprs([], []) --> [].
generic_typed_gprs([R|Rs], [Off|Offs]) -->
    ( { R = gpr(G) } -> [ins(mov, q, [reg(G), mem(Off, rbx)])] ; [] ),
    generic_typed_gprs(Rs, Offs).
generic_typed_xmms([], []) --> [].
generic_typed_xmms([R|Rs], [Off|Offs]) -->
    (   { R = xmm(K, X) }
    ->  from_xmm(K, X, a), [ins(mov, q, [reg(rax), mem(Off, rbx)])]
    ;   []
    ),
    generic_typed_xmms(Rs, Offs).

% The store of each result register at its thread offset.
generic_reg_stores([], _) --> [].
generic_reg_stores([Off|Offs], [Reg|Regs]) -->
    [ins(mov, q, [reg(Reg), mem(Off, rbx)])],
    generic_reg_stores(Offs, Regs).

% The copy of each return buffer word, from Off(%rsp) on, to thread
% offset Dest.
generic_buffer_copies([], _) --> [].
generic_buffer_copies([Dest|Dests], Off) -->
    [ins(mov, q, [mem(Off, rsp), reg(rax)]),
     ins(mov, q, [reg(rax), mem(Dest, rbx)])],
    { Off1 is Off + 8 },
    generic_buffer_copies(Dests, Off1).

% Explicit zero channels from the ABI product.
generic_zeroings([]) --> [].
generic_zeroings([Off|Offs]) -->
    [ins(mov, q, [imm(0), mem(Off, rbx)])], generic_zeroings(Offs).

%% Static data: function origins (staging's 48-byte layout), origins,
%% and one access-check origin per check kind.

% The name string, the c and n function origins with their origins, and
% the check origins of function Name.
origins(Name, Origins, CheckKinds) -->
    { format(atom(NameLabel), '.L~w..name', [Name]) },
    [section(rodata), label(NameLabel), asciz(Name),
     section(data_rel_ro), p2align(4)],
    function_origins(Origins, Name, NameLabel),
    check_origins(CheckKinds, Name).

function_origins([], _, _) --> [].
function_origins([origin(Which,Catch,NLowers,NumSetjmps,NumLocals)|Origins], Name, NameLabel) -->
    { catch_flag(Catch, CanCatch) },
    function_origin(Name, NameLabel, NLowers, Which, CanCatch, NumSetjmps, NumLocals),
    function_origins(Origins, Name, NameLabel).
catch_flag(catches, 1).
catch_flag(no_catch, 0).

% A function origin and the origin (origin_label/3) that points at it.
function_origin(Name, NameLabel, NLowers, Which, CanCatch, NumSetjmps, NumLocals) -->
    { format(atom(FOrigin), '.L~w..forigin_~w', [Name, Which]),
      origin_label(Name, Which, Origin) },
    [label(FOrigin),
     quad(NameLabel), quad(0),
     long(NLowers), zero(4),
     quad(0),
     byte([0, CanCatch]), zero(2),
     long(NumSetjmps), long(NumLocals), zero(4),
     label(Origin),
     quad(FOrigin), long(0), long(0)].

% An access-check origin for each check kind.
check_origins([], _) --> [].
check_origins([Kind|Kinds], Name) -->
    { Kind = k(Size, Write, Align),
      check_origin_label(Name, Kind, Label),
      origin_label(Name, n, Origin) },
    [p2align(4), label(Label),
     long(Size), byte([Align, 0, Write]), zero(1),
     quad(Origin), quad(Origin), quad(0)],
    check_origins(Kinds, Name).
