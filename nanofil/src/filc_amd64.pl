/*  Naive Fil-C lowering for x86-64 (milestone 3).

    Emits asm.pl lines whose GNU as text links with clang-built Fil-C
    code with filnix staging (Fil-C 0.687). The rules are in docs/m3.md;
    in short:

    - Temporaries with disjoint closed live intervals share slots. A p
      temporary's slot holds its address, and its lower lives in a
      lowers[] entry of a filc_frame pushed on thread->top_frame, for the
      whole function. Values are never kept in registers across a call or
      safepoint, so every live capability is always in a scanned slot.
    - Every access gets the full check sequence; pointer loads and stores
      go through the aux array, with ensure-aux and the store barrier.
    - alloc is a heap allocation. Back edges in block order pollcheck.
    - Calls use the fast convention (thread, callee lower, words...) and
      propagate has_exception by popping the frame and returning AL = 1.
    - Exported functions get an alias, a getter, a function object and a
      generic entry, so clang code can call them directly or indirectly.

    Scalar integer and SSE2 instructions share amd64:compute_op//4.
    Float bits have no lower; ABI boundaries carry them in XMM registers
    or generic payload words with zero aux (docs/abi-findings.md).

    Variable conventions: Ctx is the function context (function_ctx/7)
    and Fn the amd64 context inside it; K is a word class (w, l, p, s, d);
    V is a value, t(N) or c(N); D is the number of a destination t(D);
    T is a load type and W a store width; S and F are symbols; Off is a
    byte offset; Form is a return form, reg or mem(Bytes) (ret_form/2).
*/
:- module(filc_amd64, [filc_module_asm/2, signature/3]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(ir).
:- use_module(amd64).
:- use_module(frame_slots).

%! filc_module_asm(+Module, -Lines) is det.
%
%  Lines is the asm.pl line list of IR module Module for the Fil-C ABI:
%  each item's code and data, a weak thunk for each function the module
%  calls but does not define, and the GNU-stack note. Throws
%  nanofil_error(Msg) if an item cannot be lowered.
filc_module_asm(Module, Lines) :-
    Module = module(Items),
    maplist(item_lines(Module), Items, LinesPerItem),
    append(LinesPerItem, ItemLines),
    external_callees(Module, Callees),
    maplist(thunk_lines, Callees, LinesPerThunk),
    append(LinesPerThunk, ThunkLines),
    append([ItemLines, ThunkLines, [section(note_gnu_stack)]], Lines).

thunk_lines(Callee, Lines) :-
    phrase(thunk(Callee), Lines).

% item_lines(+Module, +Item, -Lines): Lines is the code or data of Item;
% throws if there is none.
item_lines(Module, Item, Lines) :-
    (   phrase(item(Module, Item), Lines) -> true
    ;   arg(1, Item, Name),
        format(atom(Msg), 'Fil-C backend cannot emit $~w', [Name]),
        throw(nanofil_error(Msg))
    ).

%% Signatures (docs/abi-findings.md): each word class is a bijective
%% base-11 digit, i64 = 0, float = 1, double = 2 and ptr = 7;
%% sig = 1 + ret + 133 * args.

%! signature(+Ret, +ParamKs, -Sig) is det.
%
%  Sig is the Fil-C signature number of a function returning Ret (void,
%  a class or tuple(Ks)) and taking parameters of classes ParamKs. Fails
%  on a class other than w, l, p, s or d; throws nanofil_error/1 for more than
%  16 parameters.
signature(Ret, ParamKs, Sig) :-
    ret_kinds(Ret, RetKs),
    maplist(class_digit, RetKs, RetDigits),
    maplist(class_digit, ParamKs, ArgDigits),
    length(ArgDigits, NArgs),
    (   NArgs =< 16
    ->  true
    ;   throw(nanofil_error('more than 16 arguments'))
    ),
    bijective_value(RetDigits, R),
    bijective_value(ArgDigits, A),
    Sig is 1 + R + 133 * A.

class_digit(w, 0).
class_digit(l, 0).
class_digit(p, 7).
class_digit(s, 1).
class_digit(d, 2).

% bijective_value(+Digits, -Value): Value is the number whose bijective
% base-11 digits, least significant first, are Digits.
bijective_value([], 0).
bijective_value([D|Ds], V) :-
    bijective_value(Ds, V1),
    V is D + 1 + 11 * V1.

func_signature(func(_, _, Ret, Params, _), Sig) :-
    findall(K, member(par(K, _), Params), Ks),
    signature(Ret, Ks, Sig).

%% ABI facts (docs/abi-findings.md), at the pin

% abi_symbol(+Role, +F, -Symbol): Symbol is the name under which code
% finds Role of the function or global F: its implementation (the fast
% entry) and FI alias for signature Sig, its getter, its function object,
% or its data object and aux array.
abi_symbol(impl(Sig), F, S) :- format(atom(S), 'pizlonatedFIP~w_~w', [Sig, F]).
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

/* layout(+Form, +Params, +Blocks, -Slots, -FrameBase, -NLowers, -Size):
   the frame of a function with return form Form. Slots maps t(N) and
   shadow(N) to address slots and lower(Key) to lowers[] entries, all as
   offsets below %rbp; thread and aux are scratch slots, and retbuf holds
   the return buffer of a buffered return. The filc_frame {parent,
   origin, lowers[NLowers]} sits at -FrameBase(%rbp), and Size is the
   16-aligned frame size. */
layout(Form, Params, Blocks, Slots, FrameBase, NLowers, Size) :-
    findall(N-K,
            (   member(par(K, t(N)), Params)
            ;   member(blk(_, Phis, Insts, _), Blocks),
                (   member(phi(t(N), K, _), Phis)
                ;   member(I, Insts),
                    inst_dest_class(I, N, K)
                )
            ),
            Temps0),
    sort(Temps0, Temps),
    findall(N-K,
            (   member(blk(_, Phis, _, _), Blocks),
                member(phi(t(N), K, _), Phis)
            ),
            Shadows0),
    sort(Shadows0, Shadows),
    findall(shadow(N), member(N-_, Shadows), ShadowKeys),
    form_extra_slots(Form, Extra),
    setjmp_slots(Blocks, JPlain, JLowers),
    temp_storage(JLowers, Params, Blocks, Temps, TempKeys, TempLowers, Aliases),
    append([TempKeys, ShadowKeys, [thread, aux], Extra, JPlain], Plain),
    findall(lower(shadow(N)), member(N-p, Shadows), ShadowLowers),
    append([TempLowers, ShadowLowers, JLowers], Lowers),
    length(Plain, NPlain),
    length(Lowers, NLowers),
    FrameBase is 8 * NPlain + 16 + 8 * NLowers,
    empty_assoc(Slots0),
    foldl(plain_slot, Plain, Slots0-0, Slots1-_),
    foldl(lower_slot(FrameBase), Lowers, Slots1-0, Slots2-_),
    foldl(temp_alias, Aliases, Slots2, Slots),
    Size is (FrameBase + 15) // 16 * 16.

% Returns-twice snapshots cover every logical payload slot, not merely
% live values. Keep their original unique layout, even for dead sites.
temp_storage([], Params, Blocks, Temps, Keys, Lowers, Aliases) :-
    temp_slots(Params, Blocks, Temps, Map, NS, NP),
    storage_keys(scalar, 0, NS, Scalars),
    storage_keys(pointer, 0, NP, Pointers),
    append(Scalars, Pointers, Keys),
    maplist(storage_lower, Pointers, Lowers),
    assoc_to_list(Map, Pairs),
    maplist(storage_alias, Pairs, Aliases).
temp_storage([_|_], _, _, Temps, Keys, Lowers, []) :-
    findall(t(N), member(N-_, Temps), Keys),
    findall(lower(t(N)), member(N-p, Temps), Lowers).

storage_keys(Pool, I, N, Keys) :-
    ( I < N
    -> Keys = [storage(Pool, I)|Rest], Next is I + 1,
       storage_keys(Pool, Next, N, Rest)
    ;  Keys = [] ).

storage_lower(Key, lower(Key)).
storage_alias(N-Key, t(N)-Key).

temp_alias(T-Key, Slots0, Slots) :-
    get_assoc(Key, Slots0, Off), put_assoc(T, Slots0, Off, Slots1),
    ( Key = storage(pointer, _)
    -> get_assoc(lower(Key), Slots1, Lower),
       put_assoc(lower(T), Slots1, Lower, Slots)
    ;  Slots = Slots1 ).

% Persistent jmpbuf roots must be the highest-indexed lowers. Ordinary
% snapshot roots are initialized eagerly and never change thereafter.
setjmp_slots(Blocks, Plain, Lowers) :-
    setjmp_sites(Blocks, Sites),
    findall(t(hidden(setjmp_buf(D))), member(D, Sites), Plain),
    findall(lower(setjmp_snapshot(D)), member(D, Sites), Snapshots),
    findall(lower(t(hidden(setjmp_buf(D)))), member(D, Sites), JmpBufs),
    append(Snapshots, JmpBufs, Lowers).

setjmp_sites(Blocks, Sites) :-
    findall(D, (member(blk(_, _, Insts, _), Blocks),
                member(ins(t(D), w, setjmp(_), _), Insts)), Sites).

% inst_dest_class(+Inst, -N, -K): t(N), of class K, is a destination of
% instruction Inst.
inst_dest_class(ins(t(N), K, _, _), N, K).
inst_dest_class(call(to(t(N), K), _, _), N, K).
inst_dest_class(call(tuple(Tos), _, _), N, K) :-
    member(to(t(N), K), Tos).

% A buffered return keeps its buffer's address in a slot.
form_extra_slots(reg, []).
form_extra_slots(mem(_), [retbuf]).

% plain_slot(+Key, +Slots0-I0, -Slots-I): Slots maps Key to the slot
% after the I0 already allocated, the Ith from %rbp.
plain_slot(Key, Slots0-I0, Slots-I) :-
    I is I0 + 1,
    Off is 8 * I,
    put_assoc(Key, Slots0, Off, Slots).

% lower_slot(+FrameBase, +Key, +Slots0-I0, -Slots-I): Slots maps Key to
% lowers[I0] of the filc_frame at -FrameBase(%rbp).
lower_slot(FrameBase, Key, Slots0-I0, Slots-I) :-
    Off is FrameBase - 16 - 8 * I0,
    I is I0 + 1,
    put_assoc(Key, Slots0, Off, Slots).

%% The function context

/* function_ctx(+Name, +Ret, +Slots, +Blocks, +Module, +FrameBase, -Ctx):
   Ctx = ctx(Fn, Module, FrameBase, Labels) is the context of function
   Name, where Fn = f(Name, Ret, Slots, Blocks) is the context amd64's
   load//4 and compute_op//4 take. Labels maps each block label to
   block(Index, Phis), so an edge finds its target's position and phis
   without searching Blocks. */
function_ctx(Name, Ret, Slots, Blocks, Module, FrameBase, Ctx) :-
    findall(Label-block(Index, Phis),
            nth0(Index, Blocks, blk(Label, Phis, _, _)),
            LabelBlocks),
    list_to_assoc(LabelBlocks, Labels),
    Ctx = ctx(f(Name, Ret, Slots, Blocks), Module, FrameBase, Labels).

ctx_fn(ctx(Fn, _, _, _), Fn).

ctx_name(ctx(f(Name, _, _, _), _, _, _), Name).

ctx_ret(ctx(f(_, Ret, _, _), _, _, _), Ret).

ctx_module(ctx(_, Module, _, _), Module).

ctx_frame_base(ctx(_, _, FrameBase, _), FrameBase).

ctx_labels(ctx(_, _, _, Labels), Labels).

% ctx_slot(+Ctx, +Key, -Off): Key's slot is at -Off(%rbp).
ctx_slot(ctx(f(_, _, Slots, _), _, _, _), Key, Off) :-
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
    format(atom(A), '.L~w..~w', [Name, Tag]).

% The label of the block named Label.
block_label(Ctx, Label, A) :-
    ctx_name(Ctx, Name),
    format(atom(A), '.L~w.~w', [Name, Label]).

% A label inside the code of instruction Index (or a jump) in Block.
local_label(Ctx, Block, Index, Tag, A) :-
    ctx_name(Ctx, Name),
    format(atom(A), '.L~w.~w..~w.~w', [Name, Block, Index, Tag]).

% The frame's origin: c (calls, can_catch) or n (pollchecks and checks).
origin_label(Name, Which, A) :-
    format(atom(A), '.L~w..origin_~w', [Name, Which]).

%% Functions

% The lines of a module item, a function or a data object.
item(Module, Func) -->
    { Func = func(_, _, _, _, _) },
    function(Module, Func).
item(_, data(Name, Linkage, _, Items)) -->
    data_object(Name, Linkage, Items).

% A function: its implementation (prologue, blocks, the shared exception
% exit and failure blocks), then its function object and origins.
function(Module, Func) -->
    { Func = func(Name, Linkage, Ret, Params, Blocks),
      implementation_params(Func, Params, BodyParams),
      func_signature(Func, Sig),
      ret_kinds(Ret, RetKs),
      ret_form(RetKs, Form),
      layout(Form, BodyParams, Blocks, Slots, FrameBase, NLowers, Size),
      function_ctx(Name, Ret, Slots, Blocks, Module, FrameBase, Ctx),
      abi_symbol(impl(Sig), Name, Impl),
      access_check_kinds(Blocks, CheckKinds),
      special_label(Ctx, exc, Exc) },
    [section(text), p2align(4)],
    linkage_globl(Linkage, Impl),
    [type(Impl, function), label(Impl)],
    prologue(Form, Size, NLowers, Ctx),
    body_param_stores(BodyParams, Form, Ctx),
    setjmp_entry(Ctx),
    blocks(Blocks, Ctx),
    [label(Exc)],
    exception_exit(Form, Ctx),
    check_fail_blocks(CheckKinds, Ctx),
    not_function_block(Blocks, Ctx),
    [size(Impl)],
    body_function_object(Func, Name, Linkage, Ret, Params, Sig, Impl),
    { setjmp_sites(Blocks, Sites), length(Sites, NumSetjmps) },
    origins(Name, NLowers, CheckKinds, NumSetjmps).

% Root parameters before allocating. All snapshot roots must be stable
% before any site captures lowers, including sites not yet executed.
setjmp_entry(Ctx) -->
    { ctx_fn(Ctx, f(_, _, Slots, _)), assoc_to_keys(Slots, All),
      findall(D, member(lower(setjmp_snapshot(D)), All), Sites),
      setjmp_payload_slots(Ctx, Keys), length(Keys, N), Bytes is 8 * N },
    setjmp_snapshots(Sites, Bytes, Ctx).

setjmp_snapshots([], _, _) --> [].
setjmp_snapshots([D|Ds], Bytes, Ctx) -->
    origin_store(Ctx, c),
    slot_reg_load(thread, rdi, Ctx),
    [ins(mov, q, [imm(Bytes), reg(rsi)]),
     ins(call, none, [plt(filc_allocate)]),
     ins(lea, q, [mem(16, rax), reg(rdx)])],
    reg_slot_store(rdx, lower(setjmp_snapshot(D)), Ctx),
    setjmp_snapshots(Ds, Bytes, Ctx).

% A private fast body keeps the existing return convention. Its final
% parameter roots the eager snapshot before the first body safepoint.
implementation_params(Func, Params, BodyParams) :-
    ( variadic_func(Func)
    -> append(Params, [par(p, t(hidden(va_snapshot)))], BodyParams)
    ; BodyParams = Params ).

body_function_object(Func, Name, Linkage, Ret, Params, Sig, Impl) -->
    ( { variadic_func(Func) }
    -> variadic_object(Name, Linkage, Ret, Params, Impl)
    ; function_object(Name, Linkage, Ret, Params, Sig, Impl) ).

% The prologue: the frame's allocation, the stack overflow check, the
% thread (and return buffer) in their slots, zeroed lowers[] and the
% filc_frame pushed on thread->top_frame.
prologue(Form, Size, NLowers, Ctx) -->
    { ctx_frame_base(Ctx, FrameBase),
      NegFrameBase is -FrameBase,
      field(thread, stack_limit, rdi, Limit),
      field(thread, top_frame, rdi, Top) },
    [ins(push, q, [reg(rbp)]),
     ins(mov, q, [reg(rsp), reg(rbp)]),
     ins(sub, q, [imm(Size), reg(rsp)])],
    entry_regs_shift(Form),
    [ins(cmp, q, [reg(rsp), Limit]),
     ins(jae, none, [plt(filc_stack_overflow_failure)])],
    reg_slot_store(rdi, thread, Ctx),
    retbuf_store(Form, Ctx),
    lowers_zeroing(NLowers, FrameBase),
    [ins(mov, q, [Top, reg(rax)]),
     ins(mov, q, [reg(rax), mem(NegFrameBase, rbp)])],
    origin_store(Ctx, c),
    [ins(lea, q, [mem(NegFrameBase, rbp), reg(rax)]),
     ins(mov, q, [reg(rax), Top])].

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

% The exception exit: the frame popped and has_exception = 1 returned.
exception_exit(Form, Ctx) -->
    frame_pop(Ctx),
    exception_flag(Form, Ctx),
    [ins(leave, none, []), ins(ret, none, [])].

% has_exception = 1, in %al or in the return buffer.
exception_flag(reg, _) -->
    [ins(mov, b, [imm(1), reg(al)])].
exception_flag(mem(_), Ctx) -->
    slot_reg_load(retbuf, rax, Ctx),
    [ins(mov, b, [imm(1), mem(0, rax)])].

% The failure block of function_check//1, if the function calls through
% a pointer.
not_function_block(Blocks, Ctx) -->
    (   { member(blk(_, _, Insts, _), Blocks),
          memberchk(call(_, t(_), _), Insts) }
    ->  { special_label(Ctx, notfn, NotFn) },
        [label(NotFn),
         ins(mov, q, [reg(rax), reg(rdi)]),
         ins(mov, q, [reg(rcx), reg(rsi)]),
         ins(call, none, [plt(filc_check_function_call_fail)]),
         ins(ud2, none, [])]
    ;   []
    ).

%% Words: a p value is two words (address, lower); w and l are one.

% class_key_slots(+K, +T, -Slots0, ?Slots): Slots0 less Slots are the
% slots of a class K word whose address slot is T: T, then lower(T) for
% p.
class_key_slots(p, T, [T, lower(T)|Ss], Ss).
class_key_slots(w, T, [T|Ss], Ss).
class_key_slots(l, T, [T|Ss], Ss).
class_key_slots(s, T, [T|Ss], Ss).
class_key_slots(d, T, [T|Ss], Ss).

% The stores of the incoming words of Ps into their slots, from where
% the convention puts them (typed_locations/5).
body_param_stores(Ps, Form, Ctx) -->
    { typed_params(Ps, Ts),
      typed_locations(Ts, Form, Ls, _, _) },
    typed_incoming(Ts, Ls, Ctx).

%% Results: none, one word or a tuple of two. A p word is two slots,
%% address and lower. Up to two slots come back in %rdx:%rcx; more go in
%% a buffer the caller passes in %rdi, {i8 has_exception, slots at 8..},
%% with the thread in %rsi, the callee lower in %rdx and the argument
%% words from %rcx (docs/abi-findings.md).

% ret_kinds(+Ret, -Ks): Ks are the classes of the words of return type
% Ret.
ret_kinds(void, []).
ret_kinds(tuple(Ks), Ks).
ret_kinds(w, [w]).
ret_kinds(l, [l]).
ret_kinds(p, [p]).
ret_kinds(s, [s]).
ret_kinds(d, [d]).

% result_tos(+Res, -Tos): Tos are the to(T, K) destinations of call
% result Res.
result_tos(void, []).
result_tos(to(T, K), [to(T, K)]).
result_tos(tuple(Tos), Tos).

% result_ret(+Res, -Ret): Ret is the return type of call result Res.
result_ret(void, void).
result_ret(to(_, K), K).
result_ret(tuple(Tos), tuple(Ks)) :-
    findall(K, member(to(_, K), Tos), Ks).

% result_form(Res, Tos, Kinds, Form): a call result's destinations,
% their classes and its return form.
result_form(Res, Tos, Kinds, Form) :-
    result_tos(Res, Tos),
    findall(K, member(to(_, K), Tos), Kinds),
    ret_form(Kinds, Form).

% ret_form(+Kinds, -Form): Form is reg when words of classes Kinds fit
% in two slots, else mem(Bytes) with Bytes the buffer size rounded to 16.
ret_form(Ks, Form) :-
    maplist(class_slot_count, Ks, Ns),
    sum_list(Ns, N),
    (   N > 2
    ->  Bytes is (8 + 8 * N + 15) // 16 * 16,
        Form = mem(Bytes)
    ;   Form = reg
    ).

% class_slot_count(?K, ?N): a word of class K takes N slots.
class_slot_count(p, 2).
class_slot_count(w, 1).
class_slot_count(l, 1).
class_slot_count(s, 1).
class_slot_count(d, 1).

% The registers that carry argument words in each form.
form_regs(reg, [rdx, rcx, r8, r9]).
form_regs(mem(_), [rcx, r8, r9]).

% The same registers by their amd64 short names, for load//4.
form_short_regs(reg, [d, c, r8, r9]).
form_short_regs(mem(_), [c, r8, r9]).

% The slots of a result, in order, as the frame slots they fill.
result_slots(Res, Slots) :-
    result_tos(Res, Tos),
    foldl(to_slots, Tos, Slots, []).

% to_slots(+To, -Slots0, ?Slots): Slots0 less Slots are To's slots.
to_slots(to(T, K), Ss0, Ss) :-
    class_key_slots(K, T, Ss0, Ss).

% Word I of a generic call's arguments or results is at thread offset
% Addr, word I of the inline buffer, with its lower at Lower, word I of
% the inline aux buffer.
generic_offsets(I, Addr, Lower) :-
    struct_field(thread, cc_inline_buffer, Buffer),
    struct_field(thread, cc_inline_aux_buffer, AuxBuffer),
    Addr is Buffer + 8 * I,
    Lower is AuxBuffer + 8 * I.

% gw(Kind, Offset) for each result word: its thread offset in a generic
% return (its lower, for p, is 256 further on).
generic_words(Ks, GWs) :-
    generic_words(Ks, 0, GWs).

% Invariant: Ks are the result words from word I on.
generic_words([], _, []).
generic_words([K|Ks], I, [gw(K, Off)|GWs]) :-
    generic_offsets(I, Off, _),
    I1 is I + 1,
    generic_words(Ks, I1, GWs).

% generic_srcs(+GW, -Offs0, ?Offs): Offs0 less Offs are the thread
% offsets of GW's slots in a generic return, in slot order.
generic_srcs(gw(K, Off), Os0, Os) :-
    class_generic_srcs(K, Off, Os0, Os).

class_generic_srcs(p, Off, [Off, LowerOff|Os], Os) :-
    LowerOff is Off + 256.
class_generic_srcs(w, Off, [Off|Os], Os).
class_generic_srcs(l, Off, [Off|Os], Os).
class_generic_srcs(s, Off, [Off|Os], Os).
class_generic_srcs(d, Off, [Off|Os], Os).

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
blocks([blk(Label, _, Insts, Jump)|Blocks], Ctx) -->
    { block_label(Ctx, Label, A) },
    [label(A)],
    insts(Insts, 0, Label, Ctx),
    jump(Jump, Label, Ctx),
    blocks(Blocks, Ctx).

% The code of the jump that ends block From.
jump(jmp(To), From, Ctx) -->
    edge(From, To, j, Ctx).
jump(jnz(V, True, False), From, Ctx) -->
    { ctx_fn(Ctx, Fn),
      local_label(Ctx, From, jnz, false, FalseLabel) },
    load(V, w, a, Fn),
    [ins(test, l, [reg(eax), reg(eax)]),
     ins(jz, none, [sym(FalseLabel)])],
    edge(From, True, t, Ctx),
    [label(FalseLabel)],
    edge(From, False, f, Ctx).
jump(ret(V), _, Ctx) -->
    { ctx_ret(Ctx, K) },
    ret_value(K, V, Ctx),
    return(Ctx).
jump(rets(Vs), _, Ctx) -->
    { ctx_ret(Ctx, tuple(Ks)),
      ret_form(Ks, Form) },
    tuple_return(Form, Ks, Vs, Ctx).
jump(ret, _, Ctx) -->
    return(Ctx).
jump(hlt, _, _) -->
    [ins(ud2, none, [])].

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

% The return of the tuple Vs of classes Ks in form Form: in %rdx:%rcx,
% or in the buffer with has_exception = 0.
tuple_return(reg, _, [V1, V2], Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V1, l, d, Fn),
    load(V2, l, c, Fn),
    return(Ctx).
tuple_return(mem(_), Ks, Vs, Ctx) -->
    slot_reg_load(retbuf, rax, Ctx),
    buffer_words(Ks, Vs, 8, Ctx),
    [ins(mov, b, [imm(0), mem(0, rax)])],
    frame_pop(Ctx),
    [ins(leave, none, []), ins(ret, none, [])].

% The words of a buffered return, into the buffer at %rax.
buffer_words([], [], _, _) --> [].
buffer_words([K|Ks], [V|Vs], Off, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, l, d, Fn),
    [ins(mov, q, [reg(rdx), mem(Off, rax)])],
    buffer_word_lower(K, V, Off, Off1, Ctx),
    buffer_words(Ks, Vs, Off1, Ctx).

% The lower, for p, of the buffer word at Off; Off1 is the next word's
% offset.
buffer_word_lower(p, V, Off, Off1, Ctx) -->
    { LowerOff is Off + 8,
      Off1 is Off + 16 },
    lower_reg_load(V, rcx, Ctx),
    [ins(mov, q, [reg(rcx), mem(LowerOff, rax)])].
buffer_word_lower(w, _, Off, Off1, _) -->
    { Off1 is Off + 8 }.
buffer_word_lower(l, _, Off, Off1, _) -->
    { Off1 is Off + 8 }.

% The return in register form, with has_exception = 0 in %al; the
% result, if any, is already in %rdx:%rcx.
return(Ctx) -->
    frame_pop(Ctx),
    [ins(xor, l, [reg(eax), reg(eax)]),
     ins(leave, none, []),
     ins(ret, none, [])].

% Phi copies for the edge, a pollcheck if it goes backwards in block
% order, then the jump.
edge(From, To, Tag, Ctx) -->
    { ctx_labels(Ctx, Labels),
      get_assoc(From, Labels, block(FromIndex, _)),
      get_assoc(To, Labels, block(ToIndex, Phis)),
      block_label(Ctx, To, ToLabel) },
    phi_reads(Phis, From, Ctx),
    phi_writes(Phis, Ctx),
    (   { ToIndex =< FromIndex }
    ->  pollcheck(Ctx, From, Tag)
    ;   []
    ),
    [ins(jmp, none, [sym(ToLabel)])].

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
phi_reads([phi(t(D), K, Pairs)|Phis], From, Ctx) -->
    { memberchk(From-V, Pairs) },
    phi_read(K, V, D, Ctx),
    phi_reads(Phis, From, Ctx).

% The incoming value V, of class K, into the shadow slots of phi t(D).
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
phi_writes([phi(t(D), K, _)|Phis], Ctx) -->
    slot_reg_load(shadow(D), rax, Ctx),
    reg_slot_store(rax, t(D), Ctx),
    phi_lower_write(K, D, Ctx),
    phi_writes(Phis, Ctx).

% For a p phi t(D), its shadow lower into its lower.
phi_lower_write(p, D, Ctx) -->
    slot_reg_load(lower(shadow(D)), rax, Ctx),
    reg_slot_store(rax, lower(t(D)), Ctx).
phi_lower_write(w, _, _) --> [].
phi_lower_write(l, _, _) --> [].
phi_lower_write(s, _, _) --> [].
phi_lower_write(d, _, _) --> [].

% The lower of a p value: its lowers[] entry, or 0 for a constant.
lower_reg_load(t(N), Reg, Ctx) --> slot_reg_load(lower(t(N)), Reg, Ctx).
lower_reg_load(c(_), Reg, _) --> [ins(mov, q, [imm(0), reg(Reg)])].

% A p value's address into %rax and lower into %rcx.
flight_load(V, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(V, l, a, Fn),
    lower_reg_load(V, rcx, Ctx).

% The flight pointer in %rax:%rcx into t(D) and its lower.
flight_store(D, Ctx) -->
    reg_slot_store(rax, t(D), Ctx),
    reg_slot_store(rcx, lower(t(D)), Ctx).

%% Instructions

% The code of each instruction. Invariant: Insts are the instructions
% of Block from index Index on.
insts([], _, _, _) --> [].
insts([Inst|Insts], Index, Block, Ctx) -->
    inst(Inst, Index, Block, Ctx),
    { Index1 is Index + 1 },
    insts(Insts, Index1, Block, Ctx).

% inst(+Inst, +Index, +Block, +Ctx)//: the code of instruction Inst,
% the Indexth of block Block. Instructions go by their op's kind (ir.pl),
% stores and calls by their width and callee.
inst(ins(t(D), K, Op, Args), Index, Block, Ctx) -->
    { op_kind(Op, Kind) },
    kind_inst(Kind, K, Op, Args, D, Index, Block, Ctx).
inst(store(W, V, A), Index, Block, Ctx) -->
    store(W, V, A, Index, Block, Ctx).
inst(call(Res, Callee, Args), Index, Block, Ctx) -->
    callee_call(Callee, Res, Args, Index, Block, Ctx).

% kind_inst(+Kind, +K, +Op, +Args, +D, +Index, +Block, +Ctx)//: as
% inst//4, for t(D) =K Op Args with Op of Kind. Integer instructions go
% to amd64:compute_op//4; the pointer ones are by K, or (copy at p) by
% the operand.
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
kind_inst(ptoi, l, _, [P], D, _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(P, l, a, Fn),
    reg_slot_store(rax, t(D), Ctx).
kind_inst(itop, p, _, [X], D, _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(X, l, a, Fn),
    [ins(xor, l, [reg(ecx), reg(ecx)])],
    flight_store(D, Ctx).
kind_inst(va_args, p, _, [c(Off)], D, _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    flight_load(t(hidden(va_snapshot)), Ctx),
    load(c(Off), l, d, Fn),
    [ins(add, q, [reg(rdx), reg(rax)])],
    flight_store(D, Ctx).
kind_inst(va_arg, K, _, [P], D, Index, Block, Ctx) -->
    { width_bytes(K, Size) },
    origin_store(Ctx, c),
    flight_load(P, Ctx),
    [ins(mov, q, [reg(rax), reg(rdi)]),
     ins(mov, q, [reg(rcx), reg(rsi)]),
     ins(mov, l, [imm(Size), reg(edx)]),
     ins(mov, l, [imm(Size), reg(ecx)]),
     ins(call, none, [plt(filc_get_next_ptr_bytes_for_va_arg)])],
    va_arg_load(K, D, Index, Block, Ctx).
kind_inst(setjmp, w, setjmp(Kind), [Buf, Mask], D, Index, Block, Ctx) -->
    { ctx_fn(Ctx, Fn),
      setjmp_payload_slots(Ctx, Keys),
      ctx_slot(Ctx, lower(t(hidden(setjmp_buf(D)))), Off), NegOff is -Off,
      setjmp_kind(Kind, KindNo),
      local_label(Ctx, Block, Index, setjmp_done, Done) },
    origin_store(Ctx, c),
    slot_reg_load(lower(setjmp_snapshot(D)), rdx, Ctx),
    setjmp_payload_copy(save, Keys, 0, Ctx),
    slot_reg_load(thread, rdi, Ctx),
    [ins(lea, q, [mem(NegOff, rbp), reg(rsi)]),
     ins(mov, l, [imm(KindNo), reg(edx)])],
    load(Mask, w, c, Fn),
    [ins(call, none, [plt(filc_jmp_buf_recreate)]),
     ins(mov, q, [reg(rax), reg(rcx)])],
    flight_store(hidden(setjmp_buf(D)), Ctx),
    store(p, t(hidden(setjmp_buf(D))), Buf, Index, Block, Ctx),
    slot_reg_load(lower(t(hidden(setjmp_buf(D)))), rdi, Ctx),
    [ins(call, none, [plt('_setjmp')]),
     ins(test, l, [reg(eax), reg(eax)]),
     ins(jz, none, [sym(Done)])],
    slot_reg_load(lower(setjmp_snapshot(D)), rdx, Ctx),
    setjmp_payload_copy(restore, Keys, 0, Ctx),
    [label(Done)],
    reg_slot_store(rax, t(D), Ctx).
kind_inst(cmp, K, Op, Args, D, _, _, Ctx) -->
    integer_inst(Op, K, Args, D, Ctx).
kind_inst(ext, K, Op, Args, D, _, _, Ctx) -->
    integer_inst(Op, K, Args, D, Ctx).
kind_inst(load, K, load(T), [A], D, Index, Block, Ctx) -->
    load_inst(T, K, A, D, Index, Block, Ctx).
kind_inst(alloc, p, alloc(Align), [N], D, _, _, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    load(N, l, si, Fn),
    slot_reg_load(thread, rdi, Ctx),
    (   { Align == 16 }
    ->  [ins(mov, l, [imm(16), reg(edx)]),
         ins(call, none, [plt(filc_allocate_with_alignment)])]
    ;   [ins(call, none, [plt(filc_allocate)])]
    ),
    [ins(lea, q, [mem(16, rax), reg(rax)]),
     ins(mov, q, [reg(rax), reg(rcx)])],
    flight_store(D, Ctx).

setjmp_kind(setjmp, 0).
setjmp_kind('_setjmp', 1).
setjmp_kind(sigsetjmp, 2).

% Never copy bookkeeping or any jmpbuf payload slot: their special lowers
% are deliberately not restored by the runtime. Snapshot roots are stable.
setjmp_payload_slots(Ctx, Keys) :-
    ctx_fn(Ctx, f(_, _, Slots, _)), assoc_to_keys(Slots, All),
    findall(Key, (member(Key, All), payload_key(Key)), Keys).
payload_key(t(N)) :- N \= hidden(setjmp_buf(_)).
payload_key(shadow(_)).

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
% instruction t(D) =K Op Args.
integer_inst(Op, K, Args, D, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    compute_op(Op, K, Args, Fn),
    reg_slot_store(rax, t(D), Ctx).

% The helper returns payload and auxiliary *addresses*, not a flight
% pointer. Consume both without a safepoint, then root the loaded lower.
va_arg_load(w, D, _, _, Ctx) -->
    [ins(mov, l, [mem(0, rax), reg(eax)])],
    reg_slot_store(rax, t(D), Ctx).
va_arg_load(l, D, _, _, Ctx) -->
    [ins(mov, q, [mem(0, rax), reg(rax)])],
    reg_slot_store(rax, t(D), Ctx).
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

% additive_inst(+K, +Op, +Args, +D, +Ctx)//: add or sub (Op) at K; at p
% it offsets the flight pointer and keeps its lower.
additive_inst(p, Op, [P, X], D, Ctx) -->
    { ctx_fn(Ctx, Fn) },
    flight_load(P, Ctx),
    load(X, l, d, Fn),
    [ins(Op, q, [reg(rdx), reg(rax)])],
    flight_store(D, Ctx).
additive_inst(w, Op, Args, D, Ctx) --> integer_inst(Op, w, Args, D, Ctx).
additive_inst(l, Op, Args, D, Ctx) --> integer_inst(Op, l, Args, D, Ctx).
additive_inst(K,Op,Args,D,Ctx) -->
    { float_class(K) }, integer_inst(Op,K,Args,D,Ctx).

% copy_inst(+K, +Op, +Args, +D, +Ctx)//: a copy at K.
copy_inst(p, _, [V], D, Ctx) --> pointer_copy(V, D, Ctx).
copy_inst(w, Op, Args, D, Ctx) --> integer_inst(Op, w, Args, D, Ctx).
copy_inst(l, Op, Args, D, Ctx) --> integer_inst(Op, l, Args, D, Ctx).
copy_inst(K,Op,Args,D,Ctx) -->
    { float_class(K) }, integer_inst(Op,K,Args,D,Ctx).

% pointer_copy(+V, +D, +Ctx)//: t(D) =p copy V. A symbol's pointer comes
% from its getter; any other value is a flight pointer already.
pointer_copy(glo(S), D, Ctx) -->
    { ctx_name(Ctx, Name),
      ctx_module(Ctx, Module),
      symbol_getter(Module, S, Getter),
      origin_label(Name, c, Origin) },
    origin_store(Ctx, c),
    slot_reg_load(thread, rdi, Ctx),
    [ins(lea, q, [rip(Origin), reg(rsi)]),
     ins(call, none, [Getter]),
     ins(mov, q, [reg(rdx), reg(rcx)])],
    flight_store(D, Ctx).
pointer_copy(t(N), D, Ctx) --> flight_copy(t(N), D, Ctx).
pointer_copy(c(N), D, Ctx) --> flight_copy(c(N), D, Ctx).

% flight_copy(+V, +D, +Ctx)//: t(D) =p copy V of a temp or constant.
flight_copy(V, D, Ctx) -->
    flight_load(V, Ctx),
    flight_store(D, Ctx).

% load_inst(+T, +K, +A, +D, +Index, +Block, +Ctx)//: a load of type T at
% K from A, the Indexth instruction of Block. A loadp also reads the
% capability; the others read an integer.
load_inst(p, p, A, D, Index, Block, Ctx) -->
    { local_label(Ctx, Block, Index, nolower, NoLower),
      local_label(Ctx, Block, Index, have, Have) },
    flight_load(A, Ctx),
    access_check(k(8, 0, 8), Ctx),
    aux_of_lower,
    [ins(jz, none, [sym(NoLower)]),
     ins(mov, q, [reg(rax), reg(rsi)]),
     ins(sub, q, [reg(rcx), reg(rsi)]),
     ins(mov, q, [mem(0, rdx, rsi), reg(rsi)]),
     ins(test, b, [imm(1), reg(sil)]),
     ins(jz, none, [sym(Have)]),
     ins(and, q, [imm(-2), reg(rsi)]),
     ins(mov, q, [mem(8, rsi), reg(rsi)]),
     ins(jmp, none, [sym(Have)]),
     label(NoLower),
     ins(xor, l, [reg(esi), reg(esi)]),
     label(Have),
     ins(mov, q, [mem(0, rax), reg(rax)]),
     ins(mov, q, [reg(rsi), reg(rcx)])],
    flight_store(D, Ctx).
load_inst(l, K, A, D, _, _, Ctx) --> integer_load(l, K, A, D, Ctx).
load_inst(s,K,A,D,_,_,Ctx) --> integer_load(s,K,A,D,Ctx).
load_inst(d,K,A,D,_,_,Ctx) --> integer_load(d,K,A,D,Ctx).
load_inst(sw, K, A, D, _, _, Ctx) --> integer_load(sw, K, A, D, Ctx).
load_inst(uw, K, A, D, _, _, Ctx) --> integer_load(uw, K, A, D, Ctx).
load_inst(sh, K, A, D, _, _, Ctx) --> integer_load(sh, K, A, D, Ctx).
load_inst(uh, K, A, D, _, _, Ctx) --> integer_load(uh, K, A, D, Ctx).
load_inst(sb, K, A, D, _, _, Ctx) --> integer_load(sb, K, A, D, Ctx).
load_inst(ub, K, A, D, _, _, Ctx) --> integer_load(ub, K, A, D, Ctx).

integer_load(T, K, A, D, Ctx) -->
    { load_type_size_align(T, Size, Align),
      load_insn(T, K, LoadInsn) },
    flight_load(A, Ctx),
    access_check(k(Size, 0, Align), Ctx),
    [LoadInsn],
    reg_slot_store(rax, t(D), Ctx).

% store(+W, +V, +A, +Index, +Block, +Ctx)//: the code of a store of V
% at A of width W, the Indexth instruction of Block.
store(p, V, A, Index, Block, Ctx) -->
    { ctx_fn(Ctx, Fn),
      local_label(Ctx, Block, Index, haveaux, HaveAux),
      local_label(Ctx, Block, Index, nobarrier, NoBarrier) },
    flight_load(A, Ctx),
    access_check(k(8, 1, 8), Ctx),
    aux_of_lower,
    [ins(jnz, none, [sym(HaveAux)])],
    slot_reg_load(thread, rdi, Ctx),
    [ins(lea, q, [mem(-16, rcx), reg(rsi)]),
     ins(call, none, [plt(filc_object_ensure_aux_ptr_outline)]),
     ins(mov, q, [reg(rax), reg(rdx)]),
     label(HaveAux)],
    reg_slot_store(rdx, aux, Ctx),
    lower_reg_load(V, rsi, Ctx),
    [ins(test, q, [reg(rsi), reg(rsi)]),
     ins(jz, none, [sym(NoBarrier)]),
     ins(mov, q, [gotpcrel(filc_current_marking_state), reg(rax)]),
     ins(cmp, l, [imm(0), mem(0, rax)]),
     ins(je, none, [sym(NoBarrier)])],
    slot_reg_load(thread, rdi, Ctx),
    [ins(call, none, [plt(filc_store_barrier_for_lower_slow)]),
     label(NoBarrier)],
    flight_load(A, Ctx),
    slot_reg_load(aux, rdx, Ctx),
    [ins(mov, q, [reg(rax), reg(r8)]),
     ins(sub, q, [reg(rcx), reg(r8)])],
    lower_reg_load(V, rsi, Ctx),
    load(V, l, r9, Fn),
    [ins(mov, q, [reg(rsi), mem(0, rdx, r8)]),
     ins(mov, q, [reg(r9), mem(0, rax)])].
store(b, V, A, _, _, Ctx) --> integer_store(b, V, A, Ctx).
store(h, V, A, _, _, Ctx) --> integer_store(h, V, A, Ctx).
store(w, V, A, _, _, Ctx) --> integer_store(w, V, A, Ctx).
store(l, V, A, _, _, Ctx) --> integer_store(l, V, A, Ctx).
store(s,V,A,_,_,Ctx) --> integer_store(s,V,A,Ctx).
store(d,V,A,_,_,Ctx) --> integer_store(d,V,A,Ctx).

% The code of a store of the integer V at A of width W.
integer_store(W, V, A, Ctx) -->
    { ctx_fn(Ctx, Fn),
      width_bytes(W, Size),
      width_value_class(W, ValueK),
      store_insn(W, d, StoreInsn) },
    flight_load(A, Ctx),
    access_check(k(Size, 1, 1), Ctx),
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

% callee_call(+Callee, +Res, +Args, +Index, +Block, +Ctx)//: the code of
% a call of Callee, the Indexth instruction of Block.
callee_call(glo(F), Res, Args, _, _, Ctx) -->
    { call_target(Ctx, F, Res, Args, Target),
      result_form(Res, _, _, Form) },
    origin_store(Ctx, c),
    ret_buffer_reservation(Form),
    fast_call(Form, Args, direct(Target), Ctx),
    fast_result(Form, Res, Ctx),
    ret_buffer_release(Form).

/* A call through a p value. The callee must be a function object: lower
   not 0, ptr equal to the object's aux pointer, and special type
   function. Then the fast entry if the signature matches the call site's,
   else the generic entry with every argument as an 8-byte word at
   thread+128+8i and its lower at thread+384+8i (docs/abi-findings.md). */
callee_call(t(C), Res, Args, Index, Block, Ctx) -->
    { ctx_fn(Ctx, Fn),
      call_sig(Res, Args, _, _, Sig),
      result_form(Res, Tos, RetKs, Form),
      special_label(Ctx, notfn, NotFn),
      special_label(Ctx, exc, Exc),
      length(Args, NArgs),
      ArgsSize is 8 * NArgs,
      local_label(Ctx, Block, Index, generic, Generic),
      local_label(Ctx, Block, Index, done, Done),
      local_label(Ctx, Block, Index, retok, RetOk) },
    origin_store(Ctx, c),
    ret_buffer_reservation(Form),
    flight_load(t(C), Ctx),
    function_check(NotFn),
    reg_slot_store(rcx, aux, Ctx),
    { field(function_object, signature, rcx, FoSig),
      field(function_object, generic_entry, rsi, FoGeneric) },
    [ins(movabs, q, [imm(Sig), reg(rsi)]),
     ins(cmp, q, [reg(rsi), FoSig]),
     ins(jne, none, [sym(Generic)])],
    fast_call(Form, Args, indirect, Ctx),
    fast_result(Form, Res, Ctx),
    [ins(jmp, none, [sym(Done)]),
     label(Generic)],
    generic_call_args(Args, 0, Fn, Ctx),
    slot_reg_load(thread, rdi, Ctx),
    slot_reg_load(aux, rsi, Ctx),
    [ins(mov, l, [imm(ArgsSize), reg(edx)]),
     ins(call, q, [ind(FoGeneric)]),
     ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Exc)])],
    generic_results(Tos, RetKs, RetOk, Ctx),
    [label(Done)],
    ret_buffer_release(Form).

% The results Tos, of classes RetKs, of a generic call, after a check of
% the return size.
generic_results([], _, _, _) --> [].
generic_results([To|Tos], RetKs, RetOk, Ctx) -->
    { length([To|Tos], NRetWords),
      Need is 8 * NRetWords,
      generic_words(RetKs, GWs) },
    slot_reg_load(thread, rsi, Ctx),
    rets_check(Need, RetOk),
    generic_slot_copies(GWs, [To|Tos], Ctx).

% Arguments, the entry registers and the call itself, for the fast
% convention in form Form; Callee is direct(Symbol) or indirect (through
% the aux slot).
fast_call(Form, Args, Callee, Ctx) -->
    { ctx_fn(Ctx, Fn),
      typed_args(Args, Ts),
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
fast_result(reg, Res, Ctx) -->
    { Res=to(T,K), float_class(K), special_label(Ctx,exc,Exc) }, !,
    [ins(test,b,[imm(1),reg(al)]),ins(jnz,none,[sym(Exc)])],
    from_xmm(K,xmm0,a), reg_slot_store(rax,T,Ctx).
fast_result(reg, Res, Ctx) -->
    { special_label(Ctx, exc, Exc),
      result_slots(Res, Slots) },
    [ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Exc)])],
    reg_slot_stores(Slots, [rdx, rcx], Ctx).
fast_result(mem(_), Res, Ctx) -->
    { special_label(Ctx, exc, Exc),
      result_slots(Res, Slots) },
    [ins(cmp, b, [imm(0), mem(0, rsp)]),
     ins(jne, none, [sym(Exc)])],
    buffer_slot_copies(Slots, 8, Ctx).

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
generic_slot_copies([], [], _) --> [].
generic_slot_copies([gw(K, Off)|GWs], [to(T, _)|Tos], Ctx) -->
    [ins(mov, q, [mem(Off, rsi), reg(rax)])],
    reg_slot_store(rax, T, Ctx),
    generic_lower_slot_copy(K, Off, T, Ctx),
    generic_slot_copies(GWs, Tos, Ctx).

% For a p word at thread offset Off, its lower into lower(T).
generic_lower_slot_copy(p, Off, T, Ctx) -->
    { LowerOff is Off + 256 },
    [ins(mov, q, [mem(LowerOff, rsi), reg(rax)])],
    reg_slot_store(rax, lower(T), Ctx).
generic_lower_slot_copy(w, _, _, _) --> [].
generic_lower_slot_copy(l, _, _, _) --> [].
generic_lower_slot_copy(s, _, _, _) --> [].
generic_lower_slot_copy(d, _, _, _) --> [].

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
generic_call_args([], _, _, _) --> [].
generic_call_args([arg(K, V)|Args], I, Fn, Ctx) -->
    { generic_offsets(I, Addr, Lower) },
    flight_value(K, V, Fn, Ctx),
    slot_reg_load(thread, rdx, Ctx),
    [ins(mov, q, [reg(rax), mem(Addr, rdx)]),
     ins(mov, q, [reg(rcx), mem(Lower, rdx)])],
    { I1 is I + 1 },
    generic_call_args(Args, I1, Fn, Ctx).

% The value V of class K in %rax, with its lower (0 for an integer) in
% %rcx.
flight_value(p, V, Fn, Ctx) -->
    load(V, l, a, Fn),
    lower_reg_load(V, rcx, Ctx).
flight_value(w, V, Fn, _) -->
    load(V, w, a, Fn),
    [ins(xor, l, [reg(ecx), reg(ecx)])].
flight_value(l, V, Fn, _) -->
    load(V, l, a, Fn),
    [ins(xor, l, [reg(ecx), reg(ecx)])].
flight_value(K,V,Fn,_) -->
    { float_class(K) }, load(V,K,a,Fn),
    [ins(xor,l,[reg(ecx),reg(ecx)])].

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

% symbol_getter(+Module, +S, -Getter): Getter is the call operand of
% S's getter, a local sym if Module defines S and a plt one otherwise.
symbol_getter(module(Items), S, Getter) :-
    abi_symbol(getter, S, Name),
    (   (   memberchk(func(S, _, _, _, _), Items)
        ;   memberchk(data(S, _, _, _), Items)
        )
    ->  Getter = sym(Name)
    ;   Getter = plt(Name)
    ).

% The aux pointer of the object at lower %rcx into %rdx, setting ZF if
% it has none.
aux_of_lower -->
    { aux_pointer_mask(Mask) },
    [ins(mov, q, [mem(-8, rcx), reg(rdx)]),
     ins(movabs, q, [imm(Mask), reg(rsi)]),
     ins(and, q, [reg(rsi), reg(rdx)])].

% load_type_size_align(?T, ?Size, ?Align): a load of type T reads Size
% bytes, and its address is checked for alignment Align (8 for a pointer
% load, so its lower is in the aux array).
load_type_size_align(p, 8, 8).
load_type_size_align(l, 8, 1).
load_type_size_align(s,4,1).
load_type_size_align(d,8,1).
load_type_size_align(sw, 4, 1).
load_type_size_align(uw, 4, 1).
load_type_size_align(sh, 2, 1).
load_type_size_align(uh, 2, 1).
load_type_size_align(sb, 1, 1).
load_type_size_align(ub, 1, 1).

% width_align(?W, ?Align): a store of width W is checked for alignment
% Align.
width_align(p, 8).
width_align(l, 1).
width_align(w, 1).
width_align(s,1).
width_align(d,1).
width_align(h, 1).
width_align(b, 1).

% call_target(+Ctx, +F, +Res, +Args, -Target): Target is the operand a
% direct call of F calls. Functions in the module are called at their
% implementation; others at
% their pizlonatedFI symbol: a weak thunk this module emits (thunk//1),
% overridden by a clang definition with the same signature if one is
% linked in.
call_target(Ctx, F, Res, Args, sym(Target)) :-
    ctx_module(Ctx, Module),
    (   func_named(Module, F, Func), \+ variadic_func(Func)
    ->  func_signature(Func, Sig),
        abi_symbol(impl(Sig), F, Target)
    ;   call_sig(Res, Args, _, _, Sig),
        abi_symbol(entry(Sig), F, Target)
    ).

% call_sig(+Res, +Args, -RetKind, -ArgKinds, -Sig): a call site with
% result Res and arguments Args has return type RetKind, argument
% classes ArgKinds and signature Sig.
call_sig(Res, Args, RetKind, ArgKinds, Sig) :-
    result_ret(Res, RetKind),
    findall(K, member(arg(K, _), Args), ArgKinds),
    signature(RetKind, ArgKinds, Sig).

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
typed_params(Ps,Ts) :- foldl(typed_param,Ps,Ts,[]).
typed_param(par(p,T),[wf(l,T),wf(l,lower(T))|Ts],Ts).
typed_param(par(K,T),[wf(K,T)|Ts],Ts) :- K \== p.
typed_args(As,Ts) :- foldl(typed_arg,As,Ts,[]).
typed_arg(arg(p,V),[wf(l,addr(V)),wf(l,lower(V))|Ts],Ts).
typed_arg(arg(K,V),[wf(K,val(K,V))|Ts],Ts) :- K \== p.
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

typed_generic(Ks,Ts) :- typed_generic(Ks,0,Ts).
typed_generic([],_,[]).
typed_generic([K|Ks],I,Ts) :-
    generic_offsets(I,A,L),
    ( K==p -> Ts=[wf(l,mem(A,rbx)),wf(l,mem(L,rbx))|Rest]
    ; Ts=[wf(K,mem(A,rbx))|Rest] ),
    I1 is I+1, typed_generic(Ks,I1,Rest).


/* thunk(+Callee)//: the weak thunk of Callee = t(F, Sig, Ret, Ks),
   which resolves F through its getter and calls the fast entry when
   the signature matches, else the generic entry. Every incoming word,
   integer or XMM, is saved below rbp before the getter can exit or
   clobber caller-saved registers; rbx holds the thread (r12 the return
   buffer) and -24(%rbp) the function object. Pointer authority stays
   rooted by the caller. */
thunk(t(F,Sig,Ret,Ks)) -->
    { abi_symbol(entry(Sig),F,FI), abi_symbol(getter,F,Getter),
      atom_concat('.L',FI,G),atom_concat(G,'.generic',Generic),
      atom_concat(G,'.out',Out),atom_concat(G,'.fail',Fail),
      atom_concat(G,'.retok',RetOk),atom_concat(G,'.exc',Exc),
      ret_kinds(Ret,RKs),ret_form(RKs,Form),
      findall(par(K,t(I)),nth0(I,Ks,K),Ps),typed_params(Ps,Ts),
      typed_locations(Ts,Form,Ls,NS,_), stack_bytes(NS, Pop),
      saved_words(Ts,0,Saved),length(Ts,NW),Alloc is ((8+8*NW+15)//16)*16,
      length(Ks,NA),ArgsSize is 8*NA,
      length(RKs,NR),Need is 8*NR,generic_words(RKs,GWs),
      field(function_object,generic_entry,rsi,GenericEntry) },
    [section(text),p2align(4),hidden(FI),weak(FI),type(FI,function),label(FI),
     ins(push,q,[reg(rbp)]),ins(mov,q,[reg(rsp),reg(rbp)]),
     ins(push,q,[reg(rbx)]),ins(push,q,[reg(r12)]),
     ins(sub,q,[imm(Alloc),reg(rsp)])],
    mixed_thunk_thread(Form), save_mixed_words(Ts,Ls,Saved),
    [ins(xor,l,[reg(esi),reg(esi)]),ins(call,none,[plt(Getter)]),
     ins(mov,q,[reg(rdx),reg(rcx)])],
    function_check(Fail),
    { field(function_object,signature,rcx,Signature) },
    [ins(mov,q,[reg(rcx),mem(-24,rbp)]),
     ins(movabs,q,[imm(Sig),reg(rsi)]),ins(cmp,q,[reg(rsi),Signature]),
     ins(jne,none,[sym(Generic)])],
    reserve_stack(Pop),adapter_stack(Saved,Ls,G),adapter_registers(Saved,Ls,G),
    mixed_thunk_call(Form),
    [ins(jmp,none,[sym(Out)]),label(Generic)],
    saved_generic(Ks,Saved,0),
    [ins(mov,q,[reg(rbx),reg(rdi)]),ins(mov,q,[mem(-24,rbp),reg(rsi)]),
     ins(mov,l,[imm(ArgsSize),reg(edx)]),
     ins(call,q,[ind(GenericEntry)]),ins(test,b,[imm(1),reg(al)])],
    thunk_generic_return(Form,RKs,Need,GWs,Out,RetOk,Exc),
    [label(Fail),ins(mov,q,[reg(rax),reg(rdi)]),ins(mov,q,[reg(rcx),reg(rsi)]),
     ins(call,none,[plt(filc_check_function_call_fail)]),ins(ud2,none,[]),
     label(Out),ins(lea,q,[mem(-16,rbp),reg(rsp)]),
     ins(pop,q,[reg(r12)]),ins(pop,q,[reg(rbx)]),ins(pop,q,[reg(rbp)]),
     ins(ret,none,[]),size(FI)].

saved_words([],_,[]).
saved_words([wf(K,_)|Ts],I,[wf(K,mem(O,rbp))|Ss]) :-
    O is -32-8*I,I1 is I+1,saved_words(Ts,I1,Ss).
mixed_thunk_thread(reg) --> [ins(mov,q,[reg(rdi),reg(rbx)])].
mixed_thunk_thread(mem(_)) -->
    [ins(mov,q,[reg(rdi),reg(r12)]),ins(mov,q,[reg(rsi),reg(rbx)]),
     ins(mov,q,[reg(rsi),reg(rdi)])].
save_mixed_words([],[],[]) --> [].
save_mixed_words([wf(K,_)|Ts],[L|Ls],[wf(_,W)|Ss]) -->
    incoming_bits(L,K),[ins(mov,q,[reg(rax),W])],save_mixed_words(Ts,Ls,Ss).
mixed_thunk_call(reg) -->
    { field(function_object,fast_entry,rsi,Fast) },
    [ins(mov,q,[reg(rbx),reg(rdi)]),ins(mov,q,[mem(-24,rbp),reg(rsi)]),
     ins(call,q,[ind(Fast)])].
mixed_thunk_call(mem(_)) -->
    { field(function_object,fast_entry,rdx,Fast) },
    [ins(mov,q,[reg(r12),reg(rdi)]),ins(mov,q,[reg(rbx),reg(rsi)]),
     ins(mov,q,[mem(-24,rbp),reg(rdx)]),ins(call,q,[ind(Fast)])].
saved_generic([],[],_) --> [].
saved_generic([p|Ks],[wf(_,A),wf(_,L)|Ts],I) -->
    { generic_offsets(I,AO,LO),I1 is I+1 },
    operand_thread_store(A,AO),operand_thread_store(L,LO),saved_generic(Ks,Ts,I1).
saved_generic([K|Ks],[wf(_,W)|Ts],I) -->
    { K\==p,generic_offsets(I,AO,LO),I1 is I+1 },
    adapter_load(K,W,unused),
    [ins(mov,q,[reg(rax),mem(AO,rbx)]),ins(mov,q,[imm(0),mem(LO,rbx)])],
    saved_generic(Ks,Ts,I1).

%% Access checks: k(Size, Write, Align), with the pointer in %rax and its
%% lower in %rcx, which the failure block passes on.

% A jump to the kind's failure block unless the pointer may be accessed:
% lower not 0, lower =< ptr =< upper - Size, the object's flags
% permitting a write if Write is 1, and ptr 8-aligned if Align is 8.
access_check(k(Size, Write, Align), Ctx) -->
    { check_fail_label(Ctx, k(Size, Write, Align), Fail) },
    [ins(test, q, [reg(rcx), reg(rcx)]),
     ins(jz, none, [sym(Fail)]),
     ins(cmp, q, [reg(rcx), reg(rax)]),
     ins(jb, none, [sym(Fail)]),
     ins(mov, q, [mem(-16, rcx), reg(rdx)]),
     ins(sub, q, [imm(Size), reg(rdx)]),
     ins(cmp, q, [reg(rdx), reg(rax)]),
     ins(ja, none, [sym(Fail)])],
    write_check(Write, Fail),
    align_check(Align, Fail).

% For a write (Write = 1), a check of the object's read-only flags.
write_check(0, _) --> [].
write_check(1, Fail) -->
    [ins(test, b, [imm(6), mem(-2, rcx)]),
     ins(jnz, none, [sym(Fail)])].

% For Align = 8, a check that the pointer is 8-aligned.
align_check(1, _) --> [].
align_check(8, Fail) -->
    [ins(test, b, [imm(7), reg(al)]),
     ins(jnz, none, [sym(Fail)])].

% The labels of a check kind's failure block and origin.
check_fail_label(Ctx, k(Size, Write, Align), Label) :-
    ctx_name(Ctx, Name),
    format(atom(Label), '.L~w..fail.~w.~w.~w', [Name, Size, Write, Align]).

check_origin_label(Name, k(Size, Write, Align), Label) :-
    format(atom(Label), '.L~w..chk.~w.~w.~w', [Name, Size, Write, Align]).

% The distinct check kinds the function's accesses need.
access_check_kinds(Blocks, Kinds) :-
    findall(Kind,
            (   member(blk(_, _, Insts, _), Blocks),
                member(Inst, Insts),
                inst_check_kind(Inst, Kind)
            ),
            Kinds0),
    sort(Kinds0, Kinds).

% inst_check_kind(+Inst, -Kind): Inst's access needs a check of Kind;
% fails if Inst does not access memory.
inst_check_kind(ins(_, _, load(T), _), k(Size, 0, Align)) :-
    load_type_size_align(T, Size, Align).
inst_check_kind(ins(_, _, setjmp(_), _), k(8, 1, 8)).
inst_check_kind(store(W, _, _), k(Size, 1, Align)) :-
    width_bytes(W, Size),
    width_align(W, Align).

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
variadic_object(Name, Linkage, Ret, Params, Impl) -->
    { abi_symbol(function_object, Name, FO),
      abi_symbol(getter, Name, Getter),
      abi_symbol(impl(0), Name, Generic),
      abi_symbol(entry(0), Name, FI),
      atom_concat(Generic, '.body', BodyObject) },
    linkage_alias(Linkage, FI, Generic, Getter),
    object_getter(Getter, FO),
    variadic_adapter(Generic, BodyObject, Ret, Params),
    [section(data_rel_ro), p2align(4), label(BodyObject), quad(Impl)],
    function_object_data(FO, 0, Generic, 0).

variadic_adapter(Generic, BodyObject, Ret, Params) -->
    { length(Params, N), Need is N * 8,
      ret_kinds(Ret, RetKs), ret_form(RetKs, Form),
      snapshot_words(Params, Ts),
      typed_locations(Ts, Form, Ls, NS, _),
      stack_bytes(NS, Pop),
      length(RetKs, NRet), RetSize is 8 * max(1, NRet),
      generic_words(RetKs, GWs), foldl(generic_srcs, GWs, Dests, []),
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
    generic_entry_call(Form, RetKs, GWs, Dests, Pop, RetSize, Done),
    [ins(pop, q, [reg(r13)]), ins(pop, q, [reg(r12)]),
     ins(pop, q, [reg(rbx)]), ins(ret, none, []),
     label(Short), ins(mov, q, [reg(rdx), reg(rdi)]),
     ins(mov, l, [imm(Need), reg(esi)]),
     ins(xor, l, [reg(edx), reg(edx)]),
     ins(call, none, [plt(filc_cc_args_check_failure)]),
     ins(ud2, none, [])].

% snapshot_words(+Params, -Ts): the words of the fast body's arguments,
% read from the argument snapshot at %r12 (lowers from its aux at %r13),
% then the snapshot itself as the hidden p parameter.
snapshot_words(Ps, Ts) :-
    findall(wf(B, W),
            (   nth0(I, Ps, par(K, _)),
                snapshot_word(K, I, W),
                ( K == p -> B = l ; B = K )
            ),
            Ts0),
    append(Ts0, [wf(l, reg(r12)), wf(l, reg(r12))], Ts).

snapshot_word(_, I, mem(Off, r12)) :- Off is 8 * I.
snapshot_word(p, I, snapshot_lower(Off)) :- Off is 8 * I.

snapshot_load(reg(R), _) --> [ins(mov, q, [reg(R), reg(rax)])].
snapshot_load(mem(O, R), _) --> [ins(mov, q, [mem(O, R), reg(rax)])].
snapshot_load(snapshot_lower(O), G) -->
    { format(atom(NoAux), '~w.lower.~w', [G, O]) },
    [ins(xor, l, [reg(eax), reg(eax)]),
     ins(test, q, [reg(r13), reg(r13)]),
     ins(jz, none, [sym(NoAux)]),
     ins(mov, q, [mem(O, r13), reg(rax)]), label(NoAux)].

function_object(Name, Linkage, Ret, Params, Sig, Impl) -->
    { abi_symbol(entry(Sig), Name, FI),
      abi_symbol(function_object, Name, FO),
      abi_symbol(getter, Name, Getter),
      format(atom(Generic), '.L~w..generic', [Name]) },
    linkage_alias(Linkage, FI, Impl, Getter),
    object_getter(Getter, FO),
    generic_entry(Generic, Ret, Params),
    [section(data_rel_ro), p2align(4)],
    function_object_data(FO, Impl, Generic, Sig).

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

% The .globl of S if its linkage is export.
linkage_globl(export, S) --> [globl(S)].
linkage_globl(local, _) --> [].

%% Data objects, as clang lays out globals (docs/abi-findings.md):
%% DO_d = {upper, aux} then the payload rounded up to 8 bytes, a 16-byte
%% cache GP_d, an aux array DA_d if the payload holds pointers, and a
%% getter whose slow path registers the object and runs the relocations
%% that fill in its pointers.

data_object(Name, Linkage0, Items) -->
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
      Total is 16 + Size },
    [section(data), p2align(4), type(DO, object), label(DO),
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
    phrase(asm_string_length(N), Cs),
    Off is Off0 + N.
value_payload(sym(S, Addend), p, quad(0), Off0-Rs,
              Off-[r(Off0, S, Addend)|Rs]) :-
    (   Off0 mod 8 =:= 0
    ->  true
    ;   throw(nanofil_error('pointer data item is not 8-aligned'))
    ),
    Off is Off0 + 8.
value_payload(c(N), W, Directive, Off0-Rs, Off-Rs) :-
    width_bytes(W, Bytes),
    Bits is 8 * Bytes,
    U is N mod (1 << Bits),
    memberchk(Bytes-Directive,
              [1-byte([U]), 2-short(U), 4-long(U), 8-quad(U)]),
    Off is Off0 + Bytes.

% The byte length of an ascii string with GNU as escapes.
asm_string_length(0) --> [].
asm_string_length(N) -->
    ['\\'],
    !,
    escape_tail,
    asm_string_length(N0),
    { N is N0 + 1 }.
asm_string_length(N) -->
    [_],
    asm_string_length(N0),
    { N is N0 + 1 }.

% After a backslash: up to three octal digits, or one other character.
escape_tail -->
    octal_digit,
    !,
    octal_upto(2).
escape_tail -->
    [_].

% As many octal digits as there are, up to K.
octal_upto(0) --> !.
octal_upto(K) -->
    octal_digit,
    !,
    { K1 is K - 1 },
    octal_upto(K1).
octal_upto(_) --> [].

octal_digit -->
    [D],
    { char_code(D, C),
      C >= 0'0,
      C =< 0'7 }.

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

%% Thunks for functions outside the module, as clang emits them: a hidden
%% weak pizlonatedFI<sig>_f that gets f's function object from its getter,
%% checks it, and calls the fast entry if the signature matches or the
%% generic entry otherwise. A clang definition of the same symbol wins.

% external_callees(+Module, -Callees): Callees are t(F, Sig, RetKind,
% ArgKinds), sorted, one for each thunk the module needs.
external_callees(Module, Callees) :-
    Module = module(Items),
    findall(t(F, Sig, RetKind, ArgKinds),
            (   member(func(_, _, _, _, Blocks), Items),
                member(blk(_, _, Insts, _), Blocks),
                member(call(Res, glo(F), Args), Insts),
                ( \+ func_named(Module, F, _)
                ; func_named(Module, F, VF), variadic_func(VF) ),
                call_sig(Res, Args, RetKind, ArgKinds, Sig)
            ),
            Callees0),
    sort(Callees0, Callees1),
    one_per_symbol(Callees1, Callees).

% one_per_symbol(+Callees0, -Callees): Callees keeps the first callee
% in Callees0 of each symbol, F and Sig. w and l are the same word, so
% call sites that differ only there share a thunk.
one_per_symbol([], []).
one_per_symbol([T|Ts0], [T|Ts]) :-
    T = t(F, Sig, _, _),
    exclude(same_symbol(F, Sig), Ts0, Ts1),
    one_per_symbol(Ts1, Ts).

same_symbol(F, Sig, t(F, Sig, _, _)).

% thunk_generic_return(+Form, +RetKs, +Need, +GWs, +Out, +RetOk,
% +GenericExc)//: the return, in form Form, of the generic entry's
% result words GWs, of classes RetKs and Need bytes, then a jump to Out.
thunk_generic_return(reg, RetKs, Need, GWs, Out, RetOk, _) -->
    [ins(jnz, none, [sym(Out)])],
    thunk_generic_reg_words(RetKs, Need, GWs, RetOk),
    [ins(xor, l, [reg(eax), reg(eax)]),
     ins(jmp, none, [sym(Out)])].
thunk_generic_return(mem(_), _, Need, GWs, Out, RetOk, GenericExc) -->
    [ins(jnz, none, [sym(GenericExc)])],
    rets_check(Need, RetOk),
    { foldl(generic_srcs, GWs, Srcs, []) },
    thunk_buffer_copies(Srcs, 8),
    [ins(mov, b, [imm(0), mem(0, r12)]),
     ins(mov, q, [reg(r12), reg(rax)]),
     ins(jmp, none, [sym(Out)]),
     label(GenericExc),
     ins(mov, b, [imm(1), mem(0, r12)]),
     ins(mov, q, [reg(r12), reg(rax)]),
     ins(jmp, none, [sym(Out)])].

% The result words, if RetKs has any, in %rdx:%rcx.
thunk_generic_reg_words([], _, _, _) --> [].
thunk_generic_reg_words([K],Need,[gw(K,Off)],RetOk) -->
    { float_class(K),att_suffix(K,S),reg_name(d,K,R) }, !,
    rets_check(Need,RetOk),
    [ins(mov,S,[mem(Off,rbx),reg(R)])],to_xmm(K,d,xmm0).
thunk_generic_reg_words([_|_], Need, GWs, RetOk) -->
    rets_check(Need, RetOk),
    { foldl(generic_srcs, GWs, Srcs, []) },
    thunk_reg_loads(Srcs, [rdx, rcx]).

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
generic_entry(Generic, Ret, Params) -->
    { findall(K,member(par(K,_),Params),Ks),
      length(Params,N), Need is 8*N,
      ret_kinds(Ret,RKs),ret_form(RKs,Form),
      typed_generic(Ks,Ts),typed_locations(Ts,Form,Ls,NS,_),
      stack_bytes(NS, Pop),
      length(RKs,NR), RetSize is 8*max(1,NR),
      generic_words(RKs,GWs),foldl(generic_srcs,GWs,Dests,[]),
      atom_concat(Generic,'.short',Short),atom_concat(Generic,'.done',Done) },
    [section(text),label(Generic),ins(push,q,[reg(rbx)]),
     ins(cmp,q,[imm(Need),reg(rdx)]),ins(jb,none,[sym(Short)]),
     ins(mov,q,[reg(rdi),reg(rbx)])],
    ret_buffer_reservation(Form), reserve_stack(Pop),
    adapter_stack(Ts,Ls,Generic),adapter_registers(Ts,Ls,Generic),
    generic_entry_call(Form,RKs,GWs,Dests,Pop,RetSize,Done),
    [ins(pop,q,[reg(rbx)]),ins(ret,none,[]),label(Short),
     ins(mov,q,[reg(rdx),reg(rdi)]),ins(mov,l,[imm(Need),reg(esi)]),
     ins(xor,l,[reg(edx),reg(edx)]),
     ins(call,none,[plt(filc_cc_args_check_failure)]),ins(ud2,none,[])].
/* generic_entry_call(+Form, +RetKs, +GWs, +Dests, +Pop, +RetSize,
   +Done)//: the generic entry's call of the fast entry in form Form,
   then the result words GWs, of classes RetKs, at their thread offsets
   Dests, and the return size RetSize in %edx. Pop is the size of the
   pushed argument words. */
generic_entry_call(reg, RetKs, GWs, Dests, Pop, RetSize, Done) -->
    { field(function_object, fast_entry, rsi, Fast) },
    [ins(call, q, [ind(Fast)])],
    stack_release(Pop),
    [ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Done)])],
    generic_reg_results(RetKs, GWs, Dests),
    [ins(mov, l, [imm(RetSize), reg(edx)]),
     label(Done)].
generic_entry_call(mem(Bytes), _, GWs, Dests, Pop, RetSize, Done) -->
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
    generic_lower_zeroings(GWs),
    [ins(mov, l, [imm(RetSize), reg(edx)]),
     ins(xor, l, [reg(eax), reg(eax)]),
     label(Done)],
    ret_buffer_release(mem(Bytes)).

% The result words from %rdx:%rcx at their thread offsets; a void result
% is one zero word.
generic_reg_results([], _, _) -->
    { generic_offsets(0, Addr, Lower) },
    [ins(mov, q, [imm(0), mem(Addr, rbx)]),
     ins(mov, q, [imm(0), mem(Lower, rbx)])].
generic_reg_results([K], [gw(K,Off)], _) -->
    { float_class(K), Lower is Off+256 }, !,
    from_xmm(K,xmm0,d),
    [ins(mov,q,[reg(rdx),mem(Off,rbx)]),
     ins(mov,q,[imm(0),mem(Lower,rbx)])].
generic_reg_results([_|_], GWs, Dests) -->
    generic_reg_stores(Dests, [rdx, rcx]),
    generic_lower_zeroings(GWs).

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

% An integer result word has no lower.
generic_lower_zeroings([]) --> [].
generic_lower_zeroings([gw(K, Off)|GWs]) -->
    generic_lower_zeroing(K, Off),
    generic_lower_zeroings(GWs).

generic_lower_zeroing(p, _) --> [].
generic_lower_zeroing(w, Off) -->
    { LowerOff is Off + 256 },
    [ins(mov, q, [imm(0), mem(LowerOff, rbx)])].
generic_lower_zeroing(l, Off) -->
    { LowerOff is Off + 256 },
    [ins(mov, q, [imm(0), mem(LowerOff, rbx)])].

%% Static data: function origins (staging's 48-byte layout), origins,
%% and one access-check origin per check kind.

% The name string, the c and n function origins with their origins, and
% the check origins of function Name.
origins(Name, NLowers, CheckKinds, NumSetjmps) -->
    { format(atom(NameLabel), '.L~w..name', [Name]) },
    [section(rodata), label(NameLabel), asciz(Name),
     section(data_rel_ro), p2align(4)],
    function_origin(Name, NameLabel, NLowers, c, 1, NumSetjmps),
    function_origin(Name, NameLabel, NLowers, n, 0, NumSetjmps),
    check_origins(CheckKinds, Name).

% A function origin and the origin (origin_label/3) that points at it.
function_origin(Name, NameLabel, NLowers, Which, CanCatch, NumSetjmps) -->
    { format(atom(FOrigin), '.L~w..forigin_~w', [Name, Which]),
      origin_label(Name, Which, Origin) },
    [label(FOrigin),
     quad(NameLabel), quad(0),
     long(NLowers), zero(4),
     quad(0),
     byte([0, CanCatch]), zero(2),
     long(NumSetjmps), long(0), zero(4),
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
