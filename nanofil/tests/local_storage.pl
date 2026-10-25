/* The local-storage contract: selection is conservative, while overlapping
   bytes and capability-bearing contents retain their memory semantics. */
:- module(local_storage_tests, [local_selection/0, local_semantics/0,
                                local_lifetime/0, local_validation/0]).

:- use_module('../src/local_storage').
:- use_module('../src/ir').
:- use_module('../src/ir_text').
:- use_module('../src/interp').
:- use_module('../src/opt').
:- use_module('../src/pizlonate').
:- use_module(library(clpz)).
:- use_module(library(lists)).

local_selection :-
    selected_overlap,
    forall(heap_case(Params, Insts, Jump), remains_heap(Params, Insts, Jump)),
    plain_unchanged,
    nonentry_unchanged,
    redefinition_unchanged,
    dead_float_unchanged,
    forall(float_heap_case(_, _, M, Expected),
           optimized_float_heap(M, Expected)),
    storage_budget,
    zero_size.

selected_overlap :-
    overlap(F), local_storage_module(module([F]), M),
    M = module([func(overlap, export, l, [], [block(s, [], Is, ret(tmp(r)))])]),
    Is == [local_alloc(a, 13), local_store(h, const(4660), a, 0),
           local_store(b, const(86), a, 1), local_load(tmp(r), l, l, a, 0)].

overlap(func(overlap, export, l, [], [block(s, [], [
    let(tmp(a), p, alloc(8), [const(13)]),
    let(tmp(b), p, add, [tmp(a), const(1)]),
    store(h, const(4660), tmp(a)), store(b, const(86), tmp(b)),
    let(tmp(r), l, load(l), [tmp(a)])
], ret(tmp(r)))])).

remains_heap(Ps, Is, J) :-
    F = func(f, export, void, Ps, [block(s, [], Is, J)]),
    local_storage_module(module([F]), M), M == module([F]).

% Each unsupported use must keep the allocation, not just its access.
heap_case([], [let(tmp(a), p, alloc(8), [const(9)]),
               let(tmp(b), p, add, [tmp(a), const(9)]),
               store(b, const(1), tmp(b))], ret).
heap_case([], [let(tmp(a), p, alloc(8), [const(8)]),
               call(void, global(sink), [arg(p, tmp(a))])], ret).
heap_case([param(p, tmp(dst))],
          [let(tmp(a), p, alloc(8), [const(8)]),
           store(p, tmp(a), tmp(dst))], ret).
heap_case([], [let(tmp(a), p, alloc(8), [const(8)]),
               let(tmp(i), l, ptoi, [tmp(a)])], ret).
heap_case([param(l, tmp(n))],
          [let(tmp(a), p, alloc(8), [const(16)]),
           let(tmp(b), p, add, [tmp(a), tmp(n)]),
           store(b, const(1), tmp(b))], ret).
heap_case([param(l, tmp(n))],
          [let(tmp(a), p, alloc(8), [tmp(n)]),
           store(b, const(1), tmp(a))], ret).
heap_case([param(p, tmp(buf))],
          [let(tmp(a), p, alloc(8), [const(8)]),
           let(tmp(j), w, setjmp('_setjmp'), [tmp(buf), const(0)]),
           store(b, const(1), tmp(a))], ret).
% Float loads are not described by escape's slot vocabulary yet. In
% particular this 4-byte load must not look like a completely unused alloc.
heap_case([], [let(tmp(a), p, alloc(8), [const(1)]),
               let(tmp(x), s, load(s), [tmp(a)])], ret).
heap_case([], [let(tmp(a), p, alloc(8), [const(0)]),
               store(b, const(1), tmp(a))], ret).
heap_case([], [let(tmp(a), p, alloc(8), [const(13)]),
               let(tmp(b), p, add, [tmp(a), const(12)]),
               store(h, const(1), tmp(b))], ret).
heap_case([], [let(tmp(a), p, alloc(8), [const(8)]),
               let(tmp(b), p, sub, [tmp(a), const(1)]),
               store(b, const(1), tmp(b))], ret).
heap_case([], [let(tmp(a), p, alloc(8), [const(2147483648)])], ret).

plain_unchanged :-
    M = module([func(f, export, l, [], [block(s, [], [
        let(tmp(a), l, alloc(8), [const(8)]),
        store(l, const(29), tmp(a)), let(tmp(r), l, load(l), [tmp(a)])
    ], ret(tmp(r)))])]),
    local_storage_module(M, N), N == M.

nonentry_unchanged :-
    M = module([func(f, export, void, [], [block(s, [], [], goto(b)),
        block(b, [], [let(tmp(a), p, alloc(8), [const(8)]),
                      store(b, const(1), tmp(a))], ret)])]),
    local_storage_module(M, N), N == M.

redefinition_unchanged :-
    remains_heap([], [let(tmp(a), p, alloc(8), [const(8)]),
                      let(tmp(a), p, copy, [const(0)]),
                      store(b, const(1), tmp(a))], ret).

dead_float_unchanged :-
    M = module([func(f, export, void, [], [
        block(s, [], [let(tmp(a), p, alloc(8), [const(1)]),
                      let(tmp(b), p, add, [tmp(a), const(1)])], ret),
        block(dead, [], [let(tmp(x), d, load(d), [tmp(b)])], ret)])]),
    local_storage_module(M, N), N == M.

% Exercise the public pipeline: promotion runs before local storage's
% unsupported-load guard. Each allocation is large enough that bounds
% alone cannot keep it on the heap. Fil-C zeroes new memory; the integer
% bit patterns below encode 1.0 in binary32 and binary64, not conversions.
float_heap_case(T, zero, module([func(f, export, T, [], [
    block(s, [], [let(tmp(a), p, alloc(8), [const(Size)]),
                  let(tmp(x), T, load(T), [tmp(a)])], ret(tmp(x)))
])]), ret(0)) :-
    float_layout(T, Size, _, _).
float_heap_case(T, pun, module([func(f, export, T, [], [
    block(s, [], [let(tmp(a), p, alloc(8), [const(Size)]),
                  store(W, const(Bits), tmp(a)),
                  let(tmp(x), T, load(T), [tmp(a)])], ret(tmp(x)))
])]), ret(Bits)) :-
    float_layout(T, Size, W, Bits).
% An unreachable load still uses the allocation, through a derived
% address. It must neither disappear from classification nor leave an
% undefined address behind when the entry allocation is optimized.
float_heap_case(T, dead, module([func(f, export, w, [], [
    block(s, [], [let(tmp(a), p, alloc(8), [const(16)]),
                  let(tmp(b), p, add, [tmp(a), const(8)])], ret(const(7))),
    block(dead, [], [let(tmp(x), T, load(T), [tmp(b)])], ret(const(7)))
])]), ret(7)) :-
    float_layout(T, _, _, _).

float_layout(s, 4, w, 1065353216).
float_layout(d, 8, l, 4607182418800017408).

optimized_float_heap(M0, Expected) :-
    valid_module(M0), once(run(M0, f, [], 100, Expected)),
    optimize(o0, M0, Unoptimized), Unoptimized == M0,
    optimize(o1, M0, M), valid_module(M), M == M0,
    once(run(M, f, [], 100, Expected)),
    pizlonate_module(M, Checked), valid_module(Checked),
    once(run(Checked, f, [], 100, Expected)).

storage_budget :-
    M = module([func(f, export, void, [], [block(s, [], [
        let(tmp(a), p, alloc(8), [const(2032)]),
        let(tmp(b), p, alloc(8), [const(1)])
    ], ret)])]),
    local_storage_module(M, module([func(f, export, void, [], [block(s, [], [
        local_alloc(a, 2032), let(tmp(b), p, alloc(8), [const(1)])
    ], ret)])])).

zero_size :-
    M = module([func(f, export, void, [], [block(s, [], [
        let(tmp(a), p, alloc(8), [const(0)])
    ], ret)])]),
    local_storage_module(M, module([func(f, export, void, [], [
        block(s, [], [local_alloc(a, 0)], ret)])])).

local_semantics :-
    overlap(F), semantics(F, [], ret(22068)),
    capability_contents(C), semantics(C, [], ret(37)),
    misaligned(P), semantics(P, [], trap(misaligned)),
    allocation_order(A), semantics(A, [], ret(64)).

% A local identity is allocated at the declaration, with the replaced
% allocation's rounded stride. Neither eager entry allocation nor an
% exact-sized reservation may change other pointers' integer values.
allocation_order(func(order, export, l, [], [block(s, [], [
    let(tmp(a), p, alloc(8), [const(8)]),
    let(tmp(local), p, alloc(8), [const(13)]),
    let(tmp(b), p, alloc(8), [const(8)]),
    let(tmp(i), l, ptoi, [tmp(a)]), let(tmp(j), l, ptoi, [tmp(b)]),
    let(tmp(v), l, sub, [tmp(j), tmp(i)])
], ret(tmp(v)))])).

% Overwriting address bytes does not clear the stored capability. The
% pointee escapes into the holder; only the holder is stack-local.
capability_contents(func(contents, export, l, [], [block(s, [], [
    let(tmp(a), p, alloc(8), [const(8)]),
    let(tmp(heap), p, alloc(8), [const(8)]),
    store(l, const(37), tmp(heap)), store(p, tmp(heap), tmp(a)),
    let(tmp(bits), l, ptoi, [tmp(heap)]), store(l, tmp(bits), tmp(a)),
    let(tmp(p), p, load(p), [tmp(a)]), let(tmp(r), l, load(l), [tmp(p)])
], ret(tmp(r)))])).

misaligned(func(misaligned, export, void, [], [block(s, [], [
    let(tmp(a), p, alloc(8), [const(9)]),
    let(tmp(b), p, add, [tmp(a), const(1)]), store(p, const(0), tmp(b))
], ret)])).

semantics(F, Args, Expected) :-
    M0 = module([F]), F = func(Name, _, _, _, _),
    valid_module(M0), once(run(M0, Name, Args, 100, Expected)),
    local_storage_module(M0, M), valid_module(M),
    once(run(M, Name, Args, 100, Expected)),
    pizlonate_module(M, Checked), valid_module(Checked),
    once(run(Checked, Name, Args, 100, Expected)).

local_lifetime :-
    read_ir_file('../tests/filc/local.ir', M, _), valid_module(M),
    pizlonate_module(M, Checked), valid_module(Checked),
    forall(member(Module, [M, Checked]), (
        module_prepared(Module, P),
        once(run_prepared(P, local_recursive, [3], 100, ret(6))),
        once(run_prepared(P, local_recursive, [5], 100, ret(15))),
        once(run_prepared(P, local_caller, [0], 100, ret(86))),
        once(run_prepared(P, local_caller, [1], 100, trap(out_of_bounds))),
        findall(N, (N in 0..3, run_prepared(P, local_recursive, [N], 100, ret(3)),
                    labeling([], [N])), Ns), Ns == [2]
    )).

local_validation :-
    forall(bad_locals(Bs),
           catch((valid_module(module([func(bad, local, void, [], Bs)])), fail),
                 nanofil_error(_), true)).

bad_locals([block(s, [], [local_load(tmp(v), l, l, missing, 0)], ret)]).
bad_locals([block(s, [], [local_alloc(x, 8), local_alloc(x, 16)], ret)]).
bad_locals([block(s, [], [local_load(tmp(v), l, l, x, 0), local_alloc(x, 8)], ret)]).
bad_locals([block(s, [], [], goto(b)), block(b, [], [local_alloc(x, 8)], ret)]).
bad_locals([block(s, [], [local_alloc(x, 8),
    let(tmp(j), w, setjmp('_setjmp'), [const(0), const(0)])], ret)]).
% A list correct for the other storage kind must not authorize access.
bad_locals([block(s, [], [local_alloc(x, 8),
    let(tmp(q), a, check_local(x, 0, 8, read, 8), []),
    let(tmp(p), p, raw_load_pointer(0, [aux_read, lower_resolve, address_read]), [tmp(q)])
], ret)]).
bad_locals([block(s, [], [let(tmp(x), p, alloc(8), [const(8)]),
    let(tmp(q), a, check(0, 8, write, 8), [tmp(x)]),
    raw_store_pointer(0, const(0), tmp(q), [lower_write, address_write])
], ret)]).
bad_locals([block(s, [], [local_alloc(x, 16),
    let(tmp(q), a, check_local(x, 0, 16, read, 1), []),
    let(tmp(v), l, raw_load(l, 1), [tmp(q)])
], ret)]).
