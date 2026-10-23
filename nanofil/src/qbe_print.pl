/*  Printer from IR terms to QBE text. Every block ends in an explicit
    jump, so printing is independent of block order.
*/
:- module(qbe_print, [module_chars//1, print_module/1]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).

print_module(M) :-
    phrase(module_chars(M), Cs),
    format("~s", [Cs]).

module_chars(module(Items)) --> items(Items).

items([]) --> [].
items([I|Is]) --> item(I), "\n", items(Is).

item(func(Name, Lk, Ret, Params, Blocks)) -->
    linkage(Lk), "function ", ret(Ret), "$", atom(Name), "(", params(Params), ") {\n",
    blocks(Blocks), "}\n".
item(data(Name, Lk, Align, Items)) -->
    linkage(Lk), "data $", atom(Name), " = align ", num(Align), " { ",
    data_items(Items), " }\n".

linkage(export) --> "export ".
linkage(local) --> [].
linkage(ro(Lk)) --> linkage(Lk), "section \".rodata\" ".

ret(void) --> [].
ret(K) --> atom(K), " ".

params([]) --> [].
params([P]) --> !, param(P).
params([P|Ps]) --> param(P), ", ", params(Ps).
param(par(K, V)) --> atom(K), " ", val(V).

blocks([]) --> [].
blocks([blk(L, Phis, Insts, J)|Bs]) -->
    "@", atom(L), "\n", phis(Phis), insts(Insts), "\t", jump(J), "\n", blocks(Bs).

phis([]) --> [].
phis([phi(D, K, Args)|Ps]) -->
    "\t", val(D), " =", atom(K), " phi ", phi_args(Args), "\n", phis(Ps).
phi_args([L-V]) --> !, "@", atom(L), " ", val(V).
phi_args([L-V|As]) --> "@", atom(L), " ", val(V), ", ", phi_args(As).

insts([]) --> [].
insts([I|Is]) --> "\t", inst(I), "\n", insts(Is).

inst(ins(D, K, Op, Args)) --> val(D), " =", atom(K), " ", opname(Op), " ", vals(Args).
inst(store(W, V, A)) --> "store", atom(W), " ", val(V), ", ", val(A).
inst(call(void, F, Args)) --> "call ", val(F), "(", call_args(Args), ")".
inst(call(to(D, K), F, Args)) --> val(D), " =", atom(K), " call ", val(F), "(", call_args(Args), ")".

call_args([]) --> [].
call_args([A]) --> !, call_arg(A).
call_args([A|As]) --> call_arg(A), ", ", call_args(As).
call_arg(arg(K, V)) --> atom(K), " ", val(V).

opname(cmp(C, K)) --> !, "c", atom(C), atom(K).
opname(ext(T)) --> !, "ext", atom(T).
opname(load(T)) --> !, "load", atom(T).
opname(alloc(N)) --> !, "alloc", num(N).
opname(Op) --> atom(Op).

jump(jmp(L)) --> "jmp @", atom(L).
jump(jnz(V, L1, L2)) --> "jnz ", val(V), ", @", atom(L1), ", @", atom(L2).
jump(ret(V)) --> "ret ", val(V).
jump(ret) --> "ret".
jump(hlt) --> "hlt".

vals([V]) --> !, val(V).
vals([V|Vs]) --> val(V), ", ", vals(Vs).

val(t(N)) --> "%", atom(N).
val(c(N)) --> num(N).
val(glo(N)) --> "$", atom(N).

data_items([I]) --> !, data_item(I).
data_items([I|Is]) --> data_item(I), ", ", data_items(Is).

data_item(zero(N)) --> "z ", num(N).
data_item(item(W, c(N))) --> atom(W), " ", num(N).
data_item(item(b, str(Cs))) --> "b \"", seq(Cs), "\"".
data_item(item(W, sym(S, 0))) --> !, atom(W), " $", atom(S).
data_item(item(W, sym(S, Off))) --> atom(W), " $", atom(S), " + ", num(Off).

atom(A) --> { atom_chars(A, Cs) }, seq(Cs).
num(N) --> { number_chars(N, Cs) }, seq(Cs).
