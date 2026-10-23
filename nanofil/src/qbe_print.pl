/*  Printer from IR terms to QBE text. Every block ends in an explicit
    jump, so printing is independent of block order.
*/
:- module(qbe_print, [module_chars//1, print_module/1]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(ir, [op_text//1, op_arg_classes/4]).
:- use_module(ieee, [ieee_decimal/3]).

%! print_module(+Module)
%
%  Print the QBE text of Module on the current output.
print_module(Module) :-
    phrase(module_chars(Module), Cs),
    format("~s", [Cs]).

%! module_chars(+Module)//
%
%  The QBE text of Module, one blank line after each item.
module_chars(module(Items)) --> items(Items).

items([]) --> [].
items([Item|Items]) --> item(Item), "\n", items(Items).

% item(+Item)//: the text of a function or data definition.
item(func(Name, Linkage, Ret, Params, Blocks)) -->
    linkage(Linkage),
    "function ", ret_class(Ret), "$", atom(Name),
    "(", params(Params), ") {\n",
    blocks(Blocks, Ret),
    "}\n".
item(data(Name, Linkage, Align, Items)) -->
    linkage(Linkage),
    "data $", atom(Name), " = align ", num(Align),
    " { ", data_items(Items), " }\n".

% linkage(+Linkage)//: the keywords before "function" or "data".
linkage(export) --> "export ".
linkage(local) --> [].
linkage(ro(Linkage)) --> linkage(Linkage), "section \".rodata\" ".

% ret_class(+Ret)//: a function's return class and a space, or nothing
% for void. One clause per Ret of ir.pl, so a void function has one text.
ret_class(void) --> [].
ret_class(tuple(Ks)) --> "{", comma_separated(Ks, atom), "} ".
ret_class(w) --> "w ".
ret_class(l) --> "l ".
ret_class(p) --> "p ".
ret_class(s) --> "s ".
ret_class(d) --> "d ".

params([]) --> [].
params([Param|Params]) --> param(Param), more_params(Params).

% more_params(+Params)//: each of Params after ", ".
more_params([]) --> [].
more_params([Param|Params]) --> ", ", param(Param), more_params(Params).

param(par(K, V)) --> atom(K), " ", val(V).

blocks([], _) --> [].
blocks([blk(Label, Phis, Insts, Jump)|Blocks], Ret) -->
    "@", atom(Label), "\n",
    phis(Phis),
    insts(Insts),
    "\t", typed_jump(Ret, Jump), "\n",
    blocks(Blocks, Ret).

phis([]) --> [].
phis([phi(D, K, Incoming)|Phis]) -->
    "\t", val(D), " =", atom(K), " phi ", phi_args(Incoming, K), "\n",
    phis(Phis).

% phi_args(+Incoming)//: the nonempty "@label value" list of a phi.
phi_args([Label-V|Incoming], K) -->
    phi_arg(Label-V, K),
    more_phi_args(Incoming, K).

% more_phi_args(+Incoming)//: each of Incoming after ", ".
more_phi_args([], _) --> [].
more_phi_args([Label-V|Incoming], K) -->
    ", ", phi_arg(Label-V, K),
    more_phi_args(Incoming, K).

phi_arg(Label-V, K) --> "@", atom(Label), " ", typed_val(K, V).

insts([]) --> [].
insts([Inst|Insts]) --> "\t", inst(Inst), "\n", insts(Insts).

% inst(+Inst)//: an instruction, without its tab and newline.
inst(ins(D, K, Op, Args)) -->
    % Only float vs nonfloat matters here; filc includes pointer-only ops.
    { op_arg_classes(Op, K, filc, Ks) },
    val(D), " =", atom(K), " ", op_text(Op), " ", typed_vals(Ks, Args).
inst(store(W, V, Addr)) -->
    "store", atom(W), " ", typed_val(W, V), ", ", val(Addr).
inst(call(Res, F, Args)) --> call_inst(Res, F, Args).

% call_inst(+Res, +F, +Args)//: a call of F on Args with result Res.
call_inst(void, F, Args) --> "call ", val(F), "(", call_args(Args), ")".
call_inst(tuple(Tos), F, Args) -->
    { findall(D, member(to(D, _), Tos), Ds),
      findall(K, member(to(_, K), Tos), Ks) },
    "{", comma_separated(Ds, val), "} ={", comma_separated(Ks, atom), "}",
    " call ", val(F), "(", call_args(Args), ")".
call_inst(to(D, K), F, Args) -->
    val(D), " =", atom(K), " call ", val(F), "(", call_args(Args), ")".

call_args([]) --> [].
call_args([Arg|Args]) --> call_arg(Arg), more_call_args(Args).

% more_call_args(+Args)//: each of Args after ", ".
more_call_args([]) --> [].
more_call_args([Arg|Args]) --> ", ", call_arg(Arg), more_call_args(Args).

call_arg(arg(K, V)) --> atom(K), " ", typed_val(K, V).

typed_jump(K, ret(V)) --> !, "ret ", typed_val(K, V).
typed_jump(_, J) --> jump(J).

% jump(+Jump)//: a jump, without its tab and newline.
jump(jmp(Label)) --> "jmp @", atom(Label).
jump(jnz(V, IfTrue, IfFalse)) -->
    "jnz ", val(V), ", @", atom(IfTrue), ", @", atom(IfFalse).
jump(ret(V)) --> "ret ", val(V).
jump(rets(Vs)) --> "ret {", comma_separated(Vs, val), "}".
jump(ret) --> "ret".
jump(hlt) --> "hlt".

% val(+V)//: a temporary, constant or global operand.
val(t(N)) --> "%", atom(N).
val(c(N)) --> num(N).
val(glo(N)) --> "$", atom(N).

typed_vals([K|Ks], [V|Vs]) --> typed_val(K, V), more_typed_vals(Ks, Vs).
more_typed_vals([], []) --> [].
more_typed_vals([K|Ks], [V|Vs]) -->
    ", ", typed_val(K, V), more_typed_vals(Ks, Vs).

% Raw integer constants in QBE are bit patterns even at float classes.
% Use those for NaNs/infinities/-0 so payloads and signs survive exactly.
typed_val(K, c(N)) -->
    { memberchk(K, [s, d]) }, !,
    ( { ( K == s -> Sign = 2147483648 ; Sign = 9223372036854775808 ),
        N =\= Sign, ieee_decimal(K, N, Cs) }
    -> atom(K), "_", seq(Cs)
    ; num(N) ).
typed_val(_, V) --> val(V).

% data_items(+Items)//: the nonempty comma-separated data items.
data_items([Item|Items]) --> data_item(Item), more_data_items(Items).

% more_data_items(+Items)//: each of Items after ", ".
more_data_items([]) --> [].
more_data_items([Item|Items]) -->
    ", ", data_item(Item),
    more_data_items(Items).

data_item(zero(N)) --> "z ", num(N).
data_item(item(W, Value)) --> item_value(Value, W).

% item_value(+Value, +W)//: a data item of width W and value Value.
item_value(c(N), W) --> atom(W), " ", typed_val(W, c(N)).
item_value(str(Cs), b) --> "b \"", seq(Cs), "\"".
item_value(sym(S, Off), W) --> atom(W), " $", atom(S), sym_offset(Off).

% sym_offset(+Off)//: " + Off", or nothing for offset 0.
sym_offset(Off) --> ( { Off == 0 } -> [] ; " + ", num(Off) ).

% comma_separated(+Xs, :Print_3)//: Print_3 of each of the nonempty Xs,
% separated by ", ".
comma_separated([X|Xs], Print_3) -->
    call(Print_3, X),
    more_comma_separated(Xs, Print_3).

more_comma_separated([], _) --> [].
more_comma_separated([X|Xs], Print_3) -->
    ", ", call(Print_3, X),
    more_comma_separated(Xs, Print_3).

% atom(+A)//, num(+N)//: the characters of an atom or number.
atom(A) --> { atom_chars(A, Cs) }, seq(Cs).
num(N) --> { number_chars(N, Cs) }, seq(Cs).
