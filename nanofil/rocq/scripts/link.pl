% Several checked modules linked into one, for a proof about a whole
% program (docs/formal.md's Campaign 7, GNU Hello). Reads OBJECT=FILE
% arguments, each FILE a checked module term (`module(Items).`, as
% nanofil's CC wrapper keeps it), and prints one `module(Items).` on
% stdout: the items a run from ENTRY can name, with every name a
% linker keeps apart made distinct. rocq/scripts/gallina.pl then prints it as
% Gallina.
%
%   swipl rocq/scripts/link.pl main hello=src/hello.o.term closeout=... >linked.term
%   swipl rocq/scripts/link.pl --ctors main hello=... --archive malloc=... >linked.term
%
% What it does, as a linker would:
%
% | Step | Meaning |
% | --- | --- |
% | `local` names | a function or data item with `local` or `ro(local)` linkage is its object's own: renamed `OBJECT#NAME`, with every `global(NAME)` and `sym(NAME, Off)` of that object |
% | other names | exported items are shared: one definition each, or the link fails |
% | kept items | the items reachable from ENTRY through `global/1` and `sym/2`, the only ways a run names an item; the rest cannot run or be read, so they are left out |
% | aliases | `alias(Name, Linkage, Target)` defines Name as Target, as glibc's `weak_alias (__strlen, strlen)`; reaching Name reaches Target |
% | weak names | a weak declaration (`extern(weak)` data) gives way to any definition, and a weak function, data object or alias to a non-weak definition of the same name in another object; aliases resolve the winning target by name, as filcc's alias getter jumps to the target getter through the PLT (unlike an ordinary ELF alias, it does not retain an overridden weak body) |
% | archive members | each `--archive OBJECT=FILE` is demand-extracted at a fixed point: a reference in an included object (or ENTRY) must need a definition it supplies; declarations cannot satisfy demand; all ordinary objects are included before extraction |
% | external names | a name no object defines is libc's, resolved by the contract registry |
% | `init` items | a constructor or destructor entry (`init(ctor, P)`, `init(dtor, P)` data) is refused by default; `--ctors` keeps it and roots its target, but does not itself run startup or exit: their effects remain proof obligations |
%
% Items keep their objects' order, ordinary objects the order given,
% extracted members their extraction order. Context items are dropped unless
% --context retains the records belonging to each surviving function.

:- initialization(main, main).

main :-
    set_stream(user_output, encoding(utf8)),
    current_prolog_flag(argv, Args0),
    ( select('--context', Args0, Args1) -> Context = true ; Args1 = Args0, Context = false ),
    ( select('--ctors', Args1, Args) -> Ctors = true ; Args = Args1, Ctors = false ),
    Args = [Entry|Specs],
    objects(Specs, Objects0, Archive),
    extract(Entry, Objects0, Archive, Objects),
    maplist(check_ctors(Ctors), Objects),
    findall(I, (member(object(_, Is), Objects), member(I, Is), \+ is_context(I)), Items00),
    exclude(overridden(Items00), Items00, Items0),
    exported_unique(Items0),
    findall(N, member(data(N, init(_, _), _, _), Items0), InitNames),
    reachable([Entry|InitNames], Items0, [], Names),
    findall(I, (member(object(_, Is), Objects), member(I, Is),
                linked_item(Context, Names, Items0, Is, I)), Items),
    print_module(Items).

objects([], [], []).
objects(['--archive', Spec|Specs], Objects, [O|Archive]) :- !,
    object(Spec, O), objects(Specs, Objects, Archive).
objects([Spec|Specs], [O|Objects], Archive) :-
    object(Spec, O), objects(Specs, Objects, Archive).

% object(+Spec, -Object): OBJECT=FILE's items, its locals renamed.
object(Spec, object(Obj, Items)) :-
    atomic_list_concat([Obj, File], '=', Spec),
    read_file_to_terms(File, [module(Items0)], [encoding(utf8)]),
    convlist(local_name, Items0, Locals),
    maplist(rename(Obj, Locals), Items0, Items).

check_ctors(true, _) :- !.
check_ctors(false, object(Obj, Items0)) :-
    forall(member(data(N, init(K, P), _, _), Items0),
           ( format(user_error,
                    "link.pl: ~w's ~q is a ~w entry (init(~w, ~w)), which the linked module does not run~n",
                    [Obj, N, K, K, P]),
             halt(1) )).

% Pull one member at a time, then recompute demand, including references
% introduced by that member. A declaration never counts as a definition.
extract(_, Objects, [], Objects) :- !.
extract(Entry, Objects0, Archive0, Objects) :-
    findall(I, (member(object(_, Is), Objects0), member(I, Is)), Items),
    findall(N, ( ( N = Entry ; member(I, Items), sub_name(I, N) ),
                 \+ (member(D, Items), item_name(D, N), \+ declaration(D)) ), Ns0),
    sort(Ns0, Ns),
    (   select(O, Archive0, Archive), O = object(_, Is),
        member(D, Is), \+ declaration(D), item_name(D, N), memberchk(N, Ns)
    ->  append(Objects0, [O], Objects1), extract(Entry, Objects1, Archive, Objects)
    ;   Objects = Objects0
    ).

is_context(context(_, _)).

local_name(func(N, local, _, _, _), N).
local_name(data(N, local, _, _), N).
local_name(data(N, ro(local), _, _), N).
local_name(alias(N, local, _), N).

% rename(+Obj, +Locals, +T0, -T): T0 with each local name of Obj, as an
% item's name or in global/1 or sym/2, made Obj#Name.
rename(Obj, Locals, func(N0, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    local(Obj, Locals, N0, N), refs(Obj, Locals, Bs0, Bs).
rename(Obj, Locals, data(N0, L, A, Is0), data(N, L, A, Is)) :- !,
    local(Obj, Locals, N0, N), refs(Obj, Locals, Is0, Is).
rename(Obj, Locals, alias(N0, L, T0), alias(N, L, T)) :- !,
    local(Obj, Locals, N0, N), local(Obj, Locals, T0, T).
rename(Obj, Locals, context(N0, Rs), context(N, Rs)) :- !,
    local(Obj, Locals, N0, N).
rename(_, _, I, I).

local(Obj, Locals, N0, N) :-
    (   memberchk(N0, Locals) -> atomic_list_concat([Obj, '#', N0], N) ; N = N0 ).

refs(Obj, Locals, global(N0), global(N)) :- !, local(Obj, Locals, N0, N).
refs(Obj, Locals, sym(N0, Off), sym(N, Off)) :- !, local(Obj, Locals, N0, N).
refs(Obj, Locals, T0, T) :-
    compound(T0), !,
    T0 =.. [F|As0], maplist(refs(Obj, Locals), As0, As), T =.. [F|As].
refs(_, _, T, T).

item_name(func(N, _, _, _, _), N).
item_name(data(N, _, _, _), N).
item_name(alias(N, _, _), N).

% overridden(+Items, +I): the linker keeps another item of I's name.
% A weak declaration (`#pragma weak` without a definition, which
% nanofil prints as extern(weak) data) gives way to any definition; a
% weak definition gives way to a non-weak one.
overridden(Items, I) :-
    item_name(I, N), declaration(I),
    member(J, Items), J \== I, item_name(J, N), \+ declaration(J), !.
overridden(Items, I) :-
    item_name(I, N), weak(I),
    member(J, Items), J \== I, item_name(J, N), \+ weak(J), \+ declaration(J), !.

declaration(data(_, extern(weak), _, _)).

weak(func(_, weak, _, _, _)).
weak(alias(_, weak, _)).
weak(data(_, weak, _, _)).
weak(data(_, ro(weak), _, _)).

exported_unique(Items) :-
    maplist(item_name, Items, Ns), msort(Ns, Sorted),
    (   append(_, [N, N|_], Sorted)
    ->  format(user_error, "link.pl: ~q is defined twice~n", [N]), halt(1)
    ;   true
    ).

% reachable(+Todo, +Items, +Seen, -Names): the names of Items reachable
% from Todo.
reachable([], _, Seen, Seen).
reachable([N|Todo], Items, Seen, Names) :-
    (   memberchk(N, Seen) -> reachable(Todo, Items, Seen, Names)
    ;   (   member(I, Items), item_name(I, N)
        ->  named(I, Ns), append(Ns, Todo, Todo1)
        ;   Todo1 = Todo        % external
        ),
        reachable(Todo1, Items, [N|Seen], Names)
    ).

named(I, Ns) :- findall(N, sub_name(I, N), Ns).

sub_name(alias(_, _, T), T) :- !.
sub_name(context(_, _), _) :- !, fail.
sub_name(global(N), N).
sub_name(sym(N, _), N).
sub_name(T, N) :- compound(T), T \= global(_), T \= sym(_, _), arg(_, T, A), sub_name(A, N).

kept(Names, I) :- item_name(I, N), memberchk(N, Names).

linked_item(true, Names, Winners, Object, context(N, _)) :- !,
    member(F, Object), F = func(N, _, _, _, _),
    memberchk(F, Winners), memberchk(N, Names).
linked_item(_, Names, Winners, _, I) :-
    \+ is_context(I), memberchk(I, Winners), kept(Names, I).

print_module(Items) :-
    format("module(["),
    print_items(Items),
    format("]).~n").

print_items([]).
print_items([I|Is]) :-
    write_canonical(I), ( Is == [] -> true ; format(",~n") ), print_items(Is).
