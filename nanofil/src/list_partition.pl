/* Stable list partitioning shared by promotion and register selection.
   Trealla's library(lists) supplies include/3 and exclude/3, but not
   SWI's partition/4. Evaluate the predicate only once per element. */
:- module(list_partition, [partition/4]).
:- meta_predicate partition(1, ?, ?, ?).

%! partition(:Predicate, +List, -Included, -Excluded) is det.
%
%  Included and Excluded retain List's order. Each element goes into
%  Included if Predicate succeeds once, and into Excluded otherwise.
partition(_, [], [], []).
partition(P, [X|Xs], In, Out) :-
    (   call(P, X) -> In = [X|Ins], Out = Outs
    ;   In = Ins, Out = [X|Outs]
    ),
    partition(P, Xs, Ins, Outs).
