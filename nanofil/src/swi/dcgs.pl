% library(dcgs) as in Trealla and Scryer: seq//1, seqq//1 and ... //0.
:- module(dcgs, [seq//1, seqq//1, ... //0]).

seq([]) --> [].
seq([E|Es]) --> [E], seq(Es).

seqq([]) --> [].
seqq([Es|Ess]) --> seq(Es), seqq(Ess).

... --> [] | [_], ... .
