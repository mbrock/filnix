% library(format) as in Trealla and Scryer: format_//2. format/2,3
% with chars(Cs) are built in.
:- module(format, [format_//2]).
:- use_module(dcgs).

format_(F, As) --> { format(chars(Cs), F, As) }, seq(Cs).
