% library(pio)'s phrase_from_file/2 over characters, as in Trealla;
% SWI's own version gives codes.
:- module(pio, [phrase_from_file/2]).
:- meta_predicate phrase_from_file(//, +).

phrase_from_file(G, F) :-
    read_file_to_string(F, S, []),
    string_chars(S, Cs),
    phrase(G, Cs).
