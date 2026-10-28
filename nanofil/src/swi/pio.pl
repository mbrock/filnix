% library(pio)'s phrase_from_file/2 over characters, as in Trealla;
% SWI's own version gives codes.
:- module(pio, [phrase_from_file/2, phrase_from_file/3]).
:- meta_predicate phrase_from_file(//, +), phrase_from_file(//, +, +).

phrase_from_file(G, F) :-
    read_file_to_string(F, S, []),
    string_chars(S, Cs),
    phrase(G, Cs).

% phrase_from_file(G, F, [type(binary)]) reads F's bytes, each as the
% character of that code, as Trealla's does.
phrase_from_file(G, F, Options) :-
    (   memberchk(type(binary), Options) -> Encoding = octet ; Encoding = utf8 ),
    read_file_to_string(F, S, [encoding(Encoding)]),
    string_chars(S, Cs),
    phrase(G, Cs).
