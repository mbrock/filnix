:- encoding(utf8).
/*  c_batch: render a deduplicated batch of C snippets through c_draw.pl.

    The OCaml dterm-rocq renderer collects every unique ```c fence, `c: ...`
    inline snippet, and unmarked C-looking inline span across a site build
    and passes them here in one shot. Loading nanofil's C frontend once
    gives Rocq pages full c_draw highlighting without duplicating the C
    parser in OCaml.

    Usage: swipl -q nanofil/web/c/c_batch.pl C_SRC_DIR PLAY_ROOT IN OUT

    Each line of IN is `F <b64>`, `I <b64>`, or `A <b64>` (fence, inline
    c:, or auto-detected inline C, UTF-8 encoded in base64). Each line of
    OUT is `OK <b64>` with the rendered HTML or `NO` when c_draw declines.
*/
:- module(c_batch, []).

:- use_module(library(base64)).
:- use_module(library(readutil)).
:- use_module(c_draw).

:- initialization(main, main).

main :-
    current_prolog_flag(argv, [SrcDir, PlayRoot, InPath, OutPath]),
    nb_setval(c_src_dir, SrcDir),
    nb_setval(c_play_root, PlayRoot),
    (   c_draw:c_ready -> true
    ;   format(user_error, "c_batch: cannot load C frontend from ~w~n", [SrcDir]),
        halt(1)
    ),
    setup_call_cleanup(
        open(InPath, read, In, [encoding(utf8)]),
        setup_call_cleanup(
            open(OutPath, write, Out, [encoding(utf8)]),
            process_stream(In, Out),
            close(Out)
        ),
        close(In)
    ).

process_stream(In, Out) :-
    read_line_to_string(In, Line),
    (   Line == end_of_file -> true
    ;   Line == "" -> process_stream(In, Out)
    ;   process_line(Line, Out),
        process_stream(In, Out)
    ).

process_line(Line, Out) :-
    (   sub_string(Line, 0, 2, _, KindSp),
        sub_string(Line, 2, _, 0, B64In),
        base64_encoded(Text, B64In, [encoding(utf8)]),
        render_item(KindSp, Text, Html)
    ->  base64_encoded(Html, B64Out, [encoding(utf8)]),
        format(Out, "OK ~w~n", [B64Out])
    ;   format(Out, "NO~n", [])
    ).

render_item("F ", Text, Html) :-
    split_string(Text, "\n", "", Lines),
    flag(c_fence, _, 0),
    catch(once(phrase(c_draw:c_fence(Lines), Cs)), _, fail),
    string_codes(Html, Cs).
render_item("I ", Text, Html) :-
    string_codes(Text, Codes),
    catch(once(phrase(c_draw:c_inline(Codes), Cs)), _, fail),
    string_codes(Html, Cs).
render_item("A ", Text, Html) :-
    string_codes(Text, Codes),
    catch(once(phrase(c_draw:c_inline_auto(Codes), Cs)), _, fail),
    string_codes(Html, Cs).
