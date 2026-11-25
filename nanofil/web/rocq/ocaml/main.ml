(* CLI for pure-OCaml Rocq parsing, strict reprinting, and full HTML page
   rendering (drop-in pure-OCaml dterm-rocq). *)

open Ast

let count_items items =
  let sents = ref 0 and steps = ref 0 in
  let rec go = function
    | IBlock (_, body, e) ->
        incr sents;
        List.iter go body;
        if e <> None then incr sents
    | IProved (_, pf) ->
        incr sents;
        steps := !steps + List.length pf.pf_steps
    | ISent _ -> incr sents
  in
  List.iter go items;
  (!sents, !steps)

let run_batch ~strict ~reprint_all ~jobs files =
  let t0 = Unix.gettimeofday () in
  let total_files = Array.length files in
  let process_slice lo hi =
    let cache = Hashtbl.create 64 in
    let ok = ref 0 and fail = ref 0 and sents = ref 0 and steps = ref 0 and raw_bad = ref 0 in
    let errs = ref [] in
    for i = lo to hi - 1 do
      let f = files.(i) in
      match Parse_vernac.parse_file ~cache f with
      | exception Lexer.Lex_error off ->
          incr fail;
          errs := Printf.sprintf "LEX FAIL %s @ byte %d" f off :: !errs
      | pf ->
          let ns, nt = count_items pf.items in
          sents := !sents + ns;
          steps := !steps + nt;
          let raws = Reprint.collect_raws [] pf.items in
          raw_bad := !raw_bad + List.length raws;
          if reprint_all then (
            match Reprint.reprint ~strict ~file:f pf with
            | Ok _ -> incr ok
            | Error msg ->
                incr fail;
                errs := msg :: !errs)
          else if strict && raws <> [] then (
            incr fail;
            List.iter
              (fun ((sp : span), kw) ->
                errs :=
                  Printf.sprintf "%s:%d: unparsed %s" f
                    (Reprint.line_of_offset pf.text sp.lo) kw
                  :: !errs)
              raws)
          else incr ok
    done;
    (!ok, !fail, !sents, !steps, !raw_bad, List.rev !errs)
  in
  let results =
    if jobs <= 1 || total_files < jobs then [ process_slice 0 total_files ]
    else
      let domains =
        List.init jobs (fun j ->
            let lo = j * total_files / jobs in
            let hi = (j + 1) * total_files / jobs in
            Domain.spawn (fun () -> process_slice lo hi))
      in
      List.map Domain.join domains
  in
  let dt = (Unix.gettimeofday () -. t0) *. 1000.0 in
  let ok, fail, sents, steps, raw_bad, errs =
    List.fold_left
      (fun (a, b, c, d, e, es) (a', b', c', d', e', es') ->
        (a + a', b + b', c + c', d + d', e + e', es @ es'))
      (0, 0, 0, 0, 0, []) results
  in
  List.iter prerr_endline errs;
  Printf.printf
    "OCaml (%d domain%s%s): %d/%d ok (fail=%d raw=%d) | %d vernac, %d proof steps | %.1f ms (%.3f ms/file)\n"
    jobs
    (if jobs = 1 then "" else "s")
    (if reprint_all then ", +tactics+reprint" else "")
    ok total_files fail raw_bad sents steps dt
    (if total_files = 0 then 0.0 else dt /. float_of_int total_files);
  if fail > 0 then exit 1

let default_jobs () =
  match Sys.getenv_opt "NIX_BUILD_CORES" with
  | Some s -> (
      match int_of_string_opt s with
      | Some n when n > 0 -> min 16 n
      | _ -> min 8 (Domain.recommended_domain_count ()))
  | None -> min 8 (Domain.recommended_domain_count ())

let () =
  let mode = ref `Bench in
  let strict = ref false in
  let reprint_all = ref false in
  let no_index = ref false in
  let jobs = ref None in
  let render_out = ref "" in
  let render_root = ref "" in
  let prolog_dir = ref None in
  let concepts_dir = ref None in
  let c_batch = ref None in
  let swipl = ref "swipl" in
  let files = ref [] in
  let rec parse_args = function
    | [] -> ()
    | "--reprint" :: rest ->
        mode := `Reprint;
        parse_args rest
    | "--render" :: out :: root :: rest ->
        mode := `Render;
        render_out := out;
        render_root := root;
        parse_args rest
    | "--reprint-all" :: rest ->
        reprint_all := true;
        parse_args rest
    | "--strict" :: rest ->
        strict := true;
        parse_args rest
    | "--no-index" :: rest ->
        no_index := true;
        parse_args rest
    | "-j" :: n :: rest ->
        jobs := Some (max 1 (int_of_string n));
        parse_args rest
    | arg :: rest when String.starts_with ~prefix:"--prolog=" arg ->
        prolog_dir := Some (String.sub arg 9 (String.length arg - 9));
        parse_args rest
    | arg :: rest when String.starts_with ~prefix:"--concepts=" arg ->
        concepts_dir := Some (String.sub arg 11 (String.length arg - 11));
        parse_args rest
    | arg :: rest when String.starts_with ~prefix:"--c-batch=" arg ->
        c_batch := Some (String.sub arg 10 (String.length arg - 10));
        parse_args rest
    | arg :: rest when String.starts_with ~prefix:"--swipl=" arg ->
        swipl := String.sub arg 8 (String.length arg - 8);
        parse_args rest
    | f :: rest ->
        files := f :: !files;
        parse_args rest
  in
  parse_args (List.tl (Array.to_list Sys.argv));
  let files = List.rev !files in
  match (!mode, files) with
  | `Reprint, [ f ] -> (
      let pf = Parse_vernac.parse_file f in
      match Reprint.reprint ~strict:!strict ~file:f pf with
      | Ok out -> print_string out
      | Error msg ->
          prerr_endline msg;
          exit 1)
  | `Render, _ :: _ ->
      let jobs = Option.value ~default:(default_jobs ()) !jobs in
      Draw_page.render_site ~out:!render_out ~root:!render_root
        ~prolog_dir:!prolog_dir ~concepts_dir:!concepts_dir ~no_index:!no_index
        ~jobs ~c_batch:!c_batch ~swipl:!swipl files
  | `Bench, _ :: _ ->
      let jobs = Option.value ~default:1 !jobs in
      run_batch ~strict:!strict ~reprint_all:!reprint_all ~jobs (Array.of_list files)
  | _ ->
      prerr_endline
        "usage:\n\
        \  dterm-rocq --reprint [--strict] FILE.v\n\
        \  dterm-rocq --render OUT ROOT [--prolog=DIR] [--concepts=DIR] [--c-batch=PL] [--swipl=BIN] [--no-index] [-j N] FILE.v...\n\
        \  dterm-rocq [--strict] [--reprint-all] [-j N] FILE.v...";
      exit 2
