(* CLI driver for the extracted Gallina C frontend (CLex.v + CParse.v + CCanon.v).
   Canonical Prolog term serialization lives in CCanon.v so OCaml and λANF builds
   share one printer. *)

open Nanofil_frontend

let read_file_bytes path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic) @@ fun () ->
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  let rec to_list i acc =
    if i < 0 then acc else to_list (i - 1) (s.[i] :: acc)
  in
  to_list (n - 1) []

let write_canon_list emit_elem xs =
  match xs with
  | [] -> output_string stdout "[].\n"
  | _ ->
      let rec go first = function
        | [] -> output_string stdout "].\n"
        | x :: rest ->
            let a0 = if first then [ "[" ] else [ "," ] in
            List.iter (output_string stdout) (List.rev (emit_elem x a0));
            go false rest
      in
      go true xs

let lex_file ~c23 file =
  let cs = read_file_bytes file in
  match lex_chars file cs with
  | COk ts -> COk (if c23 then c23_tokens ts else ts)
  | CErr m -> CErr m

let () =
  let c23 = ref false in
  let pos = ref [] in
  for i = 1 to Array.length Sys.argv - 1 do
    if Sys.argv.(i) = "--c23" then c23 := true
    else pos := Sys.argv.(i) :: !pos
  done;
  match List.rev !pos with
  | [ "lex"; file ] -> (
      match lex_file ~c23:!c23 file with
      | COk ts -> write_canon_list emit_token ts
      | CErr m ->
          Printf.eprintf "lex error: %s\n" m;
          exit 1)
  | [ "parse"; file ] -> (
      match lex_file ~c23:!c23 file with
      | CErr m ->
          Printf.eprintf "lex error: %s\n" m;
          exit 1
      | COk ts -> (
          match c_parse ts with
          | COk items -> write_canon_list emit_item items
          | CErr m ->
              Printf.eprintf "parse error: %s\n" m;
              exit 1))
  | "bench" :: files when files <> [] ->
      let t0 = Unix.gettimeofday () in
      let ok = ref 0 in
      let err = ref 0 in
      let total_toks = ref 0 in
      let total_items = ref 0 in
      List.iter
        (fun file ->
          match lex_file ~c23:!c23 file with
          | CErr _ -> incr err
          | COk ts -> (
              total_toks := !total_toks + List.length ts;
              match c_parse ts with
              | COk items ->
                  incr ok;
                  total_items := !total_items + List.length items
              | CErr _ -> incr err))
        files;
      let dt = (Unix.gettimeofday () -. t0) *. 1000.0 in
      Printf.printf
        "Gallina-OCaml frontend: %d ok, %d err | %d tokens, %d items | %.1f ms\n"
        !ok !err !total_toks !total_items dt
  | _ ->
      prerr_endline
        "usage: nanofil-frontend [--c23] (lex FILE | parse FILE | bench FILE...)";
      exit 2
