(* CLI driver for the extracted Gallina C frontend (CLex, CParse, CCanon, CPp,
   CIeee, CTypes). Canonical Prolog term serialization lives in CCanon.v and
   CTypeCanon.v so OCaml and λANF builds share one printer. *)

open Nanofil_frontend

let string_to_char_list s =
  let n = String.length s in
  let rec go i acc = if i < 0 then acc else go (i - 1) (s.[i] :: acc) in
  go (n - 1) []

let read_file_bytes path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic) @@ fun () ->
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  string_to_char_list s

let read_file_bytes_opt path =
  try Some (read_file_bytes path) with Sys_error _ | Unix.Unix_error _ -> None

let file_exists_regular path =
  try (Unix.stat path).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error _ -> false

let realpath_safe path =
  try Unix.realpath path with Unix.Unix_error _ -> path

let drain_fd fd =
  let buf = Buffer.create 4096 in
  let tmp = Bytes.create 4096 in
  let rec loop () =
    match Unix.read fd tmp 0 4096 with
    | 0 -> Buffer.contents buf
    | n ->
        Buffer.add_subbytes buf tmp 0 n;
        loop ()
  in
  loop ()

let run_cmd_capture ?(stdin_data = None) ~capture_stderr prog args =
  let argv = Array.of_list (prog :: args) in
  let devnull_r = Unix.openfile "/dev/null" [ Unix.O_RDONLY ] 0 in
  let devnull_w = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0 in
  let in_r, in_w =
    match stdin_data with
    | None -> (devnull_r, None)
    | Some _ ->
        let r, w = Unix.pipe () in
        Unix.set_close_on_exec w;
        (r, Some w)
  in
  let out_r, out_w = Unix.pipe () in
  Unix.set_close_on_exec out_r;
  let stdout_fd, stderr_fd =
    if capture_stderr then (devnull_w, out_w) else (out_w, devnull_w)
  in
  let pid = Unix.create_process prog argv in_r stdout_fd stderr_fd in
  Unix.close devnull_r;
  Unix.close devnull_w;
  if in_r <> devnull_r then Unix.close in_r;
  Unix.close out_w;
  (match (stdin_data, in_w) with
  | Some data, Some w ->
      let len = String.length data in
      let rec write_all off =
        if off < len then
          let n = Unix.write_substring w data off (len - off) in
          write_all (off + n)
      in
      write_all 0;
      Unix.close w
  | _ -> ());
  let output = drain_fd out_r in
  Unix.close out_r;
  let _, status = Unix.waitpid [] pid in
  match status with
  | Unix.WEXITED 0 -> output
  | Unix.WEXITED code ->
      failwith (Printf.sprintf "%s exited with status %d" prog code)
  | _ -> failwith (Printf.sprintf "%s terminated abnormally" prog)

let split_ws s =
  let n = String.length s in
  let is_ws = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false in
  let rec go i acc =
    if i >= n then List.rev acc
    else if is_ws s.[i] then go (i + 1) acc
    else
      let j = ref i in
      while !j < n && not (is_ws s.[!j]) do
        incr j
      done;
      go !j (String.sub s i (!j - i) :: acc)
  in
  go 0 []

let query_features_batch clang pairs =
  match pairs with
  | [] -> []
  | _ ->
      let buf = Buffer.create 512 in
      List.iter
        (fun (op, name) ->
          Buffer.add_string buf op;
          Buffer.add_char buf '(';
          Buffer.add_string buf name;
          Buffer.add_string buf ")\n")
        pairs;
      let out =
        run_cmd_capture ~stdin_data:(Some (Buffer.contents buf))
          ~capture_stderr:false clang
          [ "-E"; "-P"; "-x"; "c"; "-" ]
      in
      let vals = split_ws out in
      let rec combine ps vs acc =
        match (ps, vs) with
        | (op, name) :: prest, v :: vrest ->
            combine prest vrest
              ({ feat_op = op; feat_name = name; feat_val = v } :: acc)
        | _ -> List.rev acc
      in
      combine pairs vals []

let query_single_feature clang_opt op name =
  match clang_opt with
  | None -> "0"
  | Some clang -> (
      match query_features_batch clang [ (op, name) ] with
      | entry :: _ -> entry.feat_val
      | [] -> "0")

let discover_base_env ~no_profile ~clang_opt ~inc_dirs ~defines =
  let env0 =
    if no_profile then make_pp_env [] [] [] "<input>"
    else
      let clang =
        match clang_opt with
        | Some p -> p
        | None -> (
            match Sys.getenv_opt "FILCC" with
            | Some p when p <> "" -> p
            | _ -> "clang")
      in
      let defs_str =
        run_cmd_capture ~capture_stderr:false clang
          [ "-dM"; "-E"; "-x"; "c"; "/dev/null" ]
      in
      let verbose_str =
        run_cmd_capture ~capture_stderr:true clang
          [ "-E"; "-v"; "-x"; "c"; "/dev/null" ]
      in
      let dirs = parse_include_dirs (string_to_char_list verbose_str) in
      let feats = query_features_batch clang default_feature_queries in
      make_pp_env (string_to_char_list defs_str) dirs feats "<input>"
  in
  let env1 =
    match inc_dirs with [] -> env0 | ds -> prepend_include_dirs ds env0
  in
  List.fold_left (fun e spec -> add_cli_define spec e) env1 defines

let rec run_pp_step clang_opt = function
  | PPDone res -> res
  | PPReadFile (path, k) -> run_pp_step clang_opt (k (read_file_bytes_opt path))
  | PPFileExists (path, k) ->
      run_pp_step clang_opt (k (file_exists_regular path))
  | PPRealPath (path, k) -> run_pp_step clang_opt (k (realpath_safe path))
  | PPQueryFeature (op, name, k) ->
      run_pp_step clang_opt (k (query_single_feature clang_opt op name))

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

let parse_fmt = function
  | "s" -> FmtS
  | "d" -> FmtD
  | "x" -> FmtX
  | s -> failwith ("unknown ieee format: " ^ s)

let parse_binop = function
  | "add" -> IeeeAdd
  | "sub" -> IeeeSub
  | "mul" -> IeeeMul
  | "div" -> IeeeDiv
  | s -> failwith ("unknown ieee binop: " ^ s)

let parse_cond = function
  | "eq" -> ICEq
  | "ne" -> ICNe
  | "lt" -> ICLt
  | "le" -> ICLe
  | "gt" -> ICGt
  | "ge" -> ICGe
  | "o" -> ICOrd
  | "uo" -> ICUnord
  | s -> failwith ("unknown ieee cond: " ^ s)

let run_ieee_batch () =
  try
    while true do
      let line = input_line stdin in
      match split_ws line with
      | [ "parse"; k; lit ] -> (
          match ieee_parse (parse_fmt k) (string_to_char_list lit) with
          | Some b -> Printf.printf "ok %s\n" (Big_int_Z.string_of_big_int b)
          | None -> print_endline "fail")
      | [ "decimal"; k; b ] -> (
          match ieee_decimal (parse_fmt k) (Big_int_Z.big_int_of_string b) with
          | Some s -> Printf.printf "ok %s\n" s
          | None -> print_endline "fail")
      | [ "from_int"; k; n ] ->
          let b = ieee_from_int (parse_fmt k) (Big_int_Z.big_int_of_string n) in
          Printf.printf "ok %s\n" (Big_int_Z.string_of_big_int b)
      | [ "to_int"; k; b ] -> (
          match ieee_to_int (parse_fmt k) (Big_int_Z.big_int_of_string b) with
          | Some n -> Printf.printf "ok %s\n" (Big_int_Z.string_of_big_int n)
          | None -> print_endline "fail")
      | [ "neg"; k; a ] ->
          let r = ieee_neg (parse_fmt k) (Big_int_Z.big_int_of_string a) in
          Printf.printf "ok %s\n" (Big_int_Z.string_of_big_int r)
      | [ "sqrt"; k; a ] ->
          let r = ieee_sqrt (parse_fmt k) (Big_int_Z.big_int_of_string a) in
          Printf.printf "ok %s\n" (Big_int_Z.string_of_big_int r)
      | [ "convert"; f; t; a ] ->
          let r =
            ieee_convert (parse_fmt f) (parse_fmt t)
              (Big_int_Z.big_int_of_string a)
          in
          Printf.printf "ok %s\n" (Big_int_Z.string_of_big_int r)
      | [ "binary"; k; op; a; b ] ->
          let r =
            ieee_binary (parse_fmt k) (parse_binop op)
              (Big_int_Z.big_int_of_string a)
              (Big_int_Z.big_int_of_string b)
          in
          Printf.printf "ok %s\n" (Big_int_Z.string_of_big_int r)
      | [ "compare"; k; c; a; b ] ->
          let r =
            ieee_compare (parse_fmt k) (parse_cond c)
              (Big_int_Z.big_int_of_string a)
              (Big_int_Z.big_int_of_string b)
          in
          Printf.printf "ok %s\n" (Big_int_Z.string_of_big_int r)
      | [] -> ()
      | _ ->
          Printf.eprintf "bad ieee query: %s\n" line;
          exit 2
    done
  with End_of_file -> ()

let lex_file ~c23 file =
  let cs = read_file_bytes file in
  match lex_chars file cs with
  | COk ts -> COk (if c23 then c23_tokens ts else ts)
  | CErr m -> CErr m

let pp_one ~c23 ~clang_opt base_env file =
  match run_pp_step clang_opt (preprocess_file file base_env) with
  | COk ts -> COk (if c23 then c23_tokens ts else ts)
  | CErr m -> CErr m

let () =
  let c23 = ref false in
  let no_profile = ref false in
  let clang_opt = ref None in
  let inc_dirs = ref [] in
  let defines = ref [] in
  let pos = ref [] in
  let argc = Array.length Sys.argv in
  let i = ref 1 in
  while !i < argc do
    let arg = Sys.argv.(!i) in
    if arg = "--c23" then c23 := true
    else if arg = "--no-profile" then no_profile := true
    else if arg = "--clang" && !i + 1 < argc then (
      incr i;
      clang_opt := Some Sys.argv.(!i))
    else if arg = "-I" && !i + 1 < argc then (
      incr i;
      inc_dirs := Sys.argv.(!i) :: !inc_dirs)
    else if String.length arg > 2 && String.sub arg 0 2 = "-I" then
      inc_dirs := String.sub arg 2 (String.length arg - 2) :: !inc_dirs
    else if arg = "-D" && !i + 1 < argc then (
      incr i;
      defines := Sys.argv.(!i) :: !defines)
    else if String.length arg > 2 && String.sub arg 0 2 = "-D" then
      defines := String.sub arg 2 (String.length arg - 2) :: !defines
    else pos := arg :: !pos;
    incr i
  done;
  let inc_dirs = List.rev !inc_dirs in
  let defines = List.rev !defines in
  let effective_clang =
    if !no_profile then None
    else
      match !clang_opt with
      | Some p -> Some p
      | None -> (
          match Sys.getenv_opt "FILCC" with
          | Some p when p <> "" -> Some p
          | _ -> Some "clang")
  in
  match List.rev !pos with
  | [ "ieee-batch" ] -> run_ieee_batch ()
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
  | [ "pp"; file ] -> (
      let base_env =
        discover_base_env ~no_profile:!no_profile ~clang_opt:!clang_opt
          ~inc_dirs ~defines
      in
      match pp_one ~c23:!c23 ~clang_opt:effective_clang base_env file with
      | COk ts -> write_canon_list emit_token ts
      | CErr m ->
          Printf.eprintf "pp error: %s\n" m;
          exit 1)
  | [ "pp-parse"; file ] -> (
      let base_env =
        discover_base_env ~no_profile:!no_profile ~clang_opt:!clang_opt
          ~inc_dirs ~defines
      in
      match pp_one ~c23:!c23 ~clang_opt:effective_clang base_env file with
      | CErr m ->
          Printf.eprintf "pp error: %s\n" m;
          exit 1
      | COk ts -> (
          match c_parse ts with
          | COk items -> write_canon_list emit_item items
          | CErr m ->
              Printf.eprintf "parse error: %s\n" m;
              exit 1))
  | [ "typecheck"; file ] -> (
      match lex_file ~c23:!c23 file with
      | CErr m ->
          Printf.eprintf "lex error: %s\n" m;
          exit 1
      | COk ts -> (
          match c_parse ts with
          | CErr m ->
              Printf.eprintf "parse error: %s\n" m;
              exit 1
          | COk items ->
              let vecs =
                match Sys.getenv_opt "NANOFIL_VECTORS" with
                | Some "0" -> false
                | _ -> true
              in
              let gnu89 =
                match Sys.getenv_opt "NANOFIL_STD" with
                | Some "gnu89" -> true
                | _ -> false
              in
              let opts = { topt_vectors = vecs; topt_gnu89 = gnu89 } in
              List.iter print_endline (check_tu_items items opts)))
  | [ "pp-typecheck"; file ] -> (
      let base_env =
        discover_base_env ~no_profile:!no_profile ~clang_opt:!clang_opt
          ~inc_dirs ~defines
      in
      match pp_one ~c23:!c23 ~clang_opt:effective_clang base_env file with
      | CErr m ->
          Printf.eprintf "pp error: %s\n" m;
          exit 1
      | COk ts -> (
          match c_parse ts with
          | CErr m ->
              Printf.eprintf "parse error: %s\n" m;
              exit 1
          | COk items ->
              let vecs =
                match Sys.getenv_opt "NANOFIL_VECTORS" with
                | Some "0" -> false
                | _ -> true
              in
              let gnu89 =
                match Sys.getenv_opt "NANOFIL_STD" with
                | Some "gnu89" -> true
                | _ -> false
              in
              let opts = { topt_vectors = vecs; topt_gnu89 = gnu89 } in
              List.iter print_endline (check_tu_items items opts)))
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
  | "pp-only-bench" :: files when files <> [] ->
      let tp0 = Unix.gettimeofday () in
      let base_env =
        discover_base_env ~no_profile:!no_profile ~clang_opt:!clang_opt
          ~inc_dirs ~defines
      in
      let t0 = Unix.gettimeofday () in
      let ok = ref 0 in
      let err = ref 0 in
      let total_toks = ref 0 in
      List.iter
        (fun file ->
          match pp_one ~c23:!c23 ~clang_opt:effective_clang base_env file with
          | CErr m ->
              Printf.eprintf "pp error (%s): %s\n" file m;
              incr err
          | COk ts ->
              incr ok;
              total_toks := !total_toks + List.length ts)
        files;
      let dt = (Unix.gettimeofday () -. t0) *. 1000.0 in
      let dprof = (t0 -. tp0) *. 1000.0 in
      Printf.printf
        "Gallina-OCaml pp-only: %d ok, %d err | %d tokens | %.1f ms (profile %.1f ms)\n"
        !ok !err !total_toks dt dprof
  | "pp-bench" :: files when files <> [] ->
      let tp0 = Unix.gettimeofday () in
      let base_env =
        discover_base_env ~no_profile:!no_profile ~clang_opt:!clang_opt
          ~inc_dirs ~defines
      in
      let t0 = Unix.gettimeofday () in
      let ok = ref 0 in
      let err = ref 0 in
      let total_toks = ref 0 in
      let total_items = ref 0 in
      List.iter
        (fun file ->
          match pp_one ~c23:!c23 ~clang_opt:effective_clang base_env file with
          | CErr m ->
              Printf.eprintf "pp error (%s): %s\n" file m;
              incr err
          | COk ts -> (
              total_toks := !total_toks + List.length ts;
              match c_parse ts with
              | COk items ->
                  incr ok;
                  total_items := !total_items + List.length items
              | CErr m ->
                  Printf.eprintf "parse error (%s): %s\n" file m;
                  incr err))
        files;
      let dt = (Unix.gettimeofday () -. t0) *. 1000.0 in
      let dprof = (t0 -. tp0) *. 1000.0 in
      Printf.printf
        "Gallina-OCaml pp+parse: %d ok, %d err | %d tokens, %d items | %.1f ms (profile %.1f ms)\n"
        !ok !err !total_toks !total_items dt dprof
  | _ ->
      prerr_endline
        "usage: nanofil-frontend [--c23] [--no-profile] [--clang PATH] [-I DIR] [-D NAME[=VAL]] (lex | parse | pp | pp-parse | ieee-batch | typecheck | pp-typecheck | bench | pp-only-bench | pp-bench) FILE...";
      exit 2
