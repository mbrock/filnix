(* The driver of the extracted backend: the gates of its parts.

   With no argument it is the printer's: it reads the line terms
   `nanofil asm-terms FILE TEXT` prints from stdin, decodes each
   (AsmTerm.v's dline) and writes their text (Asm.v's
   rev_lines_parts) to stdout, which tests/asm.sh compares with the
   text that command wrote. It exits 1 on a term that is not a line.

   With `abi` it is the ABI plans' (see [abi] below), and with
   `emit` the emission's (see [emit]).

   The terms are SWI-Prolog's write_canonical form (format's ~k):
   integers, atoms (bare or quoted), compounds f(A, ...) and proper
   lists [A, ...], each top-level term ended by a full stop. The
   parser is the model driver's (rocq/extraction/main.ml), over this
   extraction's copy of the term type. *)

open Nanofil_backend

exception Syntax of string

(* [reader s] reads the next term of [s] at each call, and None at
   its end. *)
let reader (s : string) : unit -> term option =
  let n = String.length s in
  let pos = ref 0 in
  let peek () = if !pos < n then s.[!pos] else '\000' in
  let rec skip () =
    if !pos < n then
      match s.[!pos] with
      | ' ' | '\n' | '\t' | '\r' -> incr pos; skip ()
      | '%' -> while !pos < n && s.[!pos] <> '\n' do incr pos done; skip ()
      | _ -> ()
  in
  let expect c =
    skip ();
    if peek () = c then incr pos
    else raise (Syntax (Printf.sprintf "expected %c at %d" c !pos))
  in
  let is_alnum c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' || c >= '\128'
  in
  let is_digit c = c >= '0' && c <= '9' in
  let is_symbol c = String.contains "+-*/\\^<>=~:.?@#&$;!" c in
  let quoted () =
    (* after the opening quote *)
    let b = Buffer.create 16 in
    let rec go () =
      if !pos >= n then raise (Syntax "unterminated quoted atom");
      let c = s.[!pos] in
      incr pos;
      if c = '\'' then
        if peek () = '\'' then (incr pos; Buffer.add_char b '\''; go ()) else ()
      else if c = '\\' then begin
        let e = s.[!pos] in
        incr pos;
        (match e with
         | 'n' -> Buffer.add_char b '\n'
         | 't' -> Buffer.add_char b '\t'
         | 'r' -> Buffer.add_char b '\r'
         | 'a' -> Buffer.add_char b '\007'
         | 'b' -> Buffer.add_char b '\b'
         | 'f' -> Buffer.add_char b '\012'
         | 'v' -> Buffer.add_char b '\011'
         | '0' .. '7' ->
             let st = !pos - 1 in
             while s.[!pos] <> '\\' do incr pos done;
             let code = int_of_string ("0o" ^ String.sub s st (!pos - st)) in
             incr pos; Buffer.add_char b (Char.chr code)
         | 'x' ->
             let st = !pos in
             while s.[!pos] <> '\\' do incr pos done;
             let code = int_of_string ("0x" ^ String.sub s st (!pos - st)) in
             incr pos;
             if code < 128 then Buffer.add_char b (Char.chr code)
             else Buffer.add_utf_8_uchar b (Uchar.of_int code)
         | '\n' -> ()
         | c -> Buffer.add_char b c);
        go ()
      end else (Buffer.add_char b c; go ())
    in
    go (); Buffer.contents b
  in
  let rec term () : term =
    skip ();
    let c = peek () in
    if c = '[' then begin
      incr pos; skip ();
      if peek () = ']' then (incr pos; TList [])
      else begin
        let items = args () in
        expect ']'; TList items
      end
    end else if is_digit c || (c = '-' && !pos + 1 < n && is_digit s.[!pos + 1]) then begin
      let st = !pos in
      incr pos;
      while !pos < n && is_digit s.[!pos] do incr pos done;
      TInt (Big_int_Z.big_int_of_string (String.sub s st (!pos - st)))
    end else begin
      let name =
        if c = '\'' then (incr pos; quoted ())
        else if is_alnum c then begin
          let st = !pos in
          while !pos < n && is_alnum s.[!pos] do incr pos done;
          String.sub s st (!pos - st)
        end else if is_symbol c then begin
          let st = !pos in
          while !pos < n && is_symbol s.[!pos] do incr pos done;
          String.sub s st (!pos - st)
        end else if c = '{' && !pos + 1 < n && s.[!pos + 1] = '}' then (pos := !pos + 2; "{}")
        else raise (Syntax (Printf.sprintf "unexpected %C at %d" c !pos))
      in
      if peek () = '(' then begin
        incr pos;
        let xs = args () in
        expect ')'; TApp (name, xs)
      end else TAtom name
    end
  and args () =
    let t = term () in
    skip ();
    if peek () = ',' then (incr pos; t :: args ()) else [t]
  in
  fun () ->
    skip ();
    if !pos >= n then None
    else begin
      let t = term () in
      expect '.';
      Some t
    end

(* NANOFIL_BACKEND_TIME=1 reports the CPU seconds of each step on
   stderr, for the campaign's timings. *)
let report = Sys.getenv_opt "NANOFIL_BACKEND_TIME" <> None
let parse_s = ref 0.0 and decode_s = ref 0.0 and print_s = ref 0.0

let timed total f =
  if report then begin
    let t0 = Sys.time () in
    let x = f () in
    total := !total +. (Sys.time () -. t0);
    x
  end else f ()

(* The terms are read, decoded and printed a chunk of lines at a
   time, so nothing of a whole module (SQLite has 5.5 million lines
   and 135 MB of text) is held but the input. A chunk is small
   enough for its terms, lines and parts to die in the minor heap:
   with 4096 lines they were promoted first, and SQLite took twice
   as long. *)
let chunk = 64

let asm () =
  let next = reader (In_channel.input_all stdin) in
  set_binary_mode_out stdout true;
  let count = ref 0 in
  let text = Buffer.create 65536 in
  let rec terms acc k =
    if k = chunk then acc
    else match next () with
      | Some t -> terms (t :: acc) (k + 1)
      | None -> acc
  in
  (* The lines of the terms [rev], which are in reverse, in order. *)
  let lines rev =
    let i = ref (!count + List.length rev + 1) in
    List.rev_map (fun t ->
        decr i;
        match dline t with
        | Some l -> l
        | None ->
            Printf.eprintf "nanofil-backend: term %d is not a line\n" !i;
            exit 1)
      rev
  in
  let rec go () =
    match timed parse_s (fun () -> terms [] 0) with
    | [] -> ()
    | rev ->
        let ls = timed decode_s (fun () -> lines rev) in
        count := !count + List.length rev;
        (* The printer reads the lines in reverse. *)
        timed print_s (fun () ->
          List.iter (Buffer.add_string text) (rev_lines_parts (List.rev ls) []);
          Buffer.output_buffer stdout text;
          Buffer.clear text);
        go ()
  in
  go ();
  if report then
    Printf.eprintf "nanofil-backend: %d lines parse %.3fs decode %.3fs print %.3fs\n"
      !count !parse_s !decode_s !print_s

(* A term as Prolog writes it, quotes aside: for reporting. *)
let rec show b = function
  | TInt n -> Buffer.add_string b (Big_int_Z.string_of_big_int n)
  | TAtom a -> Buffer.add_string b a
  | TList ts -> Buffer.add_char b '['; show_args b ts; Buffer.add_char b ']'
  | TApp (f, ts) ->
      Buffer.add_string b f; Buffer.add_char b '('; show_args b ts; Buffer.add_char b ')'
and show_args b = function
  | [] -> ()
  | [t] -> show b t
  | t :: ts -> show b t; Buffer.add_char b ','; show_args b ts

let shown t =
  let b = Buffer.create 256 in
  show b t;
  if Buffer.length b > 600 then Buffer.sub b 0 600 ^ "..." else Buffer.contents b

(* Where the terms [ours] and [theirs] first differ: the path of
   argument and element numbers to the innermost pair of subterms
   that differ in more than one argument, and that pair. *)
let rec first_difference path ours theirs =
  let here () = (List.rev path, ours, theirs) in
  let inside xs ys =
    if List.length xs <> List.length ys then here ()
    else
      match List.filter (fun (_, (x, y)) -> not (term_eqb x y))
              (List.mapi (fun i p -> (i, p)) (List.combine xs ys)) with
      | [(i, (x, y))] -> first_difference (string_of_int (i + 1) :: path) x y
      | _ -> here ()
  in
  match ours, theirs with
  | TApp (f, xs), TApp (g, ys) when f = g -> inside xs ys
  | TList xs, TList ys -> inside xs ys
  | _ -> here ()

(* The gate of the ABI plans (tests/abi.sh). Stdin is what `nanofil
   abi-terms FILE` prints: the checked module, then an
   `abi_function(...)` for each function, then `thunks(...)`. Each
   plan Abi.v builds for a function of the core subset must be the
   term the Prolog compiler printed. A function the model keeps
   outside the subset is counted and passed over; one of the subset
   that the backend refuses is counted, named on stderr, and fails
   the gate if NANOFIL_BACKEND_STRICT is set. Exits 1 on a plan that
   differs. *)
let abi () =
  let next = reader (In_channel.input_all stdin) in
  let fail fmt = Printf.ksprintf (fun m -> prerr_endline ("nanofil-backend: " ^ m); exit 1) fmt in
  let lower_s = ref 0.0 and compare_s = ref 0.0 in
  let next () = timed parse_s next in
  let md =
    match next () with
    | Some t ->
        (match timed decode_s (fun () -> decode_module t) with
         | Some md -> md
         | None -> fail "the first term is not a module")
    | None -> fail "no module"
  in
  let sy = timed lower_s (fun () -> module_symbols md) in
  let items = Hashtbl.create 64 in
  List.iter (fun it ->
      match it with
      | IFunc f -> if not (Hashtbl.mem items f.fn_name) then Hashtbl.add items f.fn_name it
      | IOutside (n, _) -> if not (Hashtbl.mem items n) then Hashtbl.add items n it
      | _ -> ())
    md;
  let same = ref 0 and differ = ref 0 and refused = ref 0 and outside = ref 0 in
  let compare what ours theirs =
    if timed compare_s (fun () -> term_eqb ours theirs) then incr same
    else begin
      incr differ;
      let path, a, b = first_difference [] ours theirs in
      Printf.eprintf "DIFFER %s at %s\n  rocq:   %s\n  prolog: %s\n" what
        (String.concat "." path) (shown a) (shown b)
    end
  in
  let rec go () =
    match next () with
    | None -> ()
    | Some (TApp ("abi_function", name :: _) as theirs) ->
        (match Hashtbl.find_opt items name with
         | Some (IFunc f) ->
             (match timed lower_s (fun () -> Option.map plan_term (lower_function sy f)) with
              | Some ours -> compare (shown name) ours theirs
              | None -> incr refused; Printf.eprintf "refused %s\n" (shown name))
         | Some _ -> incr outside
         | None -> fail "the module has no function %s" (shown name));
        go ()
    | Some (TApp ("thunks", _) as theirs) ->
        (match timed lower_s (fun () -> Option.map thunks_term (lower_thunks sy md)) with
         | Some ours -> compare "thunks" ours theirs
         | None -> incr refused; prerr_endline "refused thunks");
        go ()
    | Some t -> fail "not a plan: %s" (shown t)
  in
  go ();
  Printf.printf "plans same %d differ %d refused %d outside %d\n" !same !differ !refused !outside;
  if report then
    Printf.eprintf "nanofil-backend: parse %.3fs decode %.3fs lower %.3fs compare %.3fs\n"
      !parse_s !decode_s !lower_s !compare_s;
  if !differ > 0 || (!refused > 0 && Sys.getenv_opt "NANOFIL_BACKEND_STRICT" <> None) then exit 1

(* The gate of the emission (tests/emit.sh). Stdin is what `nanofil
   emit-terms FILE` prints: the checked module, then a list of line
   terms for each item in order, for each weak thunk in order and for
   the end of the file. Each list is held to the lines the backend
   gives the same item or thunk (EmitModule.v), compared as text.
   Where the backend has a todo line, the lines before the first one
   must begin the Prolog compiler's and the lines after the last one
   must end them; such a list is counted as partial, and its first
   todo is tallied on stderr. A function the model keeps outside its
   subset is counted as outside and one the backend builds no plan
   for as refused; both are passed over. Exits 1 on a list that
   differs or is missing, or, if NANOFIL_BACKEND_STRICT is set, on
   one that is partial or refused. *)
let emit () =
  let next = reader (In_channel.input_all stdin) in
  let fail fmt = Printf.ksprintf (fun m -> prerr_endline ("nanofil-backend: " ^ m); exit 1) fmt in
  let lower_s = ref 0.0 and emit_s = ref 0.0 and compare_s = ref 0.0 in
  let next () = timed parse_s next in
  let md =
    match next () with
    | Some t ->
        (match timed decode_s (fun () -> decode_module t) with
         | Some md -> md
         | None -> fail "the first term is not a module")
    | None -> fail "no module"
  in
  let sy = timed lower_s (fun () -> module_symbols md) in
  (* same, differ and partial, for functions, data and thunks. *)
  let counts = Array.make_matrix 3 3 0 in
  let refused = ref 0 and outside = ref 0 in
  let todos = Hashtbl.create 16 in
  let text l = String.concat "" (rev_lines_parts [l] []) in
  let list_of what = function
    | Some (TList theirs) -> theirs
    | Some t -> fail "not a list of lines for %s: %s" what (shown t)
    | None -> fail "no lines for %s" what
  in
  let check kind name ours theirs =
    let theirs = Array.of_list (List.map (fun t ->
        match dline t with
        | Some l -> text l
        | None -> fail "not a line: %s" (shown t)) theirs) in
    let ours = Array.of_list ours in
    let n = Array.length ours and m = Array.length theirs in
    let first = ref n and last = ref (-1) in
    Array.iteri (fun i l -> if is_todo l then begin
        if !first = n then first := i; last := i end) ours;
    let ours_text = Array.map text ours in
    (* The lines before the first todo begin theirs. *)
    let bad = ref None in
    (try
       for i = 0 to !first - 1 do
         if i >= m || ours_text.(i) <> theirs.(i) then begin
           bad := Some (i, ours_text.(i), if i < m then theirs.(i) else "(none)\n"); raise Exit end
       done;
       if !first = n then begin
         if n < m then begin bad := Some (n, "(none)\n", theirs.(n)); raise Exit end
       end else
         (* The lines after the last todo end theirs. *)
         for k = 1 to n - 1 - !last do
           if m - k < 0 || ours_text.(n - k) <> theirs.(m - k) then begin
             bad := Some (n - k, ours_text.(n - k), if m - k >= 0 then theirs.(m - k) else "(none)\n");
             raise Exit end
         done
     with Exit -> ());
    match !bad with
    | Some (i, a, b) ->
        counts.(kind).(1) <- counts.(kind).(1) + 1;
        Printf.eprintf "DIFFER %s at line %d\n  rocq:   %s  prolog: %s" name i a b
    | None ->
        if !first = n then counts.(kind).(0) <- counts.(kind).(0) + 1
        else begin
          counts.(kind).(2) <- counts.(kind).(2) + 1;
          let what = match first_todo (Array.to_list ours) with Some w -> w | None -> "" in
          Hashtbl.replace todos what (1 + Option.value ~default:0 (Hashtbl.find_opt todos what))
        end
  in
  let held kind name ours theirs =
    let ours = timed emit_s ours in
    timed compare_s (fun () -> check kind name ours theirs)
  in
  List.iter (fun it ->
      match it with
      | IFunc f ->
          let name = shown f.fn_name in
          let theirs = list_of name (next ()) in
          (match timed lower_s (fun () -> lower_function sy f) with
           | Some p -> held 0 name (fun () -> function_lines p) theirs
           | None -> incr refused; Printf.eprintf "refused %s\n" name)
      | IOutside (n, _) -> ignore (list_of (shown n) (next ())); incr outside
      | IData (n, lk, align, items) ->
          let name = shown n in
          held 1 name (fun () -> data_lines n lk align items) (list_of name (next ()))
      | IAlias (n, lk, target) ->
          let name = shown n in
          held 1 name (fun () -> alias_lines sy n lk target) (list_of name (next ())))
    md;
  (* The thunks, then the end of the file, which is the last list. *)
  let rec rest acc = match next () with None -> List.rev acc | t -> rest (list_of "a thunk" t :: acc) in
  let lists = rest [] in
  let thunks, last =
    match List.rev lists with
    | last :: thunks -> List.rev thunks, last
    | [] -> fail "no lines for the end of the file"
  in
  (match timed lower_s (fun () -> lower_thunks sy md) with
   | Some ts ->
       if List.length ts <> List.length thunks then
         fail "%d thunks, and lines for %d" (List.length ts) (List.length thunks);
       List.iter2 (fun t theirs ->
           held 2 ("the thunk of " ^ shown t.th_name) (fun () -> thunk_lines t) theirs)
         ts thunks
   | None -> incr refused; prerr_endline "refused thunks");
  let ends = counts.(1).(1) in
  check 1 "the end of the file" end_lines last;
  let end_differs = counts.(1).(1) > ends in
  if not end_differs then counts.(1).(0) <- counts.(1).(0) - 1;
  let c = counts in
  Printf.printf
    "functions same %d differ %d partial %d refused %d outside %d, data same %d differ %d partial %d, thunks same %d differ %d partial %d\n"
    c.(0).(0) c.(0).(1) c.(0).(2) !refused !outside
    c.(1).(0) c.(1).(1) c.(1).(2) c.(2).(0) c.(2).(1) c.(2).(2);
  Hashtbl.iter (fun what k -> Printf.eprintf "todo %6d %s\n" k what) todos;
  if report then
    Printf.eprintf "nanofil-backend: parse %.3fs decode %.3fs lower %.3fs emit %.3fs compare %.3fs\n"
      !parse_s !decode_s !lower_s !emit_s !compare_s;
  let sum j = c.(0).(j) + c.(1).(j) + c.(2).(j) in
  if sum 1 > 0
     || ((sum 2 > 0 || !refused > 0) && Sys.getenv_opt "NANOFIL_BACKEND_STRICT" <> None)
  then exit 1

(* The assembly of a checked module, the first term of stdin, as
   EmitModule.v's module_pieces gives it and Asm.v prints it: what
   `nanofil compile` prints for the module without -O. Each piece is
   printed before the next is asked for, so its lines die in the
   minor heap. Exits 3, with its output cut short, for a module the
   backend does not take whole: one with a function outside the
   subset or without a plan, or with a form that is not ported. *)
let whole () =
  let next = reader (In_channel.input_all stdin) in
  let fail fmt = Printf.ksprintf (fun m -> prerr_endline ("nanofil-backend: " ^ m); exit 1) fmt in
  let pass fmt = Printf.ksprintf (fun m -> prerr_endline ("nanofil-backend: " ^ m); exit 3) fmt in
  let lower_s = ref 0.0 in
  let md =
    match timed parse_s next with
    | Some t ->
        (match timed decode_s (fun () -> decode_module t) with
         | Some md -> md
         | None -> fail "the first term is not a module")
    | None -> fail "no module"
  in
  set_binary_mode_out stdout true;
  let text = Buffer.create 65536 in
  (* A chunk of lines at a time, as in asm above. *)
  let rec take k rev = function
    | l :: ls when k > 0 -> take (k - 1) (l :: rev) ls
    | ls -> (rev, ls)
  in
  let rec print = function
    | [] -> ()
    | ls ->
        let rev, rest = take chunk [] ls in
        List.iter (Buffer.add_string text) (rev_lines_parts rev []);
        Buffer.output_buffer stdout text;
        Buffer.clear text;
        print rest
  in
  List.iter (fun piece ->
      match timed lower_s (fun () -> piece ()) with
      | None -> pass "a function is outside the subset or has no plan"
      | Some lists ->
          List.iter (fun ls ->
              (match first_todo ls with
               | Some what -> pass "not ported: %s" what
               | None -> ());
              timed print_s (fun () -> print ls)) lists)
    (timed lower_s (fun () -> module_pieces md));
  if report then
    Printf.eprintf "nanofil-backend: parse %.3fs decode %.3fs lower and emit %.3fs print %.3fs\n"
      !parse_s !decode_s !lower_s !print_s

(* The little-endian words of the file f. *)
let file_words f =
  let s = In_channel.with_open_bin f In_channel.input_all in
  List.init (String.length s / 4) (fun i ->
      Big_int_Z.big_int_of_int (Int32.to_int (String.get_int32_le s (4 * i)) land 0xFFFFFFFF))

(* The NFB gate (tests/nfb.sh, docs/nfb.md). Stdin is what `nanofil
   nfb-terms FILE PREFIX` prints: `nfb_module(Stage, Module)` for each
   stage, whose NFB that command wrote to PREFIX.Stage.nfb. Nfb.v's
   writer must write those very words for the module decode_module
   makes of the term, and its reader must read them back as that
   module. Exits 1 on any difference. *)
let nfb prefix =
  let next = reader (In_channel.input_all stdin) in
  let fail fmt = Printf.ksprintf (fun m -> prerr_endline ("nanofil-backend: " ^ m); exit 1) fmt in
  let encode_s = ref 0.0 and read_s = ref 0.0 and input_s = ref 0.0 in
  let bad = ref 0 in
  let rec go () =
    match timed parse_s next with
    | None -> ()
    | Some (TApp ("nfb_module", [TAtom stage; t])) ->
        let theirs = file_words (prefix ^ "." ^ stage ^ ".nfb") in
        let md = match timed decode_s (fun () -> decode_module t) with
          | Some md -> md
          | None -> fail "%s: not a module" stage in
        (match timed encode_s (fun () -> encode md) with
         | None -> incr bad; Printf.printf "%s: the writer refuses the module\n" stage
         | Some ours ->
             let rec first i xs ys = match xs, ys with
               | [], [] -> None
               | x :: xs', y :: ys' -> if Big_int_Z.eq_big_int x y then first (i + 1) xs' ys' else Some i
               | _ -> Some i in
             (match first 0 ours theirs with
              | None -> ()
              | Some i ->
                  incr bad;
                  let around ws = String.concat " " (List.filteri (fun j _ -> j >= i - 2 && j < i + 4)
                      (List.map (fun w -> Printf.sprintf "%08x" (Big_int_Z.int_of_big_int w)) ws)) in
                  Printf.printf "%s: words differ at %d of %d/%d\n  rocq:   %s\n  prolog: %s\n" stage i
                    (List.length ours) (List.length theirs) (around ours) (around theirs)));
        (match timed input_s (fun () -> decode_input theirs) with
         | Some md' when term_eqb (enc_module md') (enc_module md) -> ()
         | _ -> incr bad; Printf.printf "%s: decode_input does not give the module\n" stage);
        (match timed read_s (fun () -> decode theirs) with
         | None -> incr bad; Printf.printf "%s: the reader refuses the words\n" stage
         | Some md' ->
             if not (term_eqb (enc_module md') (enc_module md)) then begin
               incr bad;
               let path, a, b = first_difference [] (enc_module md') (enc_module md) in
               Printf.printf "%s: read back differs at %s\n  read:   %s\n  module: %s\n" stage
                 (String.concat "." path) (shown a) (shown b)
             end else Printf.printf "%s: same %d words\n" stage (List.length theirs));
        go ()
    | Some t -> fail "not an nfb_module: %s" (shown t)
  in
  go ();
  if report then
    Printf.eprintf "nanofil-backend: parse %.3fs decode_module %.3fs encode %.3fs nfb decode %.3fs nfb decode_input %.3fs\n"
      !parse_s !decode_s !encode_s !read_s !input_s;
  if !bad > 0 then exit 1

(* A minor heap of 32 MB: with OCaml's 2 MB, the plans of a large
   function were promoted while they were built, which cost a
   quarter of the time of SQLite's. *)
let big_minor_heap () = Gc.set { (Gc.get ()) with Gc.minor_heap_size = 4 * 1024 * 1024 }

let () =
  match Sys.argv with
  | [| _ |] -> asm ()
  | [| _; "abi" |] -> big_minor_heap (); abi ()
  | [| _; "emit" |] -> big_minor_heap (); emit ()
  | [| _; "module" |] -> big_minor_heap (); whole ()
  | [| _; "nfb"; prefix |] -> big_minor_heap (); nfb prefix
  | _ -> prerr_endline "usage: nanofil-backend [abi | emit | module | nfb PREFIX] <TERMS"; exit 2
