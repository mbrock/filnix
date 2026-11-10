(* The driver of the extracted backend. So far it is the printer's
   gate: it reads the line terms `nanofil asm-terms FILE TEXT` prints
   from stdin, decodes each (AsmTerm.v's dline) and writes their text
   (Asm.v's rev_lines_parts) to stdout, which tests/asm.sh compares
   with the text that command wrote. It exits 1 on a term that is not
   a line.

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
   and 135 MB of text) is held but the input. *)
let chunk = 4096

let () =
  let next = reader (In_channel.input_all stdin) in
  set_binary_mode_out stdout true;
  let count = ref 0 in
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
          List.iter print_string (rev_lines_parts (List.rev ls) []));
        go ()
  in
  go ();
  if report then
    Printf.eprintf "nanofil-backend: %d lines parse %.3fs decode %.3fs print %.3fs\n"
      !count !parse_s !decode_s !print_s
