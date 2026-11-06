(* The driver of the extracted model: reads the terms `nanofil outcomes
   FILE` prints (main.pl's outcomes/3) from stdin, decodes the first as
   the checked module, and judges each following line (Transport.v's
   judge). With --valid it reads rocq/mutants.pl's output instead and
   judges each verdict (judge_valid). Prints one judgment per line and a summary, and exits 1 if
   any line disagrees.

   The terms are SWI-Prolog's write_canonical form (format's ~k):
   integers, atoms (bare or quoted), compounds f(A, ...) and proper
   lists [A, ...], each top-level term ended by a full stop. *)

open Nanofil_model

exception Syntax of string

let parse (s : string) : term list =
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
  let is_symbol c = String.contains "+-*/\\^<>=~:.?@#&$" c in
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
  let rec terms acc =
    skip ();
    if !pos >= n then List.rev acc
    else begin
      let t = term () in
      expect '.';
      terms (t :: acc)
    end
  in
  terms []

let rec print (b : Buffer.t) (t : term) : unit =
  let atom a =
    let plain = a <> "" && (match a.[0] with 'a' .. 'z' -> true | _ -> false)
                && String.for_all (fun c -> match c with
                     | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false) a in
    if plain || a = "[]" then Buffer.add_string b a
    else begin
      Buffer.add_char b '\'';
      String.iter (fun c -> if c = '\'' || c = '\\' then Buffer.add_char b '\\';
                            Buffer.add_char b c) a;
      Buffer.add_char b '\''
    end
  in
  let list ts = List.iteri (fun i t -> if i > 0 then Buffer.add_char b ','; print b t) ts in
  match t with
  | TInt z -> Buffer.add_string b (Big_int_Z.string_of_big_int z)
  | TAtom a -> atom a
  | TApp (f, xs) -> atom f; Buffer.add_char b '('; list xs; Buffer.add_char b ')'
  | TList ts -> Buffer.add_char b '['; list ts; Buffer.add_char b ']'

let show t = let b = Buffer.create 64 in print b t; Buffer.contents b

let () =
  let input = In_channel.input_all stdin in
  match parse input with
  | [] -> prerr_endline "nanofil-model: no input"; exit 2
  | m :: lines ->
      match decode_module m with
      | None -> prerr_endline "nanofil-model: the module does not decode"; exit 2
      | Some md ->
          let count = Hashtbl.create 8 in
          let judge = if Array.exists (( = ) "--valid") Sys.argv then judge_valid else judge in
          List.iter (fun line ->
              let j = judge md line in
              let k = match j with TApp (k, _) -> k | _ -> "?" in
              Hashtbl.replace count k (1 + Option.value ~default:0 (Hashtbl.find_opt count k));
              print_endline (show j)) lines;
          let get k = Option.value ~default:0 (Hashtbl.find_opt count k) in
          Printf.printf "%% agree %d, disagree %d, outside %d, stuck_both %d, bad_line %d\n"
            (get "agree") (get "disagree") (get "outside") (get "stuck_both") (get "bad_line");
          if get "disagree" > 0 || get "bad_line" > 0 then exit 1
