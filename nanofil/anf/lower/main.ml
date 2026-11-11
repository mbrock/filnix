(* `anf-lower FILE.anf`: the λANF clauses CertiRocq's tap wrote
   (nix/certirocq-anf-tap.patch), read by IrText.v's reader, lowered
   by AnfLower.v's lower, and printed as nanofil IR text, one item
   per clause, which `nanofil-backend compile-allocated` compiles.
   Exits 1, with the reason, for a program the lowering refuses. *)

open Anf_lower

(* The bytes of the file f as the text IrText.v reads, in pieces of
   1 MB, as rocq/backend/extraction/main.ml reads it. *)
let file_text f =
  let size = 1 lsl 20 in
  let ic = In_channel.open_bin f in
  let buf = Bytes.create size in
  let rec fill at =
    let n = if at < size then In_channel.input ic buf at (size - at) else 0 in
    if n = 0 then at else fill (at + n) in
  let rec next () =
    let n = fill 0 in
    if n = 0 then (In_channel.close ic; TextEnd)
    else
      let rec go i acc = if i < 0 then acc else go (i - 1) (Bytes.unsafe_get buf i :: acc) in
      TextPiece (go (n - 1) [], next)
  in
  next ()

(* An atom as Prolog reads it back: bare when it is a name, else
   quoted. *)
let atom b a =
  let bare =
    a <> "" && (match a.[0] with 'a' .. 'z' -> true | _ -> false)
    && String.for_all (function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false) a in
  if bare || a = "[]" then Buffer.add_string b a
  else begin
    Buffer.add_char b '\'';
    String.iter (function
        | '\'' -> Buffer.add_string b "\\'"
        | '\\' -> Buffer.add_string b "\\\\"
        | c -> Buffer.add_char b c) a;
    Buffer.add_char b '\''
  end

let rec term b = function
  | TInt n -> Buffer.add_string b (Big_int_Z.string_of_big_int n)
  | TAtom a -> atom b a
  | TList ts -> Buffer.add_char b '['; args b ts; Buffer.add_char b ']'
  | TApp ("-", [x; y]) -> term b x; Buffer.add_char b '-'; term b y
  | TApp (f, ts) -> atom b f; Buffer.add_char b '('; args b ts; Buffer.add_char b ')'
and args b = function
  | [] -> ()
  | [t] -> term b t
  | t :: ts -> term b t; Buffer.add_string b ", "; args b ts

let () =
  match Sys.argv with
  | [| _; f |] ->
      (match text_clauses (file_text f) [] [] with
       | None -> prerr_endline ("anf-lower: the clauses of " ^ f ^ " are not read"); exit 1
       | Some cs ->
           match lower cs with
           | Err why -> prerr_endline ("anf-lower: " ^ why); exit 1
           | Ok (TApp ("module", [TList items]), c) ->
               Printf.eprintf "anf-lower: %d functions, %d as blocks, %d with fids, %d IR functions\n"
                 c.n_functions c.n_blocks c.n_fids (List.length items);
               let b = Buffer.create (1 lsl 16) in
               List.iter (fun it -> term b it; Buffer.add_string b ".\n"; Buffer.output_buffer stdout b;
                           Buffer.clear b) items
           | Ok _ -> prerr_endline "anf-lower: not a module"; exit 1)
  | _ -> prerr_endline "usage: anf-lower FILE.ir"; exit 2
