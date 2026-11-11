(* `rx-gallina [--check OUT] FILE.pl`: what experiments/regex-nanofil/rx.pl's
   `rx:rx_file('FILE.pl')` prints, computed by the extraction of Rx.v
   (Extract.v). It exits 0 where rx.pl succeeds and 1 where rx.pl
   fails or raises an error.

   Each function is also read back from the line printed for it with
   IrText.v's reader, which must give the very term Rx.v built
   (term_eqb), so that handing the term to the backend is handing it the
   text. With --check OUT, the functions that IrText reads from OUT, the
   text rx.pl printed for FILE.pl, must be the terms built, one for one.
   A check that fails exits 3. *)

open Rx

let read_file f = In_channel.with_open_bin f In_channel.input_all
let chars s = List.init (String.length s) (String.get s)

let die fmt = Printf.ksprintf (fun m -> prerr_endline ("rx-gallina: " ^ m); exit 3) fmt

let () =
  let check, file =
    match List.tl (Array.to_list Sys.argv) with
    | [ "--check"; out; file ] -> (Some out, file)
    | [ file ] -> (None, file)
    | _ ->
        prerr_endline "usage: rx-gallina [--check RX_PL_OUTPUT] FILE.pl";
        exit 2
  in
  let outcomes = rx_outcomes (chars (read_file file)) in
  let lines, ok = outcome_lines outcomes [] in
  List.iter print_string lines;
  flush stdout;
  (* The functions printed, with their lines: those before the first
     outcome that stops the printing. *)
  let rec funcs acc = function
    | Func f :: rest -> (
        match outcome_lines [ Func f ] [] with
        | [ line ], true -> funcs ((f, line) :: acc) rest
        | _ -> List.rev acc)
    | Unsupported _ :: rest -> funcs acc rest
    | Failed :: _ | [] -> List.rev acc
  in
  let printed = funcs [] outcomes in
  List.iteri
    (fun i (f, line) ->
      match read_clauses (chars line) with
      | Some [ g ] when term_eqb f g -> ()
      | _ -> die "function %d: IrText does not read back the term built" (i + 1))
    printed;
  (match check with
  | None -> ()
  | Some out -> (
      match read_clauses (chars (read_file out)) with
      | None -> die "IrText does not read %s" out
      | Some gs ->
          if List.length gs <> List.length printed then
            die "%s has %d functions, Rx.v built %d" out (List.length gs) (List.length printed);
          List.iteri
            (fun i (g, (f, _)) ->
              if not (term_eqb f g) then
                die "function %d: IrText's term of %s is not the term built" (i + 1) out)
            (List.combine gs printed)));
  exit (if ok then 0 else 1)
