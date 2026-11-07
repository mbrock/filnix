(* Call the extracted Validate.valid, not Transport.judge_valid's partial
   edit verdict. The whole module is None if any function is outside;
   list every such function by inspecting the extracted decoder's result. *)
open Nanofil_model

let () =
  match Parser.parse (In_channel.input_all stdin) with
  | [m] ->
      (match decode_module m with
       | None -> failwith "module does not decode"
       | Some md ->
           let funcs = ref 0 and outside = ref 0 in
           List.iter (function
               | IFunc f -> incr funcs; Printf.printf "function(%s,inside).\n" (Parser.show f.fn_name)
               | IOutside (n, _) -> incr funcs; incr outside;
                   Printf.printf "function(%s,outside).\n" (Parser.show n)
               | _ -> ()) md;
           let verdict = match valid md with None -> "none" | Some true -> "true" | Some false -> "false" in
           Printf.printf "valid(%s).\nfunctions(%d,%d).\n" verdict !funcs !outside;
           if verdict = "false" then exit 1)
  | _ -> failwith "expected exactly one checked module"
