type hyp = {
  name : string;
  ty : string;
  body : string option;
}

type goal = {
  id : string;
  hyps : hyp list;
  concl : string;
}

type t = {
  proof_name : string;
  focused_count : int;
  focused : goal list;
  unfocused_count : int;
  shelved_count : int;
  shelved : goal list;
  given_up_count : int;
}

type detail = [ `Summary | `Full ]

let proof_of (st : Vernacstate.t) =
  Stdlib.Option.map
    (fun stk -> Declare.Proof.get (Vernacstate.LemmaStack.get_top stk))
    st.Vernacstate.interp.lemmas

let has_open_proof st =
  Stdlib.Option.is_some st.Vernacstate.interp.lemmas

let print_constr env sigma c =
  Pp.string_of_ppcmds (Printer.pr_leconstr_env env sigma c)

let format_hyp env sigma decl =
  let open Context.Named.Declaration in
  {
    name = Names.Id.to_string (get_id decl);
    ty = print_constr env sigma (get_type decl);
    body = Stdlib.Option.map (print_constr env sigma) (get_value decl);
  }

let format_goal sigma evar =
  match Evd.find_undefined sigma evar with
  | info ->
      let env = Evd.evar_filtered_env (Global.env ()) info in
      (* [Evd.evar_context] stores the newest hypothesis at the head; reversing
         restores top-to-bottom introduction order. *)
      let hyps = List.rev_map (format_hyp env sigma) (Evd.evar_context info) in
      {
        id = Pp.string_of_ppcmds (Evar.print evar);
        hyps;
        concl = print_constr env sigma (Evd.evar_concl info);
      }
  | exception Not_found ->
      { id = "?"; hyps = []; concl = "?" }

let inspect ~detail st =
  match proof_of st with
  | None -> None
  | Some proof ->
      Vernacstate.unfreeze_full_state st;
      let { Proof.sigma; goals; stack; name; _ } = Proof.data proof in
      let shelved_evars = List.filter (Evd.is_undefined sigma) (Evd.shelf sigma) in
      let unfocused_count =
        List.fold_left (fun acc (l, r) -> acc + List.length l + List.length r) 0 stack
      in
      let shown_goals =
        match detail with
        | `Full -> goals
        | `Summary -> (match goals with g :: _ -> [ g ] | [] -> [])
      in
      let shown_shelved =
        match detail with
        | `Full -> List.map (format_goal sigma) shelved_evars
        | `Summary -> []
      in
      Some
        {
          proof_name = Names.Id.to_string name;
          focused_count = List.length goals;
          focused = List.map (format_goal sigma) shown_goals;
          unfocused_count;
          shelved_count = List.length shelved_evars;
          shelved = shown_shelved;
          given_up_count = Evar.Set.cardinal (Evd.given_up sigma);
        }
