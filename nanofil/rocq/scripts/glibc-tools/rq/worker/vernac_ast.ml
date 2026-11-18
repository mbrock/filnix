let is_pure_query_expr = function
  | Vernacexpr.VernacShow _
  | VernacPrint _
  | VernacSearch _
  | VernacLocate _
  | VernacCheckMayEval _
  | VernacGlobalCheck _
  | VernacPrintOption _
  | VernacMemOption _
  | VernacCheckGuard
  | VernacValidateProof
  | VernacComments _ -> true
  | _ -> false

let is_query (vc : Vernacexpr.vernac_control) =
  Vernacprop.has_query_control vc
  || (match vc.CAst.v.expr with
      | VernacSynPure expr -> is_pure_query_expr expr
      | VernacSynterp _ -> false)
  || (try Vernac_classifier.classify_vernac vc = Vernacextend.VtQuery
      with _ -> false)

let is_proof_header (vc : Vernacexpr.vernac_control) =
  match vc.CAst.v.expr with
  | VernacSynPure (VernacProof _) -> true
  | _ -> false

let add_unique acc name =
  if List.mem name acc then acc else name :: acc

let add_lident acc (lid : Names.lident) =
  add_unique acc (Names.Id.to_string lid.CAst.v)

let add_lname acc (lname : Names.lname) =
  match lname.CAst.v with
  | Names.Name.Name id -> add_unique acc (Names.Id.to_string id)
  | Names.Name.Anonymous -> acc

let defined_names (vc : Vernacexpr.vernac_control) =
  let acc =
    match vc.CAst.v.expr with
    | VernacSynPure expr -> (
        match expr with
        | VernacStartTheoremProof (_, proof_exprs) ->
            List.fold_left (fun acc ((lid, _), _) -> add_lident acc lid) [] proof_exprs
        | VernacDefinition (_, (lname, _), _) ->
            add_lname [] lname
        | VernacInstance ((lname, _), _, _, _, _) ->
            add_lname [] lname
        | VernacDeclareInstance ((lid, _), _, _, _) ->
            add_lident [] lid
        | VernacFixpoint (_, (_, rec_exprs)) | VernacCoFixpoint (_, rec_exprs) ->
            List.fold_left
              (fun acc (r : Vernacexpr.recursive_expr_gen) -> add_lident acc r.fname)
              [] rec_exprs
        | _ -> [])
    | VernacSynterp _ -> []
  in
  let acc =
    match Vernac_classifier.classify_vernac vc with
    | Vernacextend.VtStartProof (_, ids) ->
        List.fold_left (fun acc id -> add_unique acc (Names.Id.to_string id)) acc ids
    | _ | exception _ -> acc
  in
  List.rev acc
