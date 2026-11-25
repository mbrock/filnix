(* Forward dispatch hooks between mutually recursive draw modules. *)

open Ast
open Draw_env

let draw_term_ref : (ctx -> Html.t -> expr -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)

let draw_blk_ref : (ctx -> Html.t -> expr -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)

let draw_name_ref_ref : (ctx -> Html.t -> string -> string list -> [`Head | `Arg] -> unit) ref =
  ref (fun _ _ _ _ _ -> assert false)

let draw_var_ref : (Html.t -> string -> unit) ref = ref (fun _ _ -> assert false)
let draw_var_def_ref : (Html.t -> string -> unit) ref = ref (fun _ _ -> assert false)
let draw_kw_ref : (Html.t -> string -> unit) ref = ref (fun _ _ -> assert false)
let draw_defeq_ref : (Html.t -> unit) ref = ref (fun _ -> assert false)
let draw_items_ref : (ctx -> Html.t -> item list -> unit) ref = ref (fun _ _ _ -> assert false)
let draw_expr_items_ref : (ctx -> Html.t -> expr list -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_sep_items_ref : (ctx -> Html.t -> expr list -> string list -> string -> unit) ref =
  ref (fun _ _ _ _ _ -> assert false)
let draw_binders_ref : (ctx -> Html.t -> binder list -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_opt_type_ref : (ctx -> Html.t -> expr option -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_vars_ref : (Html.t -> name list -> unit) ref = ref (fun _ _ -> assert false)
let draw_seq_defs_ref : (Html.t -> name list -> unit) ref = ref (fun _ _ -> assert false)
let draw_notation_pat_ref : (Html.t -> string -> expr -> unit) ref = ref (fun _ _ _ -> assert false)

let draw_ir_fn_block_ref :
    (ctx -> Html.t -> expr -> expr -> ir_param list -> expr -> ir_body -> string list -> unit) ref =
  ref (fun _ _ _ _ _ _ _ _ -> assert false)
let draw_ir_blk_standalone_ref : (ctx -> Html.t -> ir_block -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_ir_list_block_ref : (ctx -> Html.t -> ir_ssa list -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_ir_ssa_ref : (ctx -> Html.t -> ir_ssa -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_ir_inline_ssa_items_ref : (ctx -> Html.t -> ir_ssa list -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_ir_blk_inline_ref : (ctx -> Html.t -> ir_block -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_ir_fn_inline_ref :
    (ctx -> Html.t -> expr -> expr -> ir_param list -> expr -> ir_body -> string list -> unit) ref =
  ref (fun _ _ _ _ _ _ _ _ -> assert false)

let draw_proof_ref : (ctx -> Html.t -> vernac -> proof_body -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_tactic_block_ref : (ctx -> Html.t -> tactic -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let draw_tactic_inline_ref : (ctx -> Html.t -> tactic -> string list -> unit) ref =
  ref (fun _ _ _ _ -> assert false)
let tactic_structural_ref : (tactic -> bool) ref = ref (fun _ -> false)

let notes_before_ref : (ctx -> Html.t -> int -> unit) ref = ref (fun _ _ _ -> assert false)
let notes_rows_ref : (ctx -> Html.t -> int -> int -> unit) ref = ref (fun _ _ _ _ -> assert false)
let aside_after_ref : (ctx -> Html.t -> int -> unit) ref = ref (fun _ _ _ -> assert false)
let aside_text_ref : (ctx -> int -> string option) ref = ref (fun _ _ -> assert false)
let draw_prose_inline_ref : (ctx -> Html.t -> string -> unit) ref = ref (fun _ _ _ -> assert false)
let draw_prose_ref : (ctx -> Html.t -> string list -> unit) ref = ref (fun _ _ _ -> assert false)
let draw_rocq_layout_ref : (Html.t -> unit) ref = ref (fun _ -> assert false)
