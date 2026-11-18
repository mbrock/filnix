type snapshot = Vernacstate.t

type target =
  | End
  | Line of int
  | Theorem of string

type message = {
  level : string;
  text : string;
}

type failure_kind =
  | Syntax
  | Tactic_or_cmd
  | Interrupted

type stop =
  | Done
  | Reached of string
  | Failed of {
      kind : failure_kind;
      text : string;
      span : Source.span;
      message : string;
    }

type outcome = {
  committed : snapshot History.entry list;
  stop : stop;
  messages : message list;
}

type callbacks = {
  on_sentence : origin:string -> line:int -> text:string -> unit;
  on_log : string -> unit;
}

type t = {
  callbacks : callbacks;
  initial : snapshot;
  sentence_messages : message list ref;
  loaded_objects : (string * float) list ref;  (* .vo path * mtime when loaded *)
}

let level_name = function
  | Feedback.Debug -> "debug"
  | Info -> "info"
  | Notice -> "notice"
  | Warning -> "warning"
  | Error -> "error"

let failure_kind_name = function
  | Syntax -> "syntax"
  | Tactic_or_cmd -> "error"
  | Interrupted -> "interrupted"

let create ~args callbacks =
  Coqinit.init_ocaml ();
  let usage =
    Boot.Usage.{ executable_name = "rq-worker"; extra_args = ""; extra_options = "" }
  in
  let opts, () =
    Coqinit.parse_arguments
      ~parse_extra:(fun _ extra -> ((), extra))
      ~initial_args:Coqargs.default args
  in
  Coqinit.init_runtime ~usage opts;
  Coqinit.init_document opts;
  let sentence_messages = ref [] in
  let loaded_objects = ref [] in
  Feedback.warn_no_listeners := false;
  ignore
    (Feedback.add_feeder (fun fb ->
         match fb.Feedback.contents with
         | Message (Debug, _, _, _) -> ()
         | Message (lvl, _, _, pp) ->
             let msg = { level = level_name lvl; text = Pp.string_of_ppcmds pp } in
             sentence_messages := msg :: !sentence_messages
         | FileLoaded (_, path) -> (
             match Unix.stat path with
             | st -> loaded_objects := (path, st.Unix.st_mtime) :: !loaded_objects
             | exception Unix.Unix_error _ -> ())
         | _ -> ()));
  let top = Coqinit.dirpath_of_top opts.config.logic.toplevel_name in
  Coqinit.start_library ~intern:Vernacinterp.fs_intern ~top (Coqargs.injection_commands opts);
  let initial = Vernacstate.freeze_full_state () in
  { callbacks; initial; sentence_messages; loaded_objects }

let initial_snapshot t = t.initial
let restore st = Vernacstate.unfreeze_full_state st
let goals ~detail st = Rocq_goals.inspect ~detail st

let changed_imports t =
  List.filter_map
    (fun (path, mtime) ->
      match Unix.stat path with
      | st when st.Unix.st_mtime = mtime -> None
      | _ | (exception Unix.Unix_error _) -> Some path)
    !(t.loaded_objects)

let make_parsable ?file source ~offset =
  let loc_source =
    match file with
    | Some path -> Loc.InFile { dirpath = None; file = path }
    | None -> Loc.ToplevelInput
  in
  let pos = Source.pos_of_offset source offset in
  let bol = Source.line_start_offset source offset in
  let loc = Loc.create loc_source pos.line bol offset offset in
  let rest = Source.sub source ~bp:offset ~ep:(Source.length source) in
  let stream = Gramlib.Stream.of_string ~offset rest in
  (loc_source, Procq.Parsable.make ~loc stream)

let error_failure source ~loc_source ~default_bp ~default_ep ~kind ~text exn =
  let e, info = Exninfo.capture exn in
  let bp, ep =
    match Loc.get_loc info with
    | Some loc when loc.Loc.fname = loc_source -> Loc.unloc loc
    | _ -> (default_bp, default_ep)
  in
  Failed
    {
      kind;
      text;
      span = Source.span source ~bp ~ep;
      message = Pp.string_of_ppcmds (CErrors.iprint (e, info));
    }

let interrupted_failure source ~bp ~ep ~text =
  Failed
    {
      kind = Interrupted;
      text;
      span = Source.span source ~bp ~ep;
      message = "interrupted by rq cancel";
    }

let parse_next ~st parsable =
  Vernacstate.unfreeze_full_state st;
  let proof_mode =
    if Rocq_goals.has_open_proof st then Some (Synterp.get_default_proof_mode ())
    else None
  in
  Procq.Entry.parse (Pvernac.main_entry proof_mode) parsable

type sentence_result =
  | Executed of snapshot History.entry * message list
  | Aborted of stop * message list

let exec_sentence t ~source ~loc_source ~origin ~(span : Source.span) ~text ~st vc =
  t.callbacks.on_sentence ~origin ~line:span.start_pos.line ~text;
  t.sentence_messages := [];
  let drain_messages () = List.rev !(t.sentence_messages) in
  let t0 = Unix.gettimeofday () in
  match
    Interrupt.with_armed (fun () ->
        Vernacinterp.interp ~intern:Vernacinterp.fs_intern ~st vc)
  with
  | st' ->
      let ms = (Unix.gettimeofday () -. t0) *. 1000.0 in
      let msgs = drain_messages () in
      List.iter
        (fun m -> t.callbacks.on_log (Printf.sprintf "[%s] %s" m.level m.text))
        msgs;
      let entry : snapshot History.entry =
        {
          origin;
          text;
          span;
          state = st';
          ms;
          is_query = Vernac_ast.is_query vc;
          defined_names = Vernac_ast.defined_names vc;
        }
      in
      Executed (entry, msgs)
  | exception (Interrupt.Cancelled | Sys.Break) ->
      Vernacstate.Interp.invalidate_cache ();
      Aborted (interrupted_failure source ~bp:span.bp ~ep:span.ep ~text, [])
  | exception e when CErrors.noncritical e ->
      let msgs = drain_messages () in
      let stop =
        error_failure source ~loc_source ~default_bp:span.bp ~default_ep:span.ep
          ~kind:Tactic_or_cmd ~text e
      in
      Aborted (stop, msgs)

let matches_theorem target names =
  match target with
  | Theorem name -> List.mem name names
  | End | Line _ -> false

let run ?file ?(keep_queries = false) t ~origin ~target start_st source ~offset =
  let loc_source, parsable = make_parsable ?file source ~offset in
  let target_end_offset =
    match target with Line n -> Source.end_of_line source n | End | Theorem _ -> max_int
  in
  let rec loop st acc rev_msgs ~awaiting_proof_header =
    let last_ep =
      match acc with (e : _ History.entry) :: _ -> e.span.ep | [] -> offset
    in
    if Interrupt.is_requested () then
      (List.rev acc, interrupted_failure source ~bp:last_ep ~ep:last_ep ~text:"", rev_msgs)
    else
      match parse_next ~st parsable with
      | exception e when CErrors.noncritical e ->
          let stop =
            error_failure source ~loc_source ~default_bp:last_ep ~default_ep:last_ep
              ~kind:Syntax ~text:"" e
          in
          (List.rev acc, stop, rev_msgs)
      | None ->
          let stop = if awaiting_proof_header then Reached "theorem" else Done in
          (List.rev acc, stop, rev_msgs)
      | Some vc ->
          let bp, ep =
            match vc.CAst.loc with Some loc -> Loc.unloc loc | None -> (offset, offset)
          in
          let span = Source.span source ~bp ~ep in
          let text = Source.sub source ~bp ~ep in
          begin match target with
          | Line n when ep > target_end_offset ->
              (List.rev acc, Reached ("line " ^ string_of_int n), rev_msgs)
          | _ when awaiting_proof_header && not (Vernac_ast.is_proof_header vc) ->
              (List.rev acc, Reached "theorem", rev_msgs)
          | _ ->
              begin match exec_sentence t ~source ~loc_source ~origin ~span ~text ~st vc with
              | Aborted (stop, msgs) ->
                  (List.rev acc, stop, List.rev_append msgs rev_msgs)
              | Executed (entry, msgs) ->
                  let rev_msgs' = List.rev_append msgs rev_msgs in
                  let acc' =
                    if entry.is_query && not keep_queries then acc else entry :: acc
                  in
                  if awaiting_proof_header then
                    (List.rev acc', Reached "theorem", rev_msgs')
                  else
                    loop entry.state acc' rev_msgs'
                      ~awaiting_proof_header:(matches_theorem target entry.defined_names)
              end
          end
  in
  let committed, stop, rev_msgs = loop start_st [] [] ~awaiting_proof_header:false in
  begin match stop with
  | Failed { kind; message; _ } ->
      t.callbacks.on_log (Printf.sprintf "[%s] %s" (failure_kind_name kind) message)
  | Done | Reached _ -> ()
  end;
  { committed; stop; messages = List.rev rev_msgs }
