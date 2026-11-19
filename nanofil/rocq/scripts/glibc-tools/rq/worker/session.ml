type event =
  | Sentence of { origin : string; line : int; text : string }
  | Log of string
  | Transcript of string
  | Dropped of string

type request =
  | Load of Rocq_engine.target
  | Step of { origin : string; text : string }
  | Try of { candidates : string list; commit : bool }
  | Check
  | Back of int
  | Goals
  | Nodes

type node = Rocq_engine.snapshot History.entry

type run_report = {
  committed : node list;
  stop : Rocq_engine.stop;
  messages : Rocq_engine.message list;
  goals : Rocq_goals.t option;
}

type candidate_report = {
  candidate : string;
  ok : bool;
  report : run_report;
}

type reply =
  | Restart_needed of string list
  | Loaded of {
      reused : int;
      dropped_scratch : int;
      report : run_report;
    }
  | Stepped of run_report
  | Tried of {
      results : candidate_report list;
      committed_candidate : bool;
      interrupted : bool;
    }
  | Checked of {
      ok : bool;
      goals_before : Rocq_goals.t option;
      committed : node list;
      stop : Rocq_engine.stop;
      messages : Rocq_engine.message list;
    }
  | Backed_up of {
      dropped : int;
      goals : Rocq_goals.t option;
    }
  | Goals_view of Rocq_goals.t option
  | Nodes_list of node list
  | Interrupted
  | Failed_with_exn of string

type t = {
  file : string;
  engine : Rocq_engine.t;
  emit : event -> unit;
  mutable history : Rocq_engine.snapshot History.t;
  mutable file_text : string;
}

let create ~file ~args ~emit =
  let callbacks =
    Rocq_engine.
      {
        on_sentence = (fun ~origin ~line ~text -> emit (Sentence { origin; line; text }));
        on_log = (fun line -> emit (Log line));
      }
  in
  let engine = Rocq_engine.create ~args callbacks in
  let history = History.empty ~initial:(Rocq_engine.initial_snapshot engine) in
  { file; engine; emit; history; file_text = "" }

let node_count t = History.length t.history
let tip t = History.tip t.history
let restore_tip t = Rocq_engine.restore (tip t)

let commit_nodes t (nodes : node list) =
  t.history <- History.append t.history nodes;
  List.iter
    (fun (n : node) ->
      if n.origin <> "file" then
        t.emit
          (Transcript
             (Printf.sprintf "(* rq %s:%d *) %s\n" n.origin n.span.start_pos.line n.text)))
    nodes

let report_of_outcome (outcome : Rocq_engine.outcome) state =
  {
    committed = outcome.committed;
    stop = outcome.stop;
    messages = outcome.messages;
    goals = Rocq_engine.goals ~detail:`Summary state;
  }

let is_interrupted_stop = function
  | Rocq_engine.Failed { kind = Interrupted; _ } -> true
  | _ -> false

let stop_succeeded = function
  | Rocq_engine.Done | Reached _ -> true
  | Failed _ -> false

let read_file path =
  In_channel.with_open_bin path In_channel.input_all

let save_scratch t entries =
  if entries <> [] then
    t.emit (Dropped (String.concat "\n" (List.map (fun (e : node) -> e.text) entries) ^ "\n"))

let load t (target : Rocq_engine.target) =
  match Rocq_engine.changed_imports t.engine with
  | _ :: _ as changed ->
      save_scratch t (List.filter (fun (e : node) -> e.origin <> "file") (History.entries t.history));
      Restart_needed changed
  | [] ->
      let text = read_file t.file in
      let source = Source.of_string text in
      let first_diff = Source.first_diff_offset t.file_text text in
      let target_end_offset =
        match target with
        | Line n -> Source.end_of_line source n
        | End | Theorem _ -> max_int
      in
      let reopen_theorem =
        match target with Theorem name -> Some name | End | Line _ -> None
      in
      let plan =
        History.plan_reload t.history ~first_diff ~target_end_offset ~reopen_theorem
      in
      save_scratch t plan.dropped_scratch;
      t.history <- plan.kept;
      t.file_text <- text;
      let outcome =
        Rocq_engine.run ~file:t.file t.engine ~origin:"file" ~target (tip t) source
          ~offset:plan.resume_offset
      in
      commit_nodes t outcome.committed;
      let report = report_of_outcome outcome (tip t) in
      restore_tip t;
      Loaded
        {
          reused = plan.reused_count;
          dropped_scratch = List.length plan.dropped_scratch;
          report;
        }

let step t ~origin ~text =
  let source = Source.of_string text in
  let outcome =
    Rocq_engine.run t.engine ~origin ~target:End (tip t) source ~offset:0
  in
  commit_nodes t outcome.committed;
  let report = report_of_outcome outcome (tip t) in
  restore_tip t;
  Stepped report

let state_after_nodes ~base (nodes : node list) =
  let rec last_state st = function
    | [] -> st
    | (n : node) :: rest -> last_state n.state rest
  in
  last_state base nodes

let try_candidates t candidates ~commit =
  let base = tip t in
  let rec run_each idx winner acc = function
    | [] -> (winner, List.rev acc, false)
    | candidate :: rest ->
        let origin = Printf.sprintf "try%d" idx in
        let source = Source.of_string candidate in
        let outcome =
          Rocq_engine.run ~keep_queries:true t.engine ~origin ~target:End base source ~offset:0
        in
        let end_state = state_after_nodes ~base outcome.committed in
        let ok = stop_succeeded outcome.stop in
        let cand_report =
          { candidate; ok; report = report_of_outcome outcome end_state }
        in
        Rocq_engine.restore base;
        let winner =
          if commit && ok && Stdlib.Option.is_none winner then Some outcome.committed
          else winner
        in
        if is_interrupted_stop outcome.stop then
          (winner, List.rev (cand_report :: acc), true)
        else
          run_each (idx + 1) winner (cand_report :: acc) rest
  in
  let winner, results, interrupted = run_each 1 None [] candidates in
  Stdlib.Option.iter
    (fun nodes ->
      commit_nodes t (List.filter (fun (n : node) -> not n.is_query) nodes))
    winner;
  restore_tip t;
  Tried { results; committed_candidate = Stdlib.Option.is_some winner; interrupted }

let check_qed t =
  let base = tip t in
  let goals_before = Rocq_engine.goals ~detail:`Summary base in
  let outcome =
    Rocq_engine.run t.engine ~origin:"check" ~target:End base (Source.of_string "Qed.") ~offset:0
  in
  restore_tip t;
  Checked
    {
      ok = outcome.stop = Done;
      goals_before;
      committed = outcome.committed;
      stop = outcome.stop;
      messages = outcome.messages;
    }

let back t count =
  let dropped, history' = History.drop_last count t.history in
  t.history <- history';
  let goals = Rocq_engine.goals ~detail:`Summary (tip t) in
  restore_tip t;
  Backed_up { dropped; goals }

let handle t request =
  try
    match request with
    | Load target -> load t target
    | Step { origin; text } -> step t ~origin ~text
    | Try { candidates; commit } -> try_candidates t candidates ~commit
    | Check -> check_qed t
    | Back count -> back t count
    | Goals ->
        let view = Rocq_engine.goals ~detail:`Full (tip t) in
        restore_tip t;
        Goals_view view
    | Nodes -> Nodes_list (History.entries t.history)
  with
  | Interrupt.Cancelled | Sys.Break ->
      restore_tip t;
      Interrupted
  | exn ->
      restore_tip t;
      Failed_with_exn (Printexc.to_string exn)
