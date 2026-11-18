module J = Yojson.Safe

type job_request = {
  cmd : string;
  request : Session.request;
  detach : bool;
}

type client_msg =
  | Status
  | Cancel of int option
  | Withdraw of int
  | Stop
  | Enqueue of job_request

type worker_state =
  | Starting
  | Idle
  | Busy
  | Failed
  | Stopped

let worker_state_name = function
  | Starting -> "starting"
  | Idle -> "idle"
  | Busy -> "busy"
  | Failed -> "failed"
  | Stopped -> "stopped"

type active_sentence = {
  origin : string;
  line : int;
  text : string;
  started : float;
}

type worker_status = {
  state : worker_state;
  pid : int;
  running_job : int;
  job_started : float;
  nodes : int;
  queued : int;
  updated : float;
  sentence : active_sentence option;
}

(* ## Decoding client requests *)

let decode_json (json : J.t) : (client_msg, string) result =
  let open Yojson.Safe.Util in
  let field name = member name json in
  let int_opt name =
    match field name with `Int n -> Some n | _ -> None
  in
  let string_opt name =
    match field name with `String s when s <> "" -> Some s | _ -> None
  in
  let bool_field name = field name = `Bool true in
  let decode_target () : Rocq_engine.target =
    match (field "theorem", field "line") with
    | `String name, _ -> Theorem name
    | _, `Int n -> Line n
    | _ -> End
  in
  let enqueue cmd request =
    Ok (Enqueue { cmd; request; detach = bool_field "detach" })
  in
  match field "cmd" with
  | `String "status" -> Ok Status
  | `String "cancel" -> Ok (Cancel (int_opt "job"))
  | `String "withdraw" -> (
      match int_opt "job" with
      | Some id -> Ok (Withdraw id)
      | None -> Error "withdraw needs a job")
  | `String "stop" -> Ok Stop
  | `String ("load" as cmd) -> enqueue cmd (Load (decode_target ()))
  | `String ("step" as cmd) ->
      let origin = Stdlib.Option.value (string_opt "label") ~default:"step" in
      let text = to_string (field "text") in
      enqueue cmd (Step { origin; text })
  | `String ("try" as cmd) ->
      let candidates = List.map to_string (to_list (field "candidates")) in
      enqueue cmd (Try { candidates; commit = bool_field "commit" })
  | `String ("check" as cmd) -> enqueue cmd Check
  | `String ("back" as cmd) ->
      let count = Stdlib.Option.value (int_opt "count") ~default:1 in
      enqueue cmd (Back count)
  | `String ("goals" as cmd) -> enqueue cmd Goals
  | `String ("nodes" as cmd) -> enqueue cmd Nodes
  | `String cmd -> Error ("unknown command " ^ cmd)
  | _ -> Error "a request needs a cmd"
  | exception Type_error (msg, _) -> Error msg

let decode_client_msg line =
  match J.from_string line with
  | json -> decode_json json
  | exception (Yojson.Json_error msg | Failure msg) -> Error msg

(* ## Encoding spans, goals, and session replies *)

let encode_span (s : Source.span) : J.t =
  `Assoc
    [
      ("line", `Int s.start_pos.line);
      ("col", `Int s.start_pos.col);
      ("end_line", `Int s.end_pos.line);
      ("end_col", `Int s.end_pos.col);
      ("bp", `Int s.bp);
      ("ep", `Int s.ep);
    ]

let encode_entry (e : _ History.entry) : J.t =
  `Assoc
    [
      ("origin", `String e.origin);
      ("text", `String e.text);
      ("ms", `Float e.ms);
      ("range", encode_span e.span);
    ]

let encode_failure_kind = function
  | Rocq_engine.Syntax -> "syntax"
  | Tactic_or_cmd -> "error"
  | Interrupted -> "interrupted"

let encode_stop = function
  | Rocq_engine.Done -> `Assoc [ ("kind", `String "done") ]
  | Reached target ->
      `Assoc [ ("kind", `String "reached"); ("target", `String target) ]
  | Failed { kind; text; span; message } ->
      `Assoc
        [
          ("kind", `String (encode_failure_kind kind));
          ("text", `String text);
          ("message", `String message);
          ("range", encode_span span);
        ]

let encode_message (m : Rocq_engine.message) : J.t =
  `Assoc [ ("level", `String m.level); ("text", `String m.text) ]

let encode_hyp (h : Rocq_goals.hyp) : J.t =
  let body = match h.body with Some b -> `String b | None -> `Null in
  `Assoc [ ("name", `String h.name); ("type", `String h.ty); ("body", body) ]

let encode_goal (g : Rocq_goals.goal) : J.t =
  `Assoc
    [
      ("id", `String g.id);
      ("hyps", `List (List.map encode_hyp g.hyps));
      ("concl", `String g.concl);
    ]

let encode_goals : Rocq_goals.t option -> J.t = function
  | None -> `Null
  | Some g ->
      `Assoc
        [
          ("proof", `String g.proof_name);
          ("focused", `Int g.focused_count);
          ("goals", `List (List.map encode_goal g.focused));
          ("unfocused", `Int g.unfocused_count);
          ("shelved", `Int g.shelved_count);
          ("shelved_goals", `List (List.map encode_goal g.shelved));
          ("given_up", `Int g.given_up_count);
        ]

let run_report_fields (r : Session.run_report) =
  [
    ("committed", `List (List.map encode_entry r.committed));
    ("stop", encode_stop r.stop);
    ("messages", `List (List.map encode_message r.messages));
    ("goals", encode_goals r.goals);
  ]

let encode_candidate_report (c : Session.candidate_report) : J.t =
  `Assoc
    (([ ("candidate", `String c.candidate); ("ok", `Bool c.ok) ])
    @ run_report_fields c.report)

let session_reply_fields : Session.reply -> (string * J.t) list = function
  | Restart_needed paths ->
      [ ("restart", `List (List.map (fun p -> `String p) paths)) ]
  | Loaded { reused; dropped_scratch; report } ->
      [ ("reused", `Int reused); ("dropped_scratch", `Int dropped_scratch) ]
      @ run_report_fields report
  | Stepped report ->
      run_report_fields report
  | Tried { results; committed_candidate; interrupted } ->
      [
        ("results", `List (List.map encode_candidate_report results));
        ("committed_candidate", `Bool committed_candidate);
      ]
      @ if interrupted then [ ("interrupted", `Bool true) ] else []
  | Checked { ok; goals_before; committed; stop; messages } ->
      [
        ("ok", `Bool ok);
        ("goals_before", encode_goals goals_before);
        ("committed", `List (List.map encode_entry committed));
        ("stop", encode_stop stop);
        ("messages", `List (List.map encode_message messages));
        ("goals", `Null);
      ]
  | Backed_up { dropped; goals } ->
      [ ("dropped", `Int dropped); ("goals", encode_goals goals) ]
  | Goals_view goals ->
      [ ("goals", encode_goals goals) ]
  | Nodes_list entries ->
      [ ("nodes", `List (List.map encode_entry entries)) ]
  | Interrupted ->
      [ ("interrupted", `Bool true) ]
  | Failed_with_exn msg ->
      [ ("error", `String msg) ]

(* ## Encoding worker control replies and envelopes *)

let encode_error msg =
  `Assoc [ ("error", `String msg) ]

let encode_status (s : worker_status) : J.t =
  let sentence_field =
    match s.sentence with
    | None -> []
    | Some sent ->
        [
          ( "sentence",
            `Assoc
              [
                ("origin", `String sent.origin);
                ("line", `Int sent.line);
                ("text", `String sent.text);
                ("started", `Float sent.started);
              ] );
        ]
  in
  `Assoc
    ([
       ("state", `String (worker_state_name s.state));
       ("pid", `Int s.pid);
       ("job", `Int s.running_job);
       ("job_started", `Float s.job_started);
       ("nodes", `Int s.nodes);
       ("queued", `Int s.queued);
       ("updated", `Float s.updated);
     ]
    @ sentence_field)

let encode_ack ~job_id ~queued ~starting =
  `Assoc
    [
      ("job", `Int job_id);
      ("queued", `Int queued);
      ("starting", `Bool starting);
    ]

let encode_cancelled ~cancelled ~running =
  match cancelled with
  | Some job_id -> `Assoc [ ("cancelled", `Int job_id) ]
  | None -> `Assoc [ ("cancelled", `Null); ("running", `Int running) ]

let encode_withdrawn_status ~job_id ~state =
  `Assoc [ ("job", `Int job_id); ("state", `String state) ]

let encode_stopped () =
  `Assoc [ ("stopped", `Bool true) ]

let job_header ~job_id ~cmd =
  [ ("job", `Int job_id); ("cmd", `String cmd) ]

let encode_job_withdrawn ~job_id ~cmd =
  `Assoc (job_header ~job_id ~cmd @ [ ("withdrawn", `Bool true) ])

let encode_job_startup_error ~job_id ~cmd ~seconds msg =
  `Assoc
    (job_header ~job_id ~cmd
    @ [
        ("seconds", `Float seconds);
        ("nodes", `Int 0);
        ("error", `String ("the session did not start: " ^ msg));
      ])

let encode_job_reply ~job_id ~cmd ~seconds ~nodes reply =
  `Assoc
    (job_header ~job_id ~cmd
    @ [ ("seconds", `Float seconds); ("nodes", `Int nodes) ]
    @ session_reply_fields reply)
