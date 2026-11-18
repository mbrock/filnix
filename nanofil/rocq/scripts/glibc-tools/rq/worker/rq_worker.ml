(* The rq worker keeps one Rocq session alive behind a Unix socket.

   The rq command line starts one worker per session and sends it one
   request per connection. The worker runs requests one at a time, in the
   order it accepts them, so a session has a single execution queue. A
   request is one JSON object on one line, and the reply is one JSON line
   saying which job number the worker gave it, then one JSON line with the
   result.

   The worker is linked against the same Rocq as one.sh and calls
   Rocq's parser and interpreter directly. Every executed sentence keeps
   the Vernacstate.t snapshot that follows it, so rolling back is choosing
   an earlier snapshot, a try starts each candidate from the same
   snapshot, and a reload replays only the sentences after the first
   edited byte of the file.

   The worker also writes three files beside its socket, so that rq can
   report on a busy session without waiting for it. status.json names the
   running job and its current sentence, log receives every message in
   full, and transcript.v receives every sentence the session commits.

     rq-worker SESSION_DIR [rocq options...]

   SIGINT interrupts the running sentence. The session returns to the
   snapshot before that sentence and keeps everything committed so far. *)

open Yojson.Safe

let session_dir = Sys.argv.(1)
let rocq_args = Array.to_list (Array.sub Sys.argv 2 (Array.length Sys.argv - 2))
let path name = Filename.concat session_dir name
let now () = Unix.gettimeofday ()

(* ## Files beside the socket *)

let append name s =
  let oc = open_out_gen [ Open_append; Open_creat; Open_wronly ] 0o644 (path name) in
  output_string oc s;
  close_out oc

let write_atomic name s =
  let tmp = path (name ^ ".tmp") in
  let oc = open_out tmp in
  output_string oc s;
  close_out oc;
  Sys.rename tmp (path name)

let log s = append "log" (if s = "" || s.[String.length s - 1] = '\n' then s else s ^ "\n")

(* ## Messages and loaded files

   Rocq reports Show output, warnings and the files Require loads as
   feedback. The feeder collects the messages of the sentence being run,
   and remembers every .vo file with its modification time, so that a
   reload can tell when warm.sh or one.sh replaced an import. *)

let messages : (string * string) list ref = ref []
let loaded : (string * float) list ref = ref []

let level_name = function
  | Feedback.Debug -> "debug"
  | Feedback.Info -> "info"
  | Feedback.Notice -> "notice"
  | Feedback.Warning -> "warning"
  | Feedback.Error -> "error"

let install_feeder () =
  Feedback.warn_no_listeners := false;
  ignore
    (Feedback.add_feeder (fun fb ->
         match fb.Feedback.contents with
         | Feedback.Message (Feedback.Debug, _, _, _) -> ()
         | Feedback.Message (lvl, _, _, pp) ->
             messages := (level_name lvl, Pp.string_of_ppcmds pp) :: !messages
         | Feedback.FileLoaded (_, file) -> (
             match Unix.stat file with
             | st -> loaded := (file, st.Unix.st_mtime) :: !loaded
             | exception Unix.Unix_error _ -> ())
         | _ -> ()))

let changed_imports () =
  List.filter
    (fun (file, mtime) ->
      match Unix.stat file with
      | st -> st.Unix.st_mtime <> mtime
      | exception Unix.Unix_error _ -> true)
    !loaded
  |> List.map fst

(* ## Starting Rocq *)

let init () =
  Coqinit.init_ocaml ();
  let usage =
    Boot.Usage.{ executable_name = "rq-worker"; extra_args = ""; extra_options = "" }
  in
  let opts, () =
    Coqinit.parse_arguments
      ~parse_extra:(fun _ extra -> ((), extra))
      ~initial_args:Coqargs.default rocq_args
  in
  Coqinit.init_runtime ~usage opts;
  Coqinit.init_document opts;
  install_feeder ();
  let top = Coqinit.dirpath_of_top opts.Coqargs.config.Coqargs.logic.Coqargs.toplevel_name in
  Coqinit.start_library ~intern:Vernacinterp.fs_intern ~top (Coqargs.injection_commands opts);
  Vernacstate.freeze_full_state ()

(* ## Goals

   A goal is printed as its hypotheses and its conclusion, each as Rocq
   prints it. The rq command line chooses which parts to show; an Iris
   conclusion includes the Iris context, which rq cuts off for its
   conclusion view. *)

let pr env sigma c = Pp.string_of_ppcmds (Printer.pr_leconstr_env env sigma c)

let goal_json sigma g =
  match Evd.find_undefined sigma g with
  | info ->
      let env = Evd.evar_filtered_env (Global.env ()) info in
      let hyp decl =
        let open Context.Named.Declaration in
        let name = Names.Id.to_string (get_id decl) in
        let body =
          match get_value decl with Some b -> `String (pr env sigma b) | None -> `Null
        in
        `Assoc [ ("name", `String name); ("type", `String (pr env sigma (get_type decl))); ("body", body) ]
      in
      `Assoc
        [
          ("id", `String (Pp.string_of_ppcmds (Evar.print g)));
          ("hyps", `List (List.rev_map hyp (Evd.evar_context info)));
          ("concl", `String (pr env sigma (Evd.evar_concl info)));
        ]
  | exception Not_found -> `Assoc [ ("id", `String "?"); ("hyps", `List []); ("concl", `String "?") ]

let proof_of st =
  match st.Vernacstate.interp.Vernacstate.Interp.lemmas with
  | None -> None
  | Some stk -> Some (Declare.Proof.get (Vernacstate.LemmaStack.get_top stk))

(* A summary of the goals in state st: the focused goals in full (or only
   their count when full is false), and the counts of unfocused, shelved
   and given-up goals. *)
let goals_json ?(full = true) st =
  match proof_of st with
  | None -> `Null
  | Some p ->
      Vernacstate.unfreeze_full_state st;
      let { Proof.sigma; goals; stack; name; _ } = Proof.data p in
      let undefined g = Evd.is_undefined sigma g in
      let shelved = List.filter undefined (Evd.shelf sigma) in
      let given_up = Evar.Set.cardinal (Evd.given_up sigma) in
      let unfocused = List.fold_left (fun n (l, r) -> n + List.length l + List.length r) 0 stack in
      let first =
        match goals with g :: _ when not full -> [ goal_json sigma g ] | _ -> []
      in
      `Assoc
        [
          ("proof", `String (Names.Id.to_string name));
          ("focused", `Int (List.length goals));
          ("goals", `List (if full then List.map (goal_json sigma) goals else first));
          ("unfocused", `Int unfocused);
          ("shelved", `Int (List.length shelved));
          ("shelved_goals", `List (if full then List.map (goal_json sigma) shelved else []));
          ("given_up", `Int given_up);
        ]

(* ## Sentences

   A node is one committed sentence with the snapshot after it. Nodes
   whose origin is the file carry byte offsets into the file text that
   produced them; nodes from scratch text carry offsets into that text. *)

type node = {
  text : string;
  origin : string;  (** "file" or the label of the scratch text *)
  bp : int;
  ep : int;
  line : int;
  st : Vernacstate.t;
  ms : float;
}

let init_state = ref (Obj.magic 0 : Vernacstate.t)
let nodes : node list ref = ref []  (* newest first *)
let file = ref ""
let file_text = ref ""
let job = ref 0
let job_started = ref 0.

let tip () = match !nodes with n :: _ -> n.st | [] -> !init_state

let status ?sentence state =
  let fields =
    [ ("state", `String state); ("pid", `Int (Unix.getpid ())); ("job", `Int !job);
      ("job_started", `Float !job_started); ("nodes", `Int (List.length !nodes));
      ("updated", `Float (now ())) ]
  in
  let fields =
    match sentence with
    | None -> fields
    | Some (origin, line, text, started) ->
        fields
        @ [ ("sentence", `Assoc [ ("origin", `String origin); ("line", `Int line);
                                  ("text", `String text); ("started", `Float started) ]) ]
  in
  write_atomic "status.json" (to_string (`Assoc fields) ^ "\n")

let query_re =
  Str.regexp
    "^[ \t\n]*\\(Show\\|Search\\|SearchPattern\\|SearchRewrite\\|Check\\|About\\|Print\\|Locate\\|Compute\\|Eval\\|Fail\\|Time Show\\)\\b"

let is_query text = Str.string_match query_re text 0

let line_of_offset s off =
  let n = ref 1 in
  for i = 0 to min off (String.length s) - 1 do
    if s.[i] = '\n' then incr n
  done;
  !n

let bol_of_offset s off =
  let rec go i = if i <= 0 then 0 else if s.[i - 1] = '\n' then i else go (i - 1) in
  go (min off (String.length s))

type stop =
  | Done
  | Reached of string  (** the target that ended the run *)
  | Failed of { kind : string; text : string; bp : int; ep : int; msg : string }

type target = Line of int | Theorem of string | End

let theorem_re name =
  Str.regexp
    ("^[ \t\n]*\\(#\\[[^]]*\\][ \t\n]*\\)?\\(Local[ \t\n]+\\|Global[ \t\n]+\\|Program[ \t\n]+\\)*"
   ^ "\\(Lemma\\|Theorem\\|Corollary\\|Proposition\\|Fact\\|Remark\\|Example\\|Definition\\|Instance\\|Fixpoint\\)[ \t\n]+"
   ^ Str.quote name ^ "\\b")

let proof_re = Str.regexp "^[ \t\n]*Proof\\b"

type outcome = { committed : node list; stop : stop; msgs : (string * string) list }

(* Run the sentences of src from offset off, starting from state st, until
   the text ends, the target is reached, a sentence fails or SIGINT
   arrives. The result lists the nodes that ran, oldest first. A query
   such as Show keeps its messages but adds no node unless keep_queries
   is set. The parser needs the state of the sentence before, so parsing
   and running alternate. *)
let run ?(keep_queries = false) ~origin ~target st src off =
  let all_msgs = ref [] in
  let fname = if origin = "file" then Loc.InFile { dirpath = None; file = !file } else Loc.ToplevelInput in
  let line0 = line_of_offset src off in
  let loc = Loc.create fname line0 (bol_of_offset src off) off off in
  let pa =
    Procq.Parsable.make ~loc
      (Gramlib.Stream.of_string ~offset:off (String.sub src off (String.length src - off)))
  in
  let target_off = match target with Line n ->
      (* the end of line n *)
      let rec go i l = if i >= String.length src then i else if src.[i] = '\n' then (if l = n then i else go (i + 1) (l + 1)) else go (i + 1) l in
      go 0 1
    | _ -> max_int in
  let rec loop st acc ~after_statement =
    Vernacstate.unfreeze_full_state st;
    let pm = if proof_of st <> None then Some (Synterp.get_default_proof_mode ()) else None in
    let fail kind bp ep text e =
      let e, info = Exninfo.capture e in
      let msg = Pp.string_of_ppcmds (CErrors.iprint (e, info)) in
      let bp, ep =
        match Loc.get_loc info with Some l -> Loc.unloc l | None -> (bp, ep)
      in
      (List.rev acc, Failed { kind; text; bp; ep; msg })
    in
    match Procq.Entry.parse (Pvernac.main_entry pm) pa with
    | exception Sys.Break -> (List.rev acc, Failed { kind = "interrupted"; text = ""; bp = off; ep = off; msg = "interrupted" })
    | exception e when CErrors.noncritical e ->
        let bp = match acc with n :: _ -> n.ep | [] -> off in
        fail "syntax" bp bp "" e
    | None -> (List.rev acc, if after_statement then Reached "theorem" else Done)
    | Some vc ->
        let bp, ep = match vc.CAst.loc with Some l -> Loc.unloc l | None -> (off, off) in
        let text = String.sub src bp (ep - bp) in
        let line = line_of_offset src bp in
        let stop_here =
          (match target with Line _ -> ep > target_off | _ -> false)
          || (after_statement && not (Str.string_match proof_re text 0))
        in
        if stop_here then (List.rev acc, Reached (match target with Line n -> "line " ^ string_of_int n | _ -> "theorem"))
        else begin
          let started = now () in
          status ~sentence:(origin, line, text, started) "busy";
          messages := [];
          match Vernacinterp.interp ~intern:Vernacinterp.fs_intern ~st vc with
          | st' ->
              let ms = (now () -. started) *. 1000. in
              let msgs = List.rev !messages in
              all_msgs := List.rev_append msgs !all_msgs;
              List.iter (fun (lvl, m) -> log (Printf.sprintf "[%s] %s" lvl m)) msgs;
              let n = { text; origin; bp; ep; line; st = st'; ms } in
              let acc = if is_query text && not keep_queries then acc else n :: acc in
              if after_statement then (List.rev acc, Reached "theorem")
              else
                let hit = match target with Theorem name -> Str.string_match (theorem_re name) text 0 | _ -> false in
                loop st' acc ~after_statement:hit
          | exception Sys.Break ->
              Vernacstate.Interp.invalidate_cache ();
              (List.rev acc, Failed { kind = "interrupted"; text; bp; ep; msg = "interrupted by SIGINT" })
          | exception e when CErrors.noncritical e ->
              all_msgs := List.rev_append (List.rev !messages) !all_msgs;
              fail "error" bp ep text e
        end
  in
  let committed, stop = loop st [] ~after_statement:false in
  (match stop with
   | Failed { kind; msg; _ } -> log (Printf.sprintf "[%s] %s" kind msg)
   | _ -> ());
  { committed; stop; msgs = List.rev !all_msgs }

(* ## Replies *)

let pos_json src bp ep =
  let l1 = line_of_offset src bp and l2 = line_of_offset src ep in
  `Assoc [ ("line", `Int l1); ("col", `Int (bp - bol_of_offset src bp + 1));
           ("end_line", `Int l2); ("end_col", `Int (ep - bol_of_offset src ep + 1));
           ("bp", `Int bp); ("ep", `Int ep) ]

let node_json src n =
  `Assoc [ ("origin", `String n.origin); ("text", `String n.text); ("ms", `Float n.ms);
           ("range", pos_json src n.bp n.ep) ]

let stop_json src = function
  | Done -> `Assoc [ ("kind", `String "done") ]
  | Reached t -> `Assoc [ ("kind", `String "reached"); ("target", `String t) ]
  | Failed { kind; text; bp; ep; msg } ->
      `Assoc [ ("kind", `String kind); ("text", `String text); ("message", `String msg);
               ("range", pos_json src bp ep) ]

let outcome_json ?(goals = true) src o st =
  [ ("committed", `List (List.map (node_json src) o.committed));
    ("stop", stop_json src o.stop);
    ("messages", `List (List.map (fun (l, m) -> `Assoc [ ("level", `String l); ("text", `String m) ]) o.msgs));
    ("goals", if goals then goals_json ~full:false st else `Null) ]

let record_transcript o =
  List.iter
    (fun n -> append "transcript.v" (Printf.sprintf "(* rq %s:%d *) %s\n" n.origin n.line n.text))
    o.committed

let commit o = nodes := List.rev_append o.committed !nodes

let restore () = Vernacstate.unfreeze_full_state (tip ())

(* ## Requests *)

let read_file f =
  let ic = open_in_bin f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let target_of req =
  let open Util in
  match member "theorem" req, member "line" req with
  | `String t, _ -> Theorem t
  | _, `Int n -> Line n
  | _ -> End

(* Bring the session to the target in the file on disk. The nodes that
   end before the first byte where the file changed are kept with their
   snapshots; the rest of the file is run again from there. Scratch nodes
   are dropped, and their text is saved in dropped.v so that it can be
   replayed with step. *)
let load req =
  let changed = changed_imports () in
  if changed <> [] then
    [ ("restart", `List (List.map (fun f -> `String f) changed)) ]
  else begin
    let text = read_file !file in
    let old = !file_text in
    let d =
      let n = min (String.length old) (String.length text) in
      let rec go i = if i < n && old.[i] = text.[i] then go (i + 1) else i in
      go 0
    in
    let scratch, rest = List.partition (fun n -> n.origin <> "file") !nodes in
    if scratch <> [] then
      write_atomic "dropped.v" (String.concat "\n" (List.rev_map (fun n -> n.text) scratch) ^ "\n");
    let target = target_of req in
    (* Keep a node only if it ends strictly before the first changed byte
       and, for a line target, before the end of that line. *)
    let target_off = match target with
      | Line n -> let rec go i l = if i >= String.length text then i else if text.[i] = '\n' then (if l = n then i else go (i+1) (l+1)) else go (i+1) l in go 0 1
      | _ -> max_int in
    let kept = List.filter (fun n -> n.ep < d && n.ep <= target_off) rest in
    (* For a theorem target, cut back to the statement if it is in the
       kept prefix, so that the run stops after it again. *)
    let kept =
      match target with
      | Theorem name ->
          let is_stmt n = Str.string_match (theorem_re name) n.text 0 in
          let rec cut = function [] -> [] | n :: older -> if is_stmt n then older else cut older in
          if List.exists is_stmt kept then cut kept else kept
      | _ -> kept
    in
    nodes := kept;
    file_text := text;
    let off = match kept with n :: _ -> n.ep | [] -> 0 in
    let o = run ~origin:"file" ~target (tip ()) text off in
    commit o;
    restore ();
    [ ("reused", `Int (List.length kept)); ("dropped_scratch", `Int (List.length scratch)) ]
    @ outcome_json text o (tip ())
  end

let scratch_text req =
  let open Util in
  (to_string (member "text" req), match member "label" req with `String s -> s | _ -> "scratch")

let step req =
  let text, label = scratch_text req in
  let o = run ~origin:label ~target:End (tip ()) text 0 in
  commit o;
  record_transcript o;
  restore ();
  outcome_json text o (tip ())

(* Run each candidate from the current snapshot and report how far it got.
   The session stays where it was unless commit is set, in which case the
   first candidate that runs to its end without an error is kept. *)
let try_ req =
  let open Util in
  let cands = List.map to_string (to_list (member "candidates" req)) in
  let keep = member "commit" req = `Bool true in
  let base = tip () in
  let kept = ref None in
  let results =
    List.mapi
      (fun i text ->
        let o = run ~keep_queries:true ~origin:(Printf.sprintf "try%d" (i + 1)) ~target:End base text 0 in
        let st = match List.rev o.committed with n :: _ -> n.st | [] -> base in
        let ok = match o.stop with Done | Reached _ -> true | Failed _ -> false in
        if keep && ok && !kept = None then kept := Some o;
        let r = `Assoc ([ ("candidate", `String text); ("ok", `Bool ok) ] @ outcome_json text o st) in
        Vernacstate.unfreeze_full_state base;
        (match o.stop with Failed { kind = "interrupted"; _ } -> raise Exit | _ -> ());
        r)
      cands
  in
  (match !kept with
   | Some o ->
       let o = { o with committed = List.filter (fun n -> not (is_query n.text)) o.committed } in
       commit o; record_transcript o
   | None -> ());
  restore ();
  [ ("results", `List results); ("committed_candidate", `Bool (!kept <> None)) ]

(* Try Qed in a throwaway state, after reporting the goals that would
   make it fail. *)
let check _ =
  let base = tip () in
  let goals = goals_json ~full:false base in
  let o = run ~origin:"check" ~target:End base "Qed." 0 in
  Vernacstate.unfreeze_full_state base;
  let ok = match o.stop with Done -> true | _ -> false in
  [ ("ok", `Bool ok); ("goals_before", goals) ] @ outcome_json ~goals:false "Qed." o base

let back req =
  let n = match Util.member "count" req with `Int n -> n | _ -> 1 in
  let rec drop k l = if k = 0 then l else match l with [] -> [] | _ :: t -> drop (k - 1) t in
  let dropped = min n (List.length !nodes) in
  nodes := drop n !nodes;
  restore ();
  [ ("dropped", `Int dropped); ("goals", goals_json ~full:false (tip ())) ]

let goals_req _ = [ ("goals", goals_json (tip ())) ]

let nodes_req _ =
  let src n = if n.origin = "file" then !file_text else n.text in
  [ ("nodes", `List (List.rev_map (fun n -> node_json (src n) n) !nodes)) ]

let handle req =
  let cmd = Util.(to_string (member "cmd" req)) in
  match cmd with
  | "load" -> load req
  | "step" -> step req
  | "try" -> try_ req
  | "check" -> check req
  | "back" -> back req
  | "goals" -> goals_req req
  | "nodes" -> nodes_req req
  | "stop" -> raise Exit
  | c -> [ ("error", `String ("unknown command " ^ c)) ]

(* ## The request loop *)

let send fd s =
  let s = s ^ "\n" in
  try ignore (Unix.write_substring fd s 0 (String.length s)) with Unix.Unix_error _ -> ()

let read_line fd =
  let buf = Buffer.create 4096 and b = Bytes.create 65536 in
  let rec go () =
    let n = Unix.read fd b 0 (Bytes.length b) in
    if n = 0 then ()
    else begin
      Buffer.add_subbytes buf b 0 n;
      if Bytes.index_opt (Bytes.sub b 0 n) '\n' = None then go ()
    end
  in
  go ();
  Buffer.contents buf

let () =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  file := (try Sys.getenv "RQ_FILE" with Not_found -> "");
  status "starting";
  init_state := init ();
  let sock = path "sock" in
  (try Unix.unlink sock with Unix.Unix_error _ -> ());
  let srv = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.bind srv (Unix.ADDR_UNIX sock);
  Unix.listen srv 16;
  status "idle";
  let stopping = ref false in
  while not !stopping do
    match Unix.accept srv with
    | exception Sys.Break -> ()
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> ()
    | fd, _ ->
        incr job;
        job_started := now ();
        let reply =
          match from_string (read_line fd) with
          | exception e -> `Assoc [ ("error", `String (Printexc.to_string e)) ]
          | req ->
              let cmd = Util.(to_string (member "cmd" req)) in
              send fd (to_string (`Assoc [ ("job", `Int !job) ]));
              log (Printf.sprintf "--- job %d: %s" !job (to_string req));
              status "busy";
              let fields =
                match handle req with
                | f -> f
                | exception Exit when cmd = "stop" -> stopping := true; [ ("stopped", `Bool true) ]
                | exception Exit -> restore (); [ ("interrupted", `Bool true) ]
                | exception Sys.Break -> restore (); [ ("interrupted", `Bool true) ]
                | exception e ->
                    restore ();
                    [ ("error", `String (Printexc.to_string e)) ]
              in
              `Assoc ([ ("job", `Int !job); ("cmd", `String cmd); ("seconds", `Float (now () -. !job_started));
                        ("nodes", `Int (List.length !nodes)) ] @ fields)
        in
        let s = to_string reply in
        write_atomic (Printf.sprintf "job-%d.json" !job) (s ^ "\n");
        write_atomic "last-job" (string_of_int !job ^ "\n");
        status (if !stopping then "stopped" else "idle");
        send fd s;
        (try Unix.close fd with Unix.Unix_error _ -> ())
  done;
  (try Unix.unlink sock with Unix.Unix_error _ -> ());
  exit 0
