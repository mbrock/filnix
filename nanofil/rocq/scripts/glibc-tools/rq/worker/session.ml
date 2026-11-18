(* A session is one Rocq proof state that a worker keeps between requests.

   Rocq keeps its proof state in global variables, so this module is plain
   sequential Rocq code that knows nothing about sockets, fibers or files:
   rq_worker.ml runs it in a domain of its own and talks to it through
   [handle] and the [emit] callback. Every sentence the session runs keeps
   the Vernacstate.t snapshot that follows it. Rolling back is choosing an
   earlier snapshot, a try starts each candidate from the same snapshot,
   and a reload replays only the sentences after the first edited byte of
   the file. *)

module J = Yojson.Safe

(* ## What a session reports while it runs *)

type event =
  | Sentence of { origin : string; line : int; text : string }
      (** A sentence is about to run. *)
  | Log of string  (** A message for the session's log. *)
  | Transcript of string  (** A scratch sentence was committed. *)
  | Dropped of string  (** Reload dropped these scratch sentences. *)

(* ## Requests *)

type target = Line of int | Theorem of string | End

type request =
  | Load of target  (** Bring the session to the target in the file on disk. *)
  | Step of string  (** Run sentences, keeping all before the first failure. *)
  | Try of { candidates : string list; commit : bool }
  | Check  (** Qed in a throwaway state. *)
  | Back of int  (** Drop the last committed sentences. *)
  | Goals
  | Nodes

(* ## Interrupts

   An interrupt is SIGINT, which Rocq turns into Sys.Break at its next safe
   point; its own interrupt flag is not checked during reduction, so it
   cannot stop a long vm_compute or lazy. The handler raises only while a
   sentence runs and a cancel was asked for. A cancel that arrives between
   sentences is seen by [run] before the next one, and a stale signal that
   arrives after the job ends does nothing. *)

let armed = Atomic.make false
let cancel_requested = Atomic.make false

let on_sigint _ =
  if Atomic.get armed && Atomic.get cancel_requested then raise Sys.Break

(* Ask the running job to stop, and say whether a sentence is running, in
   which case the caller sends SIGINT. The flag is set before [armed] is
   read, and [run] arms before it reads the flag, so either the caller
   signals or [run] stops by itself. *)
let request_cancel () =
  Atomic.set cancel_requested true;
  Atomic.get armed

let begin_job () = Atomic.set cancel_requested false

(* ## The session *)

type node = {
  text : string;
  origin : string;  (** "file", or where a scratch sentence came from *)
  bp : int;
  ep : int;
  line : int;
  st : Vernacstate.t;
  ms : float;
}

type t = {
  file : string;
  emit : event -> unit;
  start : Vernacstate.t;  (** the state before the file's first sentence *)
  messages : (string * string) list ref;  (** of the sentence that runs *)
  loaded : (string * float) list ref;  (** .vo files with their mtimes *)
  mutable nodes : node list;  (** newest first *)
  mutable file_text : string;
}

let now = Unix.gettimeofday
let nodes t = List.length t.nodes
let tip t = match t.nodes with n :: _ -> n.st | [] -> t.start
let restore t = Vernacstate.unfreeze_full_state (tip t)

let level_name = function
  | Feedback.Debug -> "debug"
  | Info -> "info"
  | Notice -> "notice"
  | Warning -> "warning"
  | Error -> "error"

(* Start Rocq with the given command-line options. Rocq reports Show
   output, warnings and the files Require loads as feedback. The feeder
   collects the messages of the sentence being run, and remembers every
   .vo file with its modification time, so that a reload can tell when
   warm.sh or one.sh replaced an import. *)
let create ~file ~args ~emit =
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
  let messages = ref [] and loaded = ref [] in
  Feedback.warn_no_listeners := false;
  ignore
    (Feedback.add_feeder (fun fb ->
         match fb.Feedback.contents with
         | Message (Debug, _, _, _) -> ()
         | Message (lvl, _, _, pp) -> messages := (level_name lvl, Pp.string_of_ppcmds pp) :: !messages
         | FileLoaded (_, f) -> (
             match Unix.stat f with
             | st -> loaded := (f, st.Unix.st_mtime) :: !loaded
             | exception Unix.Unix_error _ -> ())
         | _ -> ()));
  let top = Coqinit.dirpath_of_top opts.config.logic.toplevel_name in
  Coqinit.start_library ~intern:Vernacinterp.fs_intern ~top (Coqargs.injection_commands opts);
  let start = Vernacstate.freeze_full_state () in
  { file; emit; start; messages; loaded; nodes = []; file_text = "" }

let changed_imports t =
  List.filter_map
    (fun (f, mtime) ->
      match Unix.stat f with
      | st when st.Unix.st_mtime = mtime -> None
      | _ | (exception Unix.Unix_error _) -> Some f)
    !(t.loaded)

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
        let body = match get_value decl with Some b -> `String (pr env sigma b) | None -> `Null in
        `Assoc
          [ ("name", `String (Names.Id.to_string (get_id decl)));
            ("type", `String (pr env sigma (get_type decl)));
            ("body", body) ]
      in
      `Assoc
        [ ("id", `String (Pp.string_of_ppcmds (Evar.print g)));
          ("hyps", `List (List.rev_map hyp (Evd.evar_context info)));
          ("concl", `String (pr env sigma (Evd.evar_concl info))) ]
  | exception Not_found -> `Assoc [ ("id", `String "?"); ("hyps", `List []); ("concl", `String "?") ]

let proof_of st =
  Option.map
    (fun stk -> Declare.Proof.get (Vernacstate.LemmaStack.get_top stk))
    st.Vernacstate.interp.lemmas

(* The goals of state st: the focused goals in full, or only the first
   when full is false, and the counts of unfocused, shelved and given-up
   goals. *)
let goals_json ?(full = true) st =
  match proof_of st with
  | None -> `Null
  | Some p ->
      Vernacstate.unfreeze_full_state st;
      let { Proof.sigma; goals; stack; name; _ } = Proof.data p in
      let shelved = List.filter (Evd.is_undefined sigma) (Evd.shelf sigma) in
      let unfocused = List.fold_left (fun n (l, r) -> n + List.length l + List.length r) 0 stack in
      let shown = if full then goals else List.filteri (fun i _ -> i = 0) goals in
      `Assoc
        [ ("proof", `String (Names.Id.to_string name));
          ("focused", `Int (List.length goals));
          ("goals", `List (List.map (goal_json sigma) shown));
          ("unfocused", `Int unfocused);
          ("shelved", `Int (List.length shelved));
          ("shelved_goals", `List (if full then List.map (goal_json sigma) shelved else []));
          ("given_up", `Int (Evar.Set.cardinal (Evd.given_up sigma))) ]

(* ## Running sentences *)

let query_re =
  Str.regexp
    "^[ \t\n]*\\(Show\\|Search\\|SearchPattern\\|SearchRewrite\\|Check\\|About\\|Print\\|Locate\\|Compute\\|Eval\\|Fail\\|Time Show\\)\\b"

let is_query text = Str.string_match query_re text 0

let theorem_re name =
  Str.regexp
    ("^[ \t\n]*\\(#\\[[^]]*\\][ \t\n]*\\)?\\(Local[ \t\n]+\\|Global[ \t\n]+\\|Program[ \t\n]+\\)*"
   ^ "\\(Lemma\\|Theorem\\|Corollary\\|Proposition\\|Fact\\|Remark\\|Example\\|Definition\\|Instance\\|Fixpoint\\)[ \t\n]+"
   ^ Str.quote name ^ "\\b")

let proof_re = Str.regexp "^[ \t\n]*Proof\\b"

let line_of_offset s off =
  let n = ref 1 in
  for i = 0 to min off (String.length s) - 1 do
    if s.[i] = '\n' then incr n
  done;
  !n

let bol_of_offset s off =
  let rec go i = if i <= 0 then 0 else if s.[i - 1] = '\n' then i else go (i - 1) in
  go (min off (String.length s))

(* The offset of the end of line n of s. *)
let end_of_line s n =
  let rec go i l =
    if i >= String.length s then i
    else if s.[i] = '\n' then if l = n then i else go (i + 1) (l + 1)
    else go (i + 1) l
  in
  go 0 1

type stop =
  | Done
  | Reached of string  (** the target that ended the run *)
  | Failed of { kind : string; text : string; bp : int; ep : int; msg : string }

type outcome = { committed : node list; stop : stop; msgs : (string * string) list }

exception Interrupted

(* Run one parsed sentence from state st with interrupts armed. *)
let interp_armed vc st =
  Fun.protect ~finally:(fun () -> Atomic.set armed false) @@ fun () ->
  Atomic.set armed true;
  if Atomic.get cancel_requested then raise Interrupted;
  Vernacinterp.interp ~intern:Vernacinterp.fs_intern ~st vc

(* Run the sentences of src from offset off, starting from state st, until
   the text ends, the target is reached, a sentence fails or the job is
   cancelled. The result lists the nodes that ran, oldest first. A query
   such as Show keeps its messages but adds no node unless keep_queries is
   set. The parser needs the state of the sentence before, so parsing and
   running alternate. *)
let run ?(keep_queries = false) t ~origin ~target st src off =
  let all_msgs = ref [] in
  let fname = if origin = "file" then Loc.InFile { dirpath = None; file = t.file } else Loc.ToplevelInput in
  let loc = Loc.create fname (line_of_offset src off) (bol_of_offset src off) off off in
  let pa =
    Procq.Parsable.make ~loc
      (Gramlib.Stream.of_string ~offset:off (String.sub src off (String.length src - off)))
  in
  let target_off = match target with Line n -> end_of_line src n | _ -> max_int in
  let interrupted text bp ep = Failed { kind = "interrupted"; text; bp; ep; msg = "interrupted by rq cancel" } in
  let rec loop st acc ~after_statement =
    let finish stop = (List.rev acc, stop) in
    let last_ep = match acc with n :: _ -> n.ep | [] -> off in
    Vernacstate.unfreeze_full_state st;
    let pm = if proof_of st <> None then Some (Synterp.get_default_proof_mode ()) else None in
    let error kind bp ep text e =
      let e, info = Exninfo.capture e in
      let bp, ep = match Loc.get_loc info with Some l -> Loc.unloc l | None -> (bp, ep) in
      finish (Failed { kind; text; bp; ep; msg = Pp.string_of_ppcmds (CErrors.iprint (e, info)) })
    in
    if Atomic.get cancel_requested then finish (interrupted "" last_ep last_ep)
    else
      match Procq.Entry.parse (Pvernac.main_entry pm) pa with
      | exception e when CErrors.noncritical e -> error "syntax" last_ep last_ep "" e
      | None -> finish (if after_statement then Reached "theorem" else Done)
      | Some vc ->
          let bp, ep = match vc.CAst.loc with Some l -> Loc.unloc l | None -> (off, off) in
          let text = String.sub src bp (ep - bp) in
          let line = line_of_offset src bp in
          if (match target with Line _ -> ep > target_off | _ -> false) then
            finish (Reached (match target with Line n -> "line " ^ string_of_int n | _ -> ""))
          else if after_statement && not (Str.string_match proof_re text 0) then finish (Reached "theorem")
          else begin
            t.emit (Sentence { origin; line; text });
            t.messages := [];
            let started = now () in
            match interp_armed vc st with
            | st' ->
                let msgs = List.rev !(t.messages) in
                all_msgs := List.rev_append msgs !all_msgs;
                List.iter (fun (lvl, m) -> t.emit (Log (Printf.sprintf "[%s] %s" lvl m))) msgs;
                let n = { text; origin; bp; ep; line; st = st'; ms = (now () -. started) *. 1000. } in
                let acc = if is_query text && not keep_queries then acc else n :: acc in
                if after_statement then (List.rev acc, Reached "theorem")
                else
                  let hit =
                    match target with Theorem name -> Str.string_match (theorem_re name) text 0 | _ -> false
                  in
                  loop st' acc ~after_statement:hit
            | exception (Sys.Break | Interrupted) ->
                Vernacstate.Interp.invalidate_cache ();
                finish (interrupted text bp ep)
            | exception e when CErrors.noncritical e ->
                all_msgs := List.rev_append (List.rev !(t.messages)) !all_msgs;
                error "error" bp ep text e
          end
  in
  let committed, stop = loop st [] ~after_statement:false in
  (match stop with Failed { kind; msg; _ } -> t.emit (Log (Printf.sprintf "[%s] %s" kind msg)) | _ -> ());
  { committed; stop; msgs = List.rev !all_msgs }

(* ## Replies *)

let pos_json src bp ep =
  `Assoc
    [ ("line", `Int (line_of_offset src bp)); ("col", `Int (bp - bol_of_offset src bp + 1));
      ("end_line", `Int (line_of_offset src ep)); ("end_col", `Int (ep - bol_of_offset src ep + 1));
      ("bp", `Int bp); ("ep", `Int ep) ]

let node_json src n =
  `Assoc
    [ ("origin", `String n.origin); ("text", `String n.text); ("ms", `Float n.ms);
      ("range", pos_json src n.bp n.ep) ]

let stop_json src = function
  | Done -> `Assoc [ ("kind", `String "done") ]
  | Reached target -> `Assoc [ ("kind", `String "reached"); ("target", `String target) ]
  | Failed { kind; text; bp; ep; msg } ->
      `Assoc
        [ ("kind", `String kind); ("text", `String text); ("message", `String msg);
          ("range", pos_json src bp ep) ]

let outcome_fields ?(goals = true) src o st =
  [ ("committed", `List (List.map (node_json src) o.committed));
    ("stop", stop_json src o.stop);
    ("messages", `List (List.map (fun (l, m) -> `Assoc [ ("level", `String l); ("text", `String m) ]) o.msgs));
    ("goals", if goals then goals_json ~full:false st else `Null) ]

let commit t o =
  t.nodes <- List.rev_append o.committed t.nodes;
  List.iter
    (fun n -> if n.origin <> "file" then t.emit (Transcript (Printf.sprintf "(* rq %s:%d *) %s\n" n.origin n.line n.text)))
    o.committed

let is_interrupt = function Failed { kind = "interrupted"; _ } -> true | _ -> false

(* ## Handling requests *)

let read_file f = In_channel.with_open_bin f In_channel.input_all

(* Bring the session to the target in the file on disk. The nodes that end
   before the first byte where the file changed are kept with their
   snapshots, and the rest of the file runs again from there. When a
   loaded .vo changed, the reply asks for a restart instead, because the
   kept snapshots embed the old objects. *)
let load t target =
  match changed_imports t with
  | _ :: _ as changed -> [ ("restart", `List (List.map (fun f -> `String f) changed)) ]
  | [] ->
      let text = read_file t.file in
      let d =
        let old = t.file_text in
        let n = min (String.length old) (String.length text) in
        let rec go i = if i < n && old.[i] = text.[i] then go (i + 1) else i in
        go 0
      in
      let scratch, rest = List.partition (fun n -> n.origin <> "file") t.nodes in
      if scratch <> [] then t.emit (Dropped (String.concat "\n" (List.rev_map (fun n -> n.text) scratch) ^ "\n"));
      let target_off = match target with Line n -> end_of_line text n | _ -> max_int in
      let kept = List.filter (fun n -> n.ep < d && n.ep <= target_off) rest in
      (* For a theorem target, cut back to before its statement, so that the
         run stops after the statement again. *)
      let kept =
        match target with
        | Theorem name ->
            let is_stmt n = Str.string_match (theorem_re name) n.text 0 in
            let rec cut = function [] -> [] | n :: older -> if is_stmt n then older else cut older in
            if List.exists is_stmt kept then cut kept else kept
        | _ -> kept
      in
      t.nodes <- kept;
      t.file_text <- text;
      let off = match kept with n :: _ -> n.ep | [] -> 0 in
      let o = run t ~origin:"file" ~target (tip t) text off in
      commit t o;
      restore t;
      [ ("reused", `Int (List.length kept)); ("dropped_scratch", `Int (List.length scratch)) ]
      @ outcome_fields text o (tip t)

let step t text =
  let o = run t ~origin:"step" ~target:End (tip t) text 0 in
  commit t o;
  restore t;
  outcome_fields text o (tip t)

(* Run each candidate from the current snapshot and report how far it got.
   The session stays where it was unless commit is set, in which case the
   first candidate that runs to its end is kept. An interrupt ends the
   whole try. *)
let try_ t candidates ~commit:keep =
  let base = tip t in
  let rec go i kept acc = function
    | [] -> (kept, List.rev acc, false)
    | text :: rest ->
        let o = run t ~keep_queries:true ~origin:(Printf.sprintf "try%d" i) ~target:End base text 0 in
        let st = match List.rev o.committed with n :: _ -> n.st | [] -> base in
        let ok = match o.stop with Done | Reached _ -> true | Failed _ -> false in
        let r = `Assoc ([ ("candidate", `String text); ("ok", `Bool ok) ] @ outcome_fields text o st) in
        Vernacstate.unfreeze_full_state base;
        let kept = if keep && ok && kept = None then Some o else kept in
        if is_interrupt o.stop then (kept, List.rev (r :: acc), true) else go (i + 1) kept (r :: acc) rest
  in
  let kept, results, interrupted = go 1 None [] candidates in
  Option.iter (fun o -> commit t { o with committed = List.filter (fun n -> not (is_query n.text)) o.committed }) kept;
  restore t;
  [ ("results", `List results); ("committed_candidate", `Bool (kept <> None)) ]
  @ if interrupted then [ ("interrupted", `Bool true) ] else []

(* Try Qed in a throwaway state, after reporting the goals that would make
   it fail. *)
let check t =
  let base = tip t in
  let goals = goals_json ~full:false base in
  let o = run t ~origin:"check" ~target:End base "Qed." 0 in
  restore t;
  [ ("ok", `Bool (o.stop = Done)); ("goals_before", goals) ] @ outcome_fields ~goals:false "Qed." o base

let back t n =
  let rec drop k l = if k = 0 then l else match l with [] -> [] | _ :: l -> drop (k - 1) l in
  let dropped = min n (List.length t.nodes) in
  t.nodes <- drop n t.nodes;
  restore t;
  [ ("dropped", `Int dropped); ("goals", goals_json ~full:false (tip t)) ]

let handle t request =
  try
    match request with
    | Load target -> load t target
    | Step text -> step t text
    | Try { candidates; commit } -> try_ t candidates ~commit
    | Check -> check t
    | Back n -> back t n
    | Goals -> [ ("goals", goals_json (tip t)) ]
    | Nodes ->
        let src n = if n.origin = "file" then t.file_text else n.text in
        [ ("nodes", `List (List.rev_map (fun n -> node_json (src n) n) t.nodes)) ]
  with
  | Sys.Break | Interrupted ->
      restore t;
      [ ("interrupted", `Bool true) ]
  | e ->
      restore t;
      [ ("error", `String (Printexc.to_string e)) ]
