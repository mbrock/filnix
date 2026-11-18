(* The rq worker keeps one Rocq session alive behind a Unix socket.

   The rq command line starts one worker per session and sends it one
   request per connection. Rocq is sequential, blocks whatever runs it,
   and works only in the main domain: Pp.string_of_ppcmds writes to
   Format.str_formatter, which belongs to the main domain, and reads back
   the calling domain's buffer, so in any other domain every string Rocq
   prints comes out empty. The worker therefore runs the session's jobs
   one at a time in the main domain, and serves the socket from a second
   domain, which stays free while Rocq is busy and answers status, cancel
   and withdraw requests at once.

   The server domain also owns the session's files beside the socket.
   status.json names the running job and its current sentence, log
   receives every message in full, transcript.v receives every scratch
   sentence the session commits, and job-N.json keeps each job's result,
   so that rq can come back for it after it stopped waiting.

     rq-worker SESSION_DIR [rocq options...]    (with RQ_FILE set to the proof file)

   SIGINT interrupts the running sentence, and only when a cancel asked for
   it. The server domain blocks the signal, because OCaml runs a signal
   handler only in a thread that has the signal unblocked; Sys.Break thus
   lands in Rocq and never in the server's event loop. *)

open Eio.Std
module J = Yojson.Safe

(* ## Jobs *)

type state = Queued | Running | Withdrawn | Finished

let state_name = function
  | Queued -> "queued"
  | Running -> "running"
  | Withdrawn -> "withdrawn"
  | Finished -> "finished"

type job = {
  id : int;
  cmd : string;
  request : Session.request;
  state : state Atomic.t;
  reply : J.t Promise.t;
  resolve : J.t Promise.u;
}

(* What the server hears from Rocq. *)
type event =
  | Ready
  | Failed_to_start of string
  | Started of int
  | Finished_job of { job : job; reply : J.t; nodes : int }
      (** The server keeps the result, then hands it to the waiting client. *)
  | Rocq of Session.event

(* What the two domains share: the job queue, the event stream, and two
   counters that the server reads to answer status and cancel requests. *)
type shared = {
  jobs : job Eio.Stream.t;
  events : event Eio.Stream.t;
  pending : int Atomic.t;  (** jobs queued or running, Rocq's start-up included *)
  current : int Atomic.t;  (** the running job, or 0 *)
}

(* ## The Rocq side, in the main domain *)

let run_job shared session job =
  let head = [ ("job", `Int job.id); ("cmd", `String job.cmd) ] in
  if not (Atomic.compare_and_set job.state Queued Running) then (`Assoc (head @ [ ("withdrawn", `Bool true) ]), 0)
  else begin
    let started = Unix.gettimeofday () in
    let fields, nodes =
      match session with
      | Error msg -> ([ ("error", `String ("the session did not start: " ^ msg)) ], 0)
      | Ok session ->
          Session.begin_job ();
          Atomic.set shared.current job.id;
          Eio.Stream.add shared.events (Started job.id);
          let fields = Session.handle session job.request in
          Atomic.set shared.current 0;
          (fields, Session.nodes session)
    in
    Atomic.set job.state Finished;
    (`Assoc (head @ [ ("seconds", `Float (Unix.gettimeofday () -. started)); ("nodes", `Int nodes) ] @ fields), nodes)
  end

(* Start Rocq, then run jobs as they arrive. Coqinit sets its own Ctrl-C
   handler, so ours goes in after it. *)
let rocq shared ~file ~args =
  let session =
    match Session.create ~file ~args ~emit:(fun e -> Eio.Stream.add shared.events (Rocq e)) with
    | session ->
        Eio_unix.set_signal Sys.sigint (Signal_handle Session.on_sigint);
        Eio.Stream.add shared.events Ready;
        Ok session
    | exception e ->
        let msg = Printexc.to_string e in
        Eio.Stream.add shared.events (Failed_to_start msg);
        Error msg
  in
  Atomic.decr shared.pending;
  let rec loop () =
    let job = Eio.Stream.take shared.jobs in
    let reply, nodes = run_job shared session job in
    if Atomic.get job.state = Finished then Atomic.decr shared.pending;
    Eio.Stream.add shared.events (Finished_job { job; reply; nodes });
    loop ()
  in
  loop ()

(* ## The server, in its own domain *)

type server = {
  shared : shared;
  dir : Eio.Fs.dir_ty Eio.Path.t;
  clock : float Eio.Time.clock_ty r;
  waiting : (int, job) Hashtbl.t;  (** unfinished jobs, by number *)
  mutable next_id : int;
  mutable state : string;
  mutable job_started : float;
  mutable sentence : (string * int * string * float) option;
  mutable nodes : int;
}

let write_atomic t name s =
  let tmp = Eio.Path.(t.dir / (name ^ ".tmp")) in
  Eio.Path.save ~create:(`Or_truncate 0o644) tmp s;
  Eio.Path.rename tmp Eio.Path.(t.dir / name)

let append t name s = Eio.Path.save ~append:true ~create:(`If_missing 0o644) Eio.Path.(t.dir / name) s

let status_json t =
  let sentence =
    match t.sentence with
    | Some (origin, line, text, started) ->
        [ ( "sentence",
            `Assoc
              [ ("origin", `String origin); ("line", `Int line); ("text", `String text);
                ("started", `Float started) ] ) ]
    | None -> []
  in
  `Assoc
    ([ ("state", `String t.state); ("pid", `Int (Unix.getpid ())); ("job", `Int (Atomic.get t.shared.current));
       ("job_started", `Float t.job_started); ("nodes", `Int t.nodes);
       ("queued", `Int (max 0 (Atomic.get t.shared.pending - 1))); ("updated", `Float (Eio.Time.now t.clock)) ]
    @ sentence)

let write_status t = write_atomic t "status.json" (J.to_string (status_json t) ^ "\n")

(* Follow Rocq's events, keeping the status and the files up to date. This
   is the only fiber that writes them, so their order is the order in
   which things happened. *)
let rec follow t =
  (match Eio.Stream.take t.shared.events with
   | Ready -> t.state <- "idle"; write_status t
   | Failed_to_start msg -> t.state <- "failed"; append t "log" (msg ^ "\n"); write_status t
   | Started _ -> t.state <- "busy"; t.job_started <- Eio.Time.now t.clock; t.sentence <- None; write_status t
   | Finished_job { job; reply; nodes } ->
       t.state <- "idle";
       t.nodes <- nodes;
       t.sentence <- None;
       write_status t;
       write_atomic t (Printf.sprintf "job-%d.json" job.id) (J.to_string reply ^ "\n");
       write_atomic t "last-job" (string_of_int job.id ^ "\n");
       Hashtbl.remove t.waiting job.id;
       Promise.resolve job.resolve reply
   | Rocq (Sentence { origin; line; text }) ->
       t.sentence <- Some (origin, line, text, Eio.Time.now t.clock);
       write_status t
   | Rocq (Log s) -> append t "log" (if String.ends_with ~suffix:"\n" s then s else s ^ "\n")
   | Rocq (Transcript s) -> append t "transcript.v" s
   | Rocq (Dropped s) -> write_atomic t "dropped.v" s);
  follow t

(* Queue a job. [follow] keeps its result in job-N.json when it ends, so
   the result is kept whether or not the client that asked for it is
   still waiting. *)
let submit t ~cmd request =
  t.next_id <- t.next_id + 1;
  let reply, resolve = Promise.create () in
  let job = { id = t.next_id; cmd; request; state = Atomic.make Queued; reply; resolve } in
  let ahead = Atomic.fetch_and_add t.shared.pending 1 - if t.state = "starting" then 1 else 0 in
  Hashtbl.replace t.waiting job.id job;
  Eio.Stream.add t.shared.jobs job;
  (job, ahead)

let cancel t target =
  let cur = Atomic.get t.shared.current in
  if cur = 0 || Stdlib.Option.fold ~none:false ~some:(( <> ) cur) target then
    `Assoc [ ("cancelled", `Null); ("running", `Int cur) ]
  else begin
    if Session.request_cancel () then Unix.kill (Unix.getpid ()) Sys.sigint;
    `Assoc [ ("cancelled", `Int cur) ]
  end

let withdraw t id =
  match Hashtbl.find_opt t.waiting id with
  | None -> `Assoc [ ("job", `Int id); ("state", `String "finished") ]
  | Some job ->
      if Atomic.compare_and_set job.state Queued Withdrawn then Atomic.decr t.shared.pending;
      `Assoc [ ("job", `Int id); ("state", `String (state_name (Atomic.get job.state))) ]

let error msg = `Assoc [ ("error", `String msg) ]

(* Serve one connection. A session request is answered twice: at once with
   its job number and the number of jobs ahead of it, and with its result
   when the job ends. A client that hangs up while its job still waits in
   the queue withdraws it, unless it detached the job; a job that already
   runs goes on, because a client that stopped waiting did not ask the job
   to stop. *)
let serve ~stop t flow _addr =
  let r = Eio.Buf_read.of_flow flow ~max_size:(256 * 1024 * 1024) in
  let send json = Eio.Flow.copy_string (J.to_string json ^ "\n") flow in
  match Protocol.parse (J.from_string (Eio.Buf_read.line r)) with
  | exception (Yojson.Json_error msg | Failure msg) -> send (error msg)
  | exception End_of_file -> ()
  | Error msg -> send (error msg)
  | Ok Status -> send (status_json t)
  | Ok (Cancel target) -> send (cancel t target)
  | Ok (Withdraw id) -> send (withdraw t id)
  | Ok Stop -> send (`Assoc [ ("stopped", `Bool true) ]); Promise.resolve stop ()
  | Ok (Session { cmd; request; detach }) ->
      let job, ahead = submit t ~cmd request in
      send (`Assoc [ ("job", `Int job.id); ("queued", `Int ahead); ("starting", `Bool (t.state = "starting")) ]);
      if not detach then
        Fiber.first
          (fun () -> send (Promise.await job.reply))
          (fun () -> if Eio.Buf_read.at_end_of_input r then ignore (withdraw t job.id) else Fiber.await_cancel ())

(* Serve the socket until a stop request. A running sentence cannot be
   cancelled from here, so the worker then exits rather than wait for Rocq
   to finish. *)
let server env shared ~dir =
  ignore (Thread.sigmask SIG_BLOCK [ Sys.sigint ]);
  Switch.run @@ fun sw ->
  let t =
    { shared; dir = Eio.Path.(Eio.Stdenv.fs env / dir); clock = Eio.Stdenv.clock env;
      waiting = Hashtbl.create 16; next_id = 0; state = "starting"; job_started = 0.; sentence = None; nodes = 0 }
  in
  write_status t;
  let sock = Eio.Path.(t.dir / "sock") in
  Eio.Path.unlink ~missing_ok:true sock;
  let listening = Eio.Net.listen ~sw ~backlog:16 (Eio.Stdenv.net env) (`Unix (Eio.Path.native_exn sock)) in
  let stopped, stop = Promise.create () in
  Fiber.fork_daemon ~sw (fun () -> follow t);
  Fiber.first
    (fun () -> Promise.await stopped)
    (fun () ->
      Eio.Net.run_server listening (serve ~stop t)
        ~on_error:(fun e -> append t "log" ("[rq-worker] " ^ Printexc.to_string e ^ "\n")));
  t.state <- "stopped";
  write_status t;
  Eio.Path.unlink ~missing_ok:true sock;
  exit 0

let () =
  let dir = Sys.argv.(1) in
  let args = Array.to_list (Array.sub Sys.argv 2 (Array.length Sys.argv - 2)) in
  let file = Stdlib.Option.value (Sys.getenv_opt "RQ_FILE") ~default:"" in
  Sys.set_signal Sys.sigpipe Signal_ignore;
  Eio_main.run @@ fun env ->
  let shared =
    { jobs = Eio.Stream.create max_int; events = Eio.Stream.create 4096; pending = Atomic.make 1;
      current = Atomic.make 0 }
  in
  Fiber.both
    (fun () -> Eio.Domain_manager.run (Eio.Stdenv.domain_mgr env) (fun () -> server env shared ~dir))
    (fun () -> rocq shared ~file ~args)
