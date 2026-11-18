(* Entrypoint of rq-worker, the persistent Rocq proof-session daemon behind rq.

   Usage:
     rq-worker SESSION_DIR [rocq options...]   (with RQ_FILE naming the .v file)

   Architecture:
   Rocq is sequential and must run in the main OCaml domain because
   [Pp.string_of_ppcmds] formats into [Format.str_formatter] (owned by the main
   domain) and flushes the calling domain's buffer, producing empty strings on
   any secondary domain. The worker therefore splits into two domains:

   1. Main domain ([run_rocq_domain]): initializes Rocq ([Rocq_engine],
      [Session]) and executes queued jobs one at a time, pushing progress and
      results onto an [Eio.Stream.t].
   2. Server domain ([Server.run]): listens on [SESSION_DIR/sock], answers
      [status], [cancel], and [withdraw] requests immediately even while Rocq is
      busy, and runs one event-follower fiber that owns [SESSION_DIR]'s status,
      transcript, and job-result files.

   Module map (library [rq_worker_lib]):
   - [Source]      : line-indexed source buffers, byte spans, prefix diffing
   - [Interrupt]   : cooperative SIGINT arming between the two domains
   - [Vernac_ast]  : structural classification of parsed Rocq commands
   - [Rocq_goals]  : extracting open proof goals from [Vernacstate.t]
   - [Rocq_engine] : Rocq initialization, feedback capture, sentence runner
   - [History]     : committed sentence history and incremental reload planning
   - [Session]     : proof-session commands (load, step, try, check, back, ...)
   - [Protocol]    : JSON wire request decoder and reply/status encoders
   - [Job_queue]   : cross-domain FIFO queue with withdrawal and active tracking
   - [Session_dir] : atomic status/job files and append-only logs on disk
   - [Server]      : Unix-domain socket server and event follower *)

open Eio.Std
open Rq_worker_lib

type cli = {
  session_dir : string;
  file : string;
  rocq_args : string list;
}

let parse_cli argv =
  match Array.to_list argv with
  | _ :: ("-h" | "--help") :: _ | [ _ ] | [] ->
      Printf.eprintf
        "Usage: rq-worker SESSION_DIR [rocq options...]\n\
         Environment: RQ_FILE=<path-to-proof-file.v>\n";
      exit 2
  | _ :: session_dir :: rocq_args ->
      let file = Stdlib.Option.value (Sys.getenv_opt "RQ_FILE") ~default:"" in
      { session_dir; file; rocq_args }

let execute_job ~events session_result job =
  let job_id = Job_queue.id job in
  let cmd = Job_queue.cmd job in
  let started = Unix.gettimeofday () in
  match session_result with
  | Error startup_err ->
      let seconds = Unix.gettimeofday () -. started in
      let reply =
        Protocol.encode_job_startup_error ~job_id ~cmd ~seconds startup_err
      in
      (reply, 0)
  | Ok session ->
      Interrupt.reset_for_job ();
      Eio.Stream.add events (Server.Job_started job_id);
      let session_reply = Session.handle session (Job_queue.request job) in
      let seconds = Unix.gettimeofday () -. started in
      let nodes = Session.node_count session in
      let reply =
        Protocol.encode_job_reply ~job_id ~cmd ~seconds ~nodes session_reply
      in
      (reply, nodes)

let run_rocq_domain ~file ~rocq_args ~queue ~events =
  let emit ev = Eio.Stream.add events (Server.Session_event ev) in
  let session_result =
    match Session.create ~file ~args:rocq_args ~emit with
    | session ->
        (* Install our SIGINT handler after [Coqinit] has installed its own. *)
        Interrupt.install_rocq_handler ();
        Eio.Stream.add events Server.Ready;
        Ok session
    | exception exn ->
        let msg = Printexc.to_string exn in
        Eio.Stream.add events (Server.Startup_failed msg);
        Error msg
  in
  let last_nodes = ref 0 in
  let rec loop () =
    let job, reply, nodes =
      match Job_queue.take_next queue with
      | `Withdrawn job ->
          let reply =
            Protocol.encode_job_withdrawn ~job_id:(Job_queue.id job)
              ~cmd:(Job_queue.cmd job)
          in
          (job, reply, !last_nodes)
      | `Run job ->
          let reply, nodes = execute_job ~events session_result job in
          Job_queue.finish_running queue job;
          last_nodes := nodes;
          (job, reply, nodes)
    in
    Eio.Stream.add events (Server.Job_finished { job; reply; nodes });
    loop ()
  in
  loop ()

let () =
  let cli = parse_cli Sys.argv in
  Sys.set_signal Sys.sigpipe Signal_ignore;
  Eio_main.run @@ fun env ->
  let queue = Job_queue.create () in
  let events = Eio.Stream.create 4096 in
  let net = Eio.Stdenv.net env in
  let fs = Eio.Stdenv.fs env in
  let clock = Eio.Stdenv.clock env in
  let domain_mgr = Eio.Stdenv.domain_mgr env in
  Fiber.both
    (fun () ->
      Eio.Domain_manager.run domain_mgr
        (Server.run ~net ~fs ~clock ~dir:cli.session_dir ~queue ~events))
    (fun () ->
      run_rocq_domain ~file:cli.file ~rocq_args:cli.rocq_args ~queue ~events)
