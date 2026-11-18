open Eio.Std

type job = (Session.request, Yojson.Safe.t) Job_queue.job
type queue = (Session.request, Yojson.Safe.t) Job_queue.t

type worker_event =
  | Ready
  | Startup_failed of string
  | Job_started of int
  | Job_finished of {
      job : job;
      reply : Yojson.Safe.t;
      nodes : int;
    }
  | Session_event of Session.event

type t = {
  sdir : Session_dir.t;
  clock : float Eio.Time.clock_ty r;
  queue : queue;
  events : worker_event Eio.Stream.t;
  pid : int;
  mutable state : Protocol.worker_state;
  mutable job_started : float;
  mutable sentence : Protocol.active_sentence option;
  mutable nodes : int;
}

let snapshot_status t : Protocol.worker_status =
  {
    state = t.state;
    pid = t.pid;
    running_job = Job_queue.running_job_id t.queue;
    job_started = t.job_started;
    nodes = t.nodes;
    queued = Job_queue.queued_count t.queue;
    updated = Eio.Time.now t.clock;
    sentence = t.sentence;
  }

let persist_status t =
  Session_dir.write_status t.sdir (snapshot_status t)

(* Single writer for every file in [t.sdir]. Writing [status.json] and
   [job-N.json] before calling [Job_queue.complete] guarantees that a client
   woken by its reply promise (or falling back to [rq wait]) sees consistent
   files on disk. *)
let rec follow_events t =
  begin match Eio.Stream.take t.events with
  | Ready ->
      t.state <- Idle;
      persist_status t
  | Startup_failed msg ->
      t.state <- Failed;
      Session_dir.append_log t.sdir msg;
      persist_status t
  | Job_started _ ->
      t.state <- Busy;
      t.job_started <- Eio.Time.now t.clock;
      t.sentence <- None;
      persist_status t
  | Job_finished { job; reply; nodes } ->
      t.state <- Idle;
      t.nodes <- nodes;
      t.sentence <- None;
      persist_status t;
      Session_dir.write_job_result t.sdir ~job_id:(Job_queue.id job) reply;
      Job_queue.complete t.queue job reply
  | Session_event (Sentence { origin; line; text }) ->
      t.sentence <-
        Some { origin; line; text; started = Eio.Time.now t.clock };
      persist_status t
  | Session_event (Log line) ->
      Session_dir.append_log t.sdir line
  | Session_event (Transcript text) ->
      Session_dir.append_transcript t.sdir text
  | Session_event (Dropped text) ->
      Session_dir.write_dropped t.sdir text
  end;
  follow_events t

let handle_cancel t target_job =
  let running = Job_queue.running_job_id t.queue in
  let matches_target =
    match target_job with None -> true | Some id -> id = running
  in
  if running = 0 || not matches_target then
    Protocol.encode_cancelled ~cancelled:None ~running
  else begin
    Interrupt.request_cancel ();
    Protocol.encode_cancelled ~cancelled:(Some running) ~running
  end

let handle_withdraw t job_id =
  let st = Job_queue.withdraw t.queue job_id in
  Protocol.encode_withdrawn_status ~job_id ~state:(Job_queue.state_name st)

(* Serve a single client connection. If an attached client disconnects while its
   job is still queued, withdraw the job; if the job has already started, let it
   finish so Ctrl-C on [rq] detaches cleanly without aborting Rocq's work. *)
let serve_connection ~stop_server t flow _addr =
  let reader = Eio.Buf_read.of_flow flow ~max_size:(256 * 1024 * 1024) in
  let send json =
    Eio.Flow.copy_string (Yojson.Safe.to_string json ^ "\n") flow
  in
  match Eio.Buf_read.line reader with
  | exception End_of_file -> ()
  | exception Failure msg -> send (Protocol.encode_error msg)
  | line -> (
      match Protocol.decode_client_msg line with
      | Error msg -> send (Protocol.encode_error msg)
      | Ok Status -> send (Protocol.encode_status (snapshot_status t))
      | Ok (Cancel target_job) -> send (handle_cancel t target_job)
      | Ok (Withdraw job_id) -> send (handle_withdraw t job_id)
      | Ok Stop ->
          send (Protocol.encode_stopped ());
          Promise.resolve stop_server ()
      | Ok (Enqueue { cmd; request; detach }) ->
          let job, queued = Job_queue.submit t.queue ~cmd request in
          let job_id = Job_queue.id job in
          send
            (Protocol.encode_ack ~job_id ~queued ~starting:(t.state = Starting));
          if not detach then
            Fiber.first
              (fun () -> send (Job_queue.await_reply job))
              (fun () ->
                if Eio.Buf_read.at_end_of_input reader then
                  ignore (Job_queue.withdraw t.queue job_id)
                else
                  Fiber.await_cancel ()))

let run ~net ~fs ~clock ~dir ~queue ~events () =
  Interrupt.block_in_current_thread ();
  Switch.run @@ fun sw ->
  let sdir = Session_dir.of_path Eio.Path.(fs / dir) in
  let t =
    {
      sdir;
      clock;
      queue;
      events;
      pid = Unix.getpid ();
      state = Starting;
      job_started = 0.0;
      sentence = None;
      nodes = 0;
    }
  in
  persist_status t;
  Session_dir.remove_socket sdir;
  let listening =
    Eio.Net.listen ~sw ~backlog:16 net (`Unix (Session_dir.socket_native_path sdir))
  in
  let stopped, stop_server = Promise.create () in
  Fiber.fork_daemon ~sw (fun () -> follow_events t);
  Fiber.first
    (fun () -> Promise.await stopped)
    (fun () ->
      Eio.Net.run_server listening (serve_connection ~stop_server t)
        ~on_error:(fun exn ->
          Session_dir.append_log sdir
            ("[rq-worker] " ^ Printexc.to_string exn)));
  t.state <- Stopped;
  persist_status t;
  Session_dir.remove_socket sdir;
  exit 0
