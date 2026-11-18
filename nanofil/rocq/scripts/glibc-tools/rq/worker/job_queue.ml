open Eio.Std

type state =
  | Queued
  | Running
  | Withdrawn
  | Finished

let state_name = function
  | Queued -> "queued"
  | Running -> "running"
  | Withdrawn -> "withdrawn"
  | Finished -> "finished"

type ('req, 'reply) job = {
  id : int;
  cmd : string;
  request : 'req;
  state : state Atomic.t;
  reply : 'reply Promise.t;
  resolve : 'reply Promise.u;
}

let id job = job.id
let cmd job = job.cmd
let request job = job.request
let state job = Atomic.get job.state
let await_reply job = Promise.await job.reply

type ('req, 'reply) t = {
  stream : ('req, 'reply) job Eio.Stream.t;
  active : (int, ('req, 'reply) job) Hashtbl.t;  (* owned by the server domain *)
  mutable next_id : int;                          (* owned by the server domain *)
  unfinished : int Atomic.t;                      (* queued + running jobs *)
  current : int Atomic.t;                         (* running job id, or 0 *)
}

let create () =
  {
    stream = Eio.Stream.create max_int;
    active = Hashtbl.create 16;
    next_id = 0;
    unfinished = Atomic.make 0;
    current = Atomic.make 0;
  }

let submit t ~cmd request =
  t.next_id <- t.next_id + 1;
  let reply, resolve = Promise.create () in
  let job =
    {
      id = t.next_id;
      cmd;
      request;
      state = Atomic.make Queued;
      reply;
      resolve;
    }
  in
  let jobs_ahead = Atomic.fetch_and_add t.unfinished 1 in
  Hashtbl.replace t.active job.id job;
  Eio.Stream.add t.stream job;
  (job, jobs_ahead)

let withdraw t job_id =
  match Hashtbl.find_opt t.active job_id with
  | None -> Finished
  | Some job ->
      if Atomic.compare_and_set job.state Queued Withdrawn then
        Atomic.decr t.unfinished;
      Atomic.get job.state

let complete t job reply =
  Hashtbl.remove t.active job.id;
  Promise.resolve job.resolve reply

let running_job_id t =
  Atomic.get t.current

let queued_count t =
  let total = Atomic.get t.unfinished in
  let running = if Atomic.get t.current <> 0 then 1 else 0 in
  max 0 (total - running)

let take_next t =
  let job = Eio.Stream.take t.stream in
  if Atomic.compare_and_set job.state Queued Running then begin
    Atomic.set t.current job.id;
    `Run job
  end else
    `Withdrawn job

let finish_running t job =
  Atomic.set job.state Finished;
  Atomic.decr t.unfinished;
  Atomic.set t.current 0
