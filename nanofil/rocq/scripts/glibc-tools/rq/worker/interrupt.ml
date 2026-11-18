exception Cancelled

let armed = Atomic.make false
let cancel_requested = Atomic.make false

let on_sigint _ =
  if Atomic.get armed && Atomic.get cancel_requested then raise Sys.Break

let install_rocq_handler () =
  Eio_unix.set_signal Sys.sigint (Signal_handle on_sigint)

let block_in_current_thread () =
  ignore (Thread.sigmask SIG_BLOCK [ Sys.sigint ])

let reset_for_job () =
  Atomic.set cancel_requested false

let is_requested () =
  Atomic.get cancel_requested

(* Store [cancel_requested] before reading [armed]; [with_armed] stores [armed]
   before reading [cancel_requested]. Sequential consistency guarantees that at
   least one side sees the other's write: either [request_cancel] sends SIGINT
   or [with_armed] aborts before entering Rocq. *)
let request_cancel () =
  Atomic.set cancel_requested true;
  if Atomic.get armed then Unix.kill (Unix.getpid ()) Sys.sigint

let with_armed f =
  Fun.protect ~finally:(fun () -> Atomic.set armed false) @@ fun () ->
  Atomic.set armed true;
  if Atomic.get cancel_requested then raise Cancelled;
  try f () with Sys.Break -> raise Cancelled
