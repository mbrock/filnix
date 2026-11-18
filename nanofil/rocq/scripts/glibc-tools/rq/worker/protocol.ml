(* The rq command line sends the worker one JSON object per connection, on
   one line. A control request is answered at once, even while Rocq is
   busy; a session request joins the queue, and the worker first answers
   with the job number it gave it and how many jobs are ahead of it, then
   with the result when the job ends. *)

type t =
  | Status  (** what the session is doing now *)
  | Cancel of int option  (** interrupt the running job, or only job N *)
  | Withdraw of int  (** take job N out of the queue if it has not started *)
  | Stop
  | Session of { cmd : string; request : Session.request; detach : bool }
      (** A job for the queue. A detached job stays queued when its client
          hangs up. *)

let parse json =
  let open Yojson.Safe.Util in
  let field name = member name json in
  let int_opt name = match field name with `Int n -> Some n | _ -> None in
  let target () =
    match (field "theorem", field "line") with
    | `String name, _ -> Session.Theorem name
    | _, `Int n -> Line n
    | _ -> End
  in
  let job cmd request = Ok (Session { cmd; request; detach = field "detach" = `Bool true }) in
  match field "cmd" with
  | `String "status" -> Ok Status
  | `String "cancel" -> Ok (Cancel (int_opt "job"))
  | `String "withdraw" -> (
      match int_opt "job" with Some n -> Ok (Withdraw n) | None -> Error "withdraw needs a job")
  | `String "stop" -> Ok Stop
  | `String ("load" as c) -> job c (Load (target ()))
  | `String ("step" as c) -> job c (Step (to_string (field "text")))
  | `String ("try" as c) ->
      job c (Try { candidates = List.map to_string (to_list (field "candidates")); commit = field "commit" = `Bool true })
  | `String ("check" as c) -> job c Check
  | `String ("back" as c) -> job c (Back (Stdlib.Option.value (int_opt "count") ~default:1))
  | `String ("goals" as c) -> job c Goals
  | `String ("nodes" as c) -> job c Nodes
  | `String c -> Error ("unknown command " ^ c)
  | _ -> Error "a request needs a cmd"
  | exception Type_error (msg, _) -> Error msg
