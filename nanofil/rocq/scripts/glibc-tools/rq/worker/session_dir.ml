type t = Eio.Fs.dir_ty Eio.Path.t

let of_path (path : _ Eio.Path.t) : t = (path :> t)

let file t name = Eio.Path.(t / name)

let write_atomic t name content =
  let tmp = file t (name ^ ".tmp") in
  Eio.Path.save ~create:(`Or_truncate 0o644) tmp content;
  Eio.Path.rename tmp (file t name)

let append t name content =
  Eio.Path.save ~append:true ~create:(`If_missing 0o644) (file t name) content

let ensure_newline s =
  if String.ends_with ~suffix:"\n" s then s else s ^ "\n"

let socket_native_path t =
  Eio.Path.native_exn (file t "sock")

let remove_socket t =
  Eio.Path.unlink ~missing_ok:true (file t "sock")

let write_status t status =
  let body = Yojson.Safe.to_string (Protocol.encode_status status) ^ "\n" in
  write_atomic t "status.json" body

let write_job_result t ~job_id reply_json =
  let name = Printf.sprintf "job-%d.json" job_id in
  write_atomic t name (Yojson.Safe.to_string reply_json ^ "\n");
  write_atomic t "last-job" (string_of_int job_id ^ "\n")

let append_log t line =
  append t "log" (ensure_newline line)

let append_transcript t text =
  append t "transcript.v" text

let write_dropped t text =
  write_atomic t "dropped.v" text
