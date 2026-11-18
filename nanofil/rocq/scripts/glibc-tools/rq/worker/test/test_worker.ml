open Rq_worker_lib

let check msg cond =
  if not cond then failwith ("test failure: " ^ msg)

let check_eq ~pp msg expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf "test failure (%s): expected %s, got %s" msg (pp expected)
         (pp actual))

let check_int = check_eq ~pp:string_of_int
let check_str = check_eq ~pp:(Printf.sprintf "%S")

let test_source () =
  let s = Source.of_string "Lemma a.\nProof.\n  auto." in
  check_int "length" 23 (Source.length s);
  let p0 = Source.pos_of_offset s 0 in
  check_int "p0.line" 1 p0.line;
  check_int "p0.col" 1 p0.col;
  (* Offset 8 is the '\n' at the end of line 1. *)
  let p8 = Source.pos_of_offset s 8 in
  check_int "p8.line" 1 p8.line;
  check_int "p8.col" 9 p8.col;
  (* Offset 9 is 'P' at the start of line 2. *)
  let p9 = Source.pos_of_offset s 9 in
  check_int "p9.line" 2 p9.line;
  check_int "p9.col" 1 p9.col;
  check_int "bol line 2" 9 (Source.line_start_offset s 12);
  check_int "eol 1" 8 (Source.end_of_line s 1);
  check_int "eol 2" 15 (Source.end_of_line s 2);
  check_int "eol 3 (no trailing newline)" 23 (Source.end_of_line s 3);
  check_int "eol past end" 23 (Source.end_of_line s 99);
  let sp = Source.span s ~bp:9 ~ep:15 in
  check_str "sub" "Proof." (Source.sub s ~bp:sp.bp ~ep:sp.ep);
  check_int "diff identical" 5 (Source.first_diff_offset "hello" "hello");
  check_int "diff prefix" 3 (Source.first_diff_offset "hel" "hello");
  check_int "diff middle" 2 (Source.first_diff_offset "heXlo" "hello")

let mk_entry ~origin ~bp ~ep ?(names = []) state text : int History.entry =
  let dummy_src = Source.of_string (String.make (max ep 64) 'x') in
  {
    origin;
    text;
    span = Source.span dummy_src ~bp ~ep;
    state;
    ms = 1.0;
    is_query = false;
    defined_names = names;
  }

let test_history () =
  let h0 = History.empty ~initial:0 in
  check_int "empty tip" 0 (History.tip h0);
  let e1 = mk_entry ~origin:"file" ~bp:0 ~ep:10 1 "Require Import A." in
  let e2 = mk_entry ~origin:"file" ~bp:11 ~ep:25 ~names:[ "foo" ] 2 "Lemma foo : True." in
  let e3 = mk_entry ~origin:"file" ~bp:26 ~ep:32 3 "Proof." in
  let e4 = mk_entry ~origin:"step" ~bp:0 ~ep:6 4 "exact I." in
  let h = History.append h0 [ e1; e2; e3; e4 ] in
  check_int "length" 4 (History.length h);
  check_int "tip" 4 (History.tip h);
  check_eq ~pp:(fun l -> String.concat "," (List.map string_of_int l))
    "chronological order" [ 1; 2; 3; 4 ]
    (List.map (fun (e : _ History.entry) -> e.state) (History.entries h));

  (* Strict ep < first_diff: an edit at byte 25 (e2.ep) must re-run e2. *)
  let plan_boundary =
    History.plan_reload h ~first_diff:25 ~target_end_offset:max_int ~reopen_theorem:None
  in
  check_int "boundary reused" 1 plan_boundary.reused_count;
  check_int "boundary resume" 10 plan_boundary.resume_offset;
  check_int "scratch dropped" 1 (List.length plan_boundary.dropped_scratch);
  check_str "scratch text" "exact I." (List.hd plan_boundary.dropped_scratch).text;

  (* Reopening theorem "foo" cuts back before e2 even when the file did not change. *)
  let plan_thm =
    History.plan_reload h ~first_diff:100 ~target_end_offset:max_int
      ~reopen_theorem:(Some "foo")
  in
  check_int "reopen reused" 1 plan_thm.reused_count;
  check_int "reopen tip" 1 (History.tip plan_thm.kept);

  let dropped, h_back = History.drop_last 2 h in
  check_int "dropped 2" 2 dropped;
  check_int "tip after back 2" 2 (History.tip h_back);
  let dropped_all, h_empty = History.drop_last 99 h_back in
  check_int "dropped clamped" 2 dropped_all;
  check_int "tip initial" 0 (History.tip h_empty)

let test_protocol () =
  begin match Protocol.decode_client_msg {|{"cmd":"load","theorem":"sl_find_one"}|} with
  | Ok (Enqueue { cmd = "load"; request = Load (Theorem "sl_find_one"); detach = false }) -> ()
  | _ -> failwith "unexpected decode for load theorem"
  end;
  begin match Protocol.decode_client_msg {|{"cmd":"step","text":"auto.","detach":true}|} with
  | Ok (Enqueue { cmd = "step"; request = Step { origin = "step"; text = "auto." }; detach = true }) -> ()
  | _ -> failwith "unexpected decode for detached step"
  end;
  begin match Protocol.decode_client_msg {|{"cmd":"withdraw"}|} with
  | Error _ -> ()
  | Ok _ -> failwith "withdraw without job should fail"
  end;
  let open Yojson.Safe.Util in
  let cancel_none = Protocol.encode_cancelled ~cancelled:None ~running:0 in
  check "cancelled is null" (member "cancelled" cancel_none = `Null);
  check_int "running is 0" 0 (to_int (member "running" cancel_none));
  let reply =
    Protocol.encode_job_reply ~job_id:3 ~cmd:"back" ~seconds:0.25 ~nodes:7
      (Session.Backed_up { dropped = 2; goals = None })
  in
  check_int "reply job" 3 (to_int (member "job" reply));
  check_int "reply nodes" 7 (to_int (member "nodes" reply));
  check_int "reply dropped" 2 (to_int (member "dropped" reply));
  check "reply goals null" (member "goals" reply = `Null)

let test_job_queue_and_dir () =
  Eio_main.run @@ fun env ->
  let q : (string, string) Job_queue.t = Job_queue.create () in
  let j1, ahead1 = Job_queue.submit q ~cmd:"step" "first" in
  let j2, ahead2 = Job_queue.submit q ~cmd:"step" "second" in
  check_int "j1 ahead" 0 ahead1;
  check_int "j2 ahead" 1 ahead2;
  check_int "queued before take" 2 (Job_queue.queued_count q);
  check_int "running before take" 0 (Job_queue.running_job_id q);

  begin match Job_queue.take_next q with
  | `Run taken ->
      check_int "taken id" (Job_queue.id j1) (Job_queue.id taken);
      check_int "running id" 1 (Job_queue.running_job_id q);
      check_int "queued while running" 1 (Job_queue.queued_count q);
      (* Withdraw j2 while j1 is running. *)
      check "j2 withdrawn" (Job_queue.withdraw q (Job_queue.id j2) = Withdrawn);
      check_int "queued after withdraw" 0 (Job_queue.queued_count q);
      (* Withdrawing running j1 leaves it Running. *)
      check "j1 stays running" (Job_queue.withdraw q (Job_queue.id j1) = Running);
      Job_queue.finish_running q taken;
      Job_queue.complete q taken "done-1"
  | `Withdrawn _ -> failwith "j1 should not be withdrawn"
  end;
  check_str "await j1" "done-1" (Job_queue.await_reply j1);
  check_int "idle running id" 0 (Job_queue.running_job_id q);
  check_int "idle queued" 0 (Job_queue.queued_count q);

  begin match Job_queue.take_next q with
  | `Withdrawn taken ->
      check_int "withdrawn id" (Job_queue.id j2) (Job_queue.id taken);
      Job_queue.complete q taken "withdrawn-2"
  | `Run _ -> failwith "j2 was withdrawn and must not run"
  end;
  check_str "await j2" "withdrawn-2" (Job_queue.await_reply j2);

  (* Session_dir atomic writes and appends *)
  let tmp = Filename.temp_dir "rq-worker-test-" "" in
  Fun.protect ~finally:(fun () ->
      Array.iter (fun f -> Sys.remove (Filename.concat tmp f)) (Sys.readdir tmp);
      Unix.rmdir tmp)
  @@ fun () ->
  let fs = Eio.Stdenv.fs env in
  let sdir = Session_dir.of_path Eio.Path.(fs / tmp) in
  Session_dir.write_status sdir
    {
      state = Idle;
      pid = 42;
      running_job = 0;
      job_started = 0.0;
      nodes = 5;
      queued = 0;
      updated = 100.0;
      sentence = None;
    };
  Session_dir.write_job_result sdir ~job_id:1 (`Assoc [ ("ok", `Bool true) ]);
  Session_dir.append_log sdir "hello";
  Session_dir.append_log sdir "world\n";
  let log_text = Eio.Path.load Eio.Path.(fs / tmp / "log") in
  check_str "log content" "hello\nworld\n" log_text;
  let last_job = String.trim (Eio.Path.load Eio.Path.(fs / tmp / "last-job")) in
  check_str "last-job" "1" last_job

let () =
  test_source ();
  test_history ();
  test_protocol ();
  test_job_queue_and_dir ();
  print_endline "rq-worker unit tests passed"
