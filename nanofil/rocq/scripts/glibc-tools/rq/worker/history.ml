type 'st entry = {
  origin : string;
  text : string;
  span : Source.span;
  state : 'st;
  ms : float;
  is_query : bool;
  defined_names : string list;
}

(* Stored newest-first internally for O(1) [tip] and [drop_last], while the
   public API works exclusively in chronological (oldest-first) order. *)
type 'st t = {
  initial : 'st;
  rev_entries : 'st entry list;
  count : int;
}

let empty ~initial = { initial; rev_entries = []; count = 0 }
let length t = t.count

let tip t =
  match t.rev_entries with
  | newest :: _ -> newest.state
  | [] -> t.initial

let entries t = List.rev t.rev_entries

let of_chronological ~initial chronological =
  {
    initial;
    rev_entries = List.rev chronological;
    count = List.length chronological;
  }

let append t chronological =
  if chronological = [] then t
  else
    {
      initial = t.initial;
      rev_entries = List.rev_append chronological t.rev_entries;
      count = t.count + List.length chronological;
    }

let rec drop_prefix n lst =
  if n <= 0 then lst
  else match lst with [] -> [] | _ :: rest -> drop_prefix (n - 1) rest

let drop_last n t =
  let n = max 0 n in
  let dropped = min n t.count in
  if dropped = 0 then (0, t)
  else
    ( dropped,
      {
        initial = t.initial;
        rev_entries = drop_prefix dropped t.rev_entries;
        count = t.count - dropped;
      } )

type 'st reload_plan = {
  kept : 'st t;
  reused_count : int;
  resume_offset : int;
  dropped_scratch : 'st entry list;
}

let take_while pred lst =
  let rec loop acc = function
    | x :: xs when pred x -> loop (x :: acc) xs
    | _ -> List.rev acc
  in
  loop [] lst

let take_before pred lst =
  let rec loop acc = function
    | [] -> List.rev acc
    | x :: _ when pred x -> List.rev acc
    | x :: xs -> loop (x :: acc) xs
  in
  loop [] lst

let plan_reload t ~first_diff ~target_end_offset ~reopen_theorem =
  let all = entries t in
  let file_entries, dropped_scratch =
    List.partition (fun e -> e.origin = "file") all
  in
  let kept_entries =
    take_while
      (fun e -> e.span.ep < first_diff && e.span.ep <= target_end_offset)
      file_entries
  in
  let kept_entries =
    match reopen_theorem with
    | None -> kept_entries
    | Some name ->
        take_before (fun e -> List.mem name e.defined_names) kept_entries
  in
  let kept = of_chronological ~initial:t.initial kept_entries in
  let resume_offset =
    match kept.rev_entries with
    | last_kept :: _ -> last_kept.span.ep
    | [] -> 0
  in
  { kept; reused_count = kept.count; resume_offset; dropped_scratch }
