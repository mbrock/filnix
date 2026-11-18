type pos = {
  line : int;
  col : int;
}

type span = {
  bp : int;
  ep : int;
  start_pos : pos;
  end_pos : pos;
}

type t = {
  text : string;
  line_starts : int array;  (* 0-based start offset of each 0-indexed line *)
}

let of_string text =
  let len = String.length text in
  let count = ref 1 in
  for i = 0 to len - 1 do
    if text.[i] = '\n' then incr count
  done;
  let line_starts = Array.make !count 0 in
  let line_idx = ref 1 in
  for i = 0 to len - 1 do
    if text.[i] = '\n' then begin
      line_starts.(!line_idx) <- i + 1;
      incr line_idx
    end
  done;
  { text; line_starts }

let text t = t.text
let length t = String.length t.text

let clamp_offset t off =
  max 0 (min off (String.length t.text))

let sub t ~bp ~ep =
  let bp = clamp_offset t bp in
  let ep = max bp (clamp_offset t ep) in
  String.sub t.text bp (ep - bp)

(* Binary search for the largest 0-based line index whose start offset <= off. *)
let line_index_of_offset t off =
  let off = clamp_offset t off in
  let rec search lo hi =
    if lo >= hi then lo
    else
      let mid = lo + ((hi - lo + 1) / 2) in
      if t.line_starts.(mid) <= off then search mid hi
      else search lo (mid - 1)
  in
  search 0 (Array.length t.line_starts - 1)

let line_start_offset t off =
  let idx = line_index_of_offset t off in
  t.line_starts.(idx)

let pos_of_offset t off =
  let off = clamp_offset t off in
  let idx = line_index_of_offset t off in
  let bol = t.line_starts.(idx) in
  { line = idx + 1; col = off - bol + 1 }

let span t ~bp ~ep =
  let bp = clamp_offset t bp in
  let ep = max bp (clamp_offset t ep) in
  { bp; ep; start_pos = pos_of_offset t bp; end_pos = pos_of_offset t ep }

let end_of_line t line_num =
  if line_num <= 0 then 0
  else if line_num < Array.length t.line_starts then
    (* Line (line_num + 1) begins right after line_num's '\n'. *)
    t.line_starts.(line_num) - 1
  else String.length t.text

let first_diff_offset a b =
  let limit = min (String.length a) (String.length b) in
  let rec scan i =
    if i < limit && a.[i] = b.[i] then scan (i + 1) else i
  in
  scan 0
