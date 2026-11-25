(* Comment Markdown block parser mirroring nanofil/web/dterm_html.pl. *)

type block =
  | P of string
  | Ul of string list
  | Pre of string list
  | H of int * string
  | Table of string list * string list list
  | Fence of string * string list
  | Embed of string

let trim_spaces s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && s.[!i] = ' ' do
    incr i
  done;
  let j = ref n in
  while !j > !i && s.[!j - 1] = ' ' do
    decr j
  done;
  String.sub s !i (!j - !i)

let trim_ws s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && (s.[!i] = ' ' || s.[!i] = '\t') do
    incr i
  done;
  let j = ref n in
  while !j > !i && (s.[!j - 1] = ' ' || s.[!j - 1] = '\t') do
    decr j
  done;
  String.sub s !i (!j - !i)

let rtrim s =
  let j = ref (String.length s) in
  while !j > 0 && (s.[!j - 1] = ' ' || s.[!j - 1] = '\t') do
    decr j
  done;
  String.sub s 0 !j

let is_blank s = trim_ws s = ""

let rec drop_leading_blank = function
  | l :: ls when is_blank l -> drop_leading_blank ls
  | ls -> ls

let trim_blank_ends ls =
  ls |> drop_leading_blank |> List.rev |> drop_leading_blank |> List.rev

let indent s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && s.[!i] = ' ' do
    incr i
  done;
  !i

let dedent ls =
  let non_blank = List.filter (fun l -> not (is_blank l)) ls in
  let min_i =
    match non_blank with
    | [] -> 0
    | first :: rest -> List.fold_left (fun acc l -> min acc (indent l)) (indent first) rest
  in
  List.map
    (fun l ->
      if is_blank l then ""
      else
        let n = String.length l in
        if min_i >= n then "" else String.sub l min_i (n - min_i))
    ls

let item_start l =
  if String.starts_with ~prefix:"- " l then Some (String.sub l 2 (String.length l - 2))
  else if String.starts_with ~prefix:"* " l then Some (String.sub l 2 (String.length l - 2))
  else None

let heading l =
  if String.starts_with ~prefix:"### " l then Some (4, String.sub l 4 (String.length l - 4))
  else if String.starts_with ~prefix:"## " l then Some (3, String.sub l 3 (String.length l - 3))
  else None

let embed_line l =
  let t = trim_ws l in
  if String.starts_with ~prefix:"![[" t && String.ends_with ~suffix:"]]" t then
    let inner = String.sub t 3 (String.length t - 5) in
    if String.contains inner ']' then None else Some inner
  else None

let unescape_pipes s =
  let n = String.length s in
  let b = Buffer.create n in
  let rec go i =
    if i >= n then Buffer.contents b
    else if s.[i] = '\\' && i + 1 < n && s.[i + 1] = '|' then (
      Buffer.add_char b '|';
      go (i + 2))
    else (
      Buffer.add_char b s.[i];
      go (i + 1))
  in
  go 0

let table_line l =
  let n = String.length l in
  if n >= 2 && l.[0] = '|' && l.[n - 1] = '|' then (
    let body = String.sub l 1 (n - 2) in
    let blen = String.length body in
    let rec parse_cells i acc =
      let buf = Buffer.create 32 in
      let rec scan j =
        if j >= blen then (j, Buffer.contents buf)
        else if body.[j] = '\\' && j + 1 < blen && body.[j + 1] = '|' then (
          Buffer.add_char buf '|';
          scan (j + 2))
        else if body.[j] = '|' then (j, Buffer.contents buf)
        else if body.[j] = '`' then (
          match String.index_from_opt body (j + 1) '`' with
          | Some k ->
              Buffer.add_char buf '`';
              Buffer.add_string buf (unescape_pipes (String.sub body (j + 1) (k - j - 1)));
              Buffer.add_char buf '`';
              scan (k + 1)
          | None ->
              Buffer.add_char buf '`';
              scan (j + 1))
        else (
          Buffer.add_char buf body.[j];
          scan (j + 1))
      in
      let next_i, cell = scan i in
      let acc' = trim_spaces cell :: acc in
      if next_i < blen && body.[next_i] = '|' then parse_cells (next_i + 1) acc'
      else List.rev acc'
    in
    Some (parse_cells 0 []))
  else None

let is_rule_cell s =
  let n = String.length s in
  n > 0
  &&
  let rec ok i = if i >= n then true else (s.[i] = '-' || s.[i] = ':') && ok (i + 1) in
  ok 0

let rec take_table acc = function
  | l :: ls -> (
      match table_line l with
      | Some cells -> take_table (cells :: acc) ls
      | None -> (List.rev acc, l :: ls))
  | [] -> (List.rev acc, [])

let rec take_cont acc = function
  | l :: ls when (not (is_blank l)) && indent l > 0 -> take_cont (l :: acc) ls
  | ls -> (List.rev acc, ls)

let rec list_items acc = function
  | l :: ls0 -> (
      match item_start l with
      | Some first ->
          let cont, ls1 = take_cont [] ls0 in
          let cont1 = List.map trim_spaces cont in
          let text = String.concat " " (first :: cont1) in
          let acc' = text :: acc in
          (match ls1 with
          | l1 :: _ when item_start l1 <> None -> list_items acc' ls1
          | b :: l1 :: rest when is_blank b && item_start l1 <> None ->
              list_items acc' (l1 :: rest)
          | _ -> (List.rev acc', ls1))
      | None -> (List.rev acc, l :: ls0))
  | [] -> (List.rev acc, [])

let rec take_indented acc = function
  | l :: ls when is_blank l || indent l > 0 -> take_indented (l :: acc) ls
  | ls -> (List.rev acc, ls)

let rec take_para acc = function
  | l :: ls
    when (not (is_blank l))
         && item_start l = None
         && indent l = 0
         && (not (String.starts_with ~prefix:"```" l))
         && heading l = None
         && table_line l = None
         && embed_line l = None ->
      take_para (l :: acc) ls
  | ls -> (List.rev acc, ls)

let rec take_fence acc = function
  | [] -> (List.rev acc, [])
  | l :: ls when String.starts_with ~prefix:"```" l -> (List.rev acc, ls)
  | l :: ls -> take_fence (l :: acc) ls

let blocks (lines : string list) : block list =
  let rec go acc = function
    | [] -> List.rev acc
    | l :: ls when is_blank l -> go acc ls
    | l :: ls0 when String.starts_with ~prefix:"```" l ->
        let lang = trim_spaces (String.sub l 3 (String.length l - 3)) in
        let body, ls = take_fence [] ls0 in
        go (Fence (lang, body) :: acc) ls
    | l :: ls0 -> (
        match heading l with
        | Some (n, text) -> go (H (n, text) :: acc) ls0
        | None -> (
            match embed_line l with
            | Some name -> go (Embed name :: acc) ls0
            | None -> (
                match (table_line l, ls0) with
                | Some head, sep :: ls1 -> (
                    match table_line sep with
                    | Some cells when List.for_all is_rule_cell cells ->
                        let rows, ls = take_table [] ls1 in
                        go (Table (head, rows) :: acc) ls
                    | _ -> go_other acc l ls0)
                | _ -> go_other acc l ls0)))
  and go_other acc l ls0 =
    if item_start l <> None then
      let items, ls = list_items [] (l :: ls0) in
      go (Ul items :: acc) ls
    else if indent l > 0 then
      let pre0, ls = take_indented [] ls0 in
      let pre1 = trim_blank_ends pre0 in
      go (Pre (l :: pre1) :: acc) ls
    else
      let para, ls = take_para [] ls0 in
      let text = String.concat " " (l :: para) in
      go (P text :: acc) ls
  in
  go [] lines
