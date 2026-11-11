(* M0 reference benchmark in idiomatic pure OCaml (ocamlopt -O2).
   Computes the exact same three algebraic-data workloads and 64-bit
   checksums as kernels.ir, bench_c_arena.c and bench_filc_heap.c. *)

let next_rng (x : int) : int =
  ((x * 1664525) + 1013904223) land 0xFFFFFFFF

(* 1. Ephemeral + major-promoted list construction and tail-recursive sum *)

type int_list = Nil | Cons of int * int_list

let rec list_build_loop (n : int) (s : int) (acc : int_list) : int_list =
  if n <= 0 then acc
  else
    let s' = next_rng s in
    let v = s' land 1023 in
    list_build_loop (n - 1) s' (Cons (v, acc))

let list_build (n : int) (seed : int) : int_list =
  list_build_loop n seed Nil

let rec list_sum (xs : int_list) (acc : int) : int =
  match xs with
  | Nil -> acc
  | Cons (h, tl) -> list_sum tl (acc + h)

let bench_list (len : int) (rounds : int) : int64 =
  let keep = Sys.opaque_identity (list_build len 42) in
  let total = ref 0L in
  for r = 0 to rounds - 1 do
    let xs = list_build len (r + 1000) in
    let s1 = list_sum xs 0 in
    let s2 = list_sum keep 0 in
    total := Int64.add !total (Int64.of_int (s1 + s2))
  done;
  !total

(* 2. Nanofil.Term-shaped AST construction and structural equality *)

type term =
  | TInt of int
  | TAtom of int
  | TComp of int * term_list
and term_list =
  | TNil
  | TCons of term * term_list

let rec term_build (depth : int) (seed : int) (flip : int) : term =
  if depth <= 0 then
    if (seed land 1) = 0 then TInt ((seed lsr 1) + flip)
    else TAtom ((seed lsr 1) + flip)
  else
    let s0 = ((seed * 3) + 1) land 0xFFFF in
    let s1 = ((seed * 3) + 2) land 0xFFFF in
    let s2 = ((seed * 3) + 3) land 0xFFFF in
    let c0 = term_build (depth - 1) s0 0 in
    let c1 = term_build (depth - 1) s1 0 in
    let c2 = term_build (depth - 1) s2 flip in
    TComp (seed land 255, TCons (c0, TCons (c1, TCons (c2, TNil))))

let rec term_eqb (a : term) (b : term) : bool =
  match a, b with
  | TInt x, TInt y -> x = y
  | TAtom x, TAtom y -> x = y
  | TComp (f1, xs), TComp (f2, ys) ->
      if f1 <> f2 then false else term_list_eqb xs ys
  | _, _ -> false
and term_list_eqb (xs : term_list) (ys : term_list) : bool =
  match xs, ys with
  | TNil, TNil -> true
  | TCons (x, xr), TCons (y, yr) ->
      if term_eqb x y then term_list_eqb xr yr else false
  | _, _ -> false

let bench_term (depth : int) (rounds : int) : int64 =
  let base = Sys.opaque_identity (term_build depth 7 0) in
  let total = ref 0L in
  for r = 0 to rounds - 1 do
    let flip = r land 1 in
    let t = term_build depth 7 flip in
    let eq1 = if term_eqb base t then 1L else 0L in
    let eq2 = if term_eqb t t then 1L else 0L in
    total := Int64.add (Int64.add (Int64.mul !total 131L) (Int64.mul eq1 17L)) eq2
  done;
  !total

(* 3. Persistent AVL map (FMapAVL-style height-2 balancing) *)

type avl =
  | Leaf
  | Node of avl * int * int * avl * int

let avl_height = function
  | Leaf -> 0
  | Node (_, _, _, _, h) -> h

let avl_create (l : avl) (k : int) (v : int) (r : avl) : avl =
  let hl = avl_height l in
  let hr = avl_height r in
  let h = (if hl >= hr then hl else hr) + 1 in
  Node (l, k, v, r, h)

let avl_bal (l : avl) (k : int) (v : int) (r : avl) : avl =
  let hl = avl_height l in
  let hr = avl_height r in
  if hl > hr + 2 then
    match l with
    | Leaf -> assert false
    | Node (ll, lk, lv, lr, _) ->
        if avl_height ll >= avl_height lr then
          avl_create ll lk lv (avl_create lr k v r)
        else
          match lr with
          | Leaf -> assert false
          | Node (lrl, lrk, lrv, lrr, _) ->
              avl_create (avl_create ll lk lv lrl) lrk lrv (avl_create lrr k v r)
  else if hr > hl + 2 then
    match r with
    | Leaf -> assert false
    | Node (rl, rk, rv, rr, _) ->
        if avl_height rr >= avl_height rl then
          avl_create (avl_create l k v rl) rk rv rr
        else
          match rl with
          | Leaf -> assert false
          | Node (rll, rlk, rlv, rlr, _) ->
              avl_create (avl_create l k v rll) rlk rlv (avl_create rlr rk rv rr)
  else
    avl_create l k v r

let rec avl_insert (t : avl) (k : int) (v : int) : avl =
  match t with
  | Leaf -> Node (Leaf, k, v, Leaf, 1)
  | Node (l, nk, nv, r, h) ->
      if k = nk then Node (l, k, v, r, h)
      else if k < nk then avl_bal (avl_insert l k v) nk nv r
      else avl_bal l nk nv (avl_insert r k v)

let rec avl_lookup (t : avl) (k : int) : int =
  match t with
  | Leaf -> 0
  | Node (l, nk, nv, r, _) ->
      if k = nk then nv
      else if k < nk then avl_lookup l k
      else avl_lookup r k

let avl_build_n (nkeys : int) (seed0 : int) : avl =
  let s = ref seed0 in
  let t = ref Leaf in
  for i = 0 to nkeys - 1 do
    s := next_rng !s;
    let k = (!s lsr 16) land 4095 in
    t := avl_insert !t k (i + 1)
  done;
  !t

let bench_avl (nkeys : int) (rounds : int) : int64 =
  let base = Sys.opaque_identity (avl_build_n nkeys 99) in
  let total = ref 0L in
  for r = 0 to rounds - 1 do
    let t = avl_build_n nkeys ((r * 977) + 1) in
    let sum = ref 0 in
    for k = 0 to 4095 do
      sum := !sum + avl_lookup t k
    done;
    for k = 0 to 1023 do
      sum := !sum + avl_lookup base (k * 4)
    done;
    total := Int64.add !total (Int64.of_int !sum)
  done;
  !total

let now_ns () : int64 =
  Int64.of_float (Unix.gettimeofday () *. 1e9)

let () =
  let which = if Array.length Sys.argv > 1 then Sys.argv.(1) else "all" in
  let scale = if Array.length Sys.argv > 2 then Array.get Sys.argv 2 |> int_of_string else 1 in
  let run name f =
    let t0 = now_ns () in
    let res = f () in
    let dt_ms = Int64.to_float (Int64.sub (now_ns ()) t0) /. 1e6 in
    Printf.printf "%s\t%Lu\t%.3f\n%!" name res dt_ms
  in
  if which = "all" || which = "list" then
    run "list_sum" (fun () -> bench_list 4096 (2000 * scale));
  if which = "all" || which = "term" then
    run "term_eqb" (fun () -> bench_term 8 (200 * scale));
  if which = "all" || which = "avl" then
    run "avl" (fun () -> bench_avl 2048 (100 * scale))
