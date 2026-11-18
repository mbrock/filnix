(* Render the result of Transport.decode_module. All interpretation of the
   checked IR has already happened in Rocq. The layout pass groups complete
   items and blocks; their Gallina expressions are opaque to it. *)
[@@@warning "+8"]
[@@@warnerror "+8"]
open Nanofil_model

let app constructor arguments =
  "(" ^ String.concat " " (constructor :: arguments) ^ ")"

let list ?(sep="; ") render xs =
  let values = Array.of_list (List.map render xs) in
  let rec range start length =
    if length <= 64 then
      "[" ^ String.concat sep (Array.to_list (Array.sub values start length)) ^ "]"
    else
      let left = length / 2 in
      app "app" [range start left; range (start + left) (length - left)]
  in
  range 0 (Array.length values)

let pair left right (x, y) = "(" ^ left x ^ ", " ^ right y ^ ")"

let integer z =
  let s = Big_int_Z.string_of_big_int z in
  if s.[0] = '-' then "(" ^ s ^ ")" else s

let string s =
  if String.for_all (fun c -> c >= ' ' && c <= '~') s then
    "\"" ^ String.concat "\"\"" (String.split_on_char '"' s) ^ "\""
  else
    let byte c = app "ascii_of_nat" [string_of_int (Char.code c)] in
    app "string_of_list_ascii" [list byte (List.of_seq (String.to_seq s))]

let rec term = function
  | TInt z -> app "TInt" [integer z]
  | TAtom s -> app "a" [string s]
  | TList xs -> app "TList" [list term xs]
  | TApp (f, xs) -> app "TApp" [string f; list term xs]

let cls = function
  | W -> "W"
  | L -> "L"
  | P -> "P"
  | A -> "A"
  | F -> "F"
  | Single -> "Single"
  | Double -> "Double"
  | Extended -> "Extended"

let width = function
  | Wb -> "Wb"
  | Wh -> "Wh"
  | Ww -> "Ww"
  | Wl -> "Wl"
  | Wp -> "Wp"
  | Ws -> "Ws"
  | Wd -> "Wd"
  | Wx -> "Wx"

let narrow = function
  | Sw -> "Sw"
  | Uw -> "Uw"
  | Sh -> "Sh"
  | Uh -> "Uh"
  | Sb -> "Sb"
  | Ub -> "Ub"

let signedness = function
  | Signed -> "Signed"
  | Unsigned -> "Unsigned"

let load_type = function
  | LdL -> "LdL"
  | LdS -> "LdS"
  | LdD -> "LdD"
  | LdX -> "LdX"
  | LdNarrow x -> app "LdNarrow" [narrow x]

let cas_type = function
  | CasL -> "CasL"
  | CasP -> "CasP"
  | CasNarrow x -> app "CasNarrow" [narrow x]

let cond = function
  | Eq0 -> "Eq"
  | Ne -> "Ne"
  | Sle -> "Sle"
  | Slt -> "Slt"
  | Sge -> "Sge"
  | Sgt -> "Sgt"
  | Ule -> "Ule"
  | Ult -> "Ult"
  | Uge -> "Uge"
  | Ugt -> "Ugt"
  | Le -> "Le"
  | Lt0 -> "Lt"
  | Ge -> "Ge"
  | Gt0 -> "Gt"
  | Ord -> "Ord"
  | Unord -> "Unord"

let rights = function
  | Read -> "Read"
  | Write -> "Write"

let bound = function
  | Upper -> "Upper"
  | Lower -> "Lower"

let pointer_effect = function
  | AuxRead -> "AuxRead"
  | LowerResolve -> "LowerResolve"
  | AddressRead -> "AddressRead"
  | AtomicRead -> "AtomicRead"
  | AuxEnsure -> "AuxEnsure"
  | LowerBarrier -> "LowerBarrier"
  | RootedReload -> "RootedReload"
  | LowerWrite -> "LowerWrite"
  | AddressWrite -> "AddressWrite"
  | AtomicWrite -> "AtomicWrite"

let setjmp_kind = function
  | SjSetjmp -> "SjSetjmp"
  | SjUnderscore -> "SjUnderscore"
  | SjSig -> "SjSig"

let op = function
  | Add -> "Add"
  | Sub -> "Sub"
  | Mul -> "Mul"
  | Div -> "Div"
  | Udiv -> "Udiv"
  | Rem -> "Rem"
  | Urem -> "Urem"
  | And -> "And"
  | Or -> "Or"
  | Xor -> "Xor"
  | Sar -> "Sar"
  | Shr -> "Shr"
  | Shl -> "Shl"
  | Neg -> "Neg"
  | Copy -> "Copy"
  | Ptoi -> "Ptoi"
  | Itop -> "Itop"
  | Select -> "Select"
  | Cmp (condition, k) -> app "Cmp" [cond condition; cls k]
  | Ext x -> app "Ext" [narrow x]
  | ExtF x -> app "ExtF" [cls x]
  | Truncd -> "Truncd"
  | Truncx -> "Truncx"
  | FloatToInt (k, signed) -> app "FloatToInt" [cls k; signedness signed]
  | IntToFloat (k, signed) -> app "IntToFloat" [cls k; signedness signed]
  | Cast -> "Cast"
  | Sqrt -> "Sqrt"
  | Alloc x -> app "Alloc" [integer x]
  | Check (lo, hi, rights_, align) -> app "Check" [integer lo; integer hi; rights rights_; integer align]
  | CheckAhead (lo, hi, rights_, align, ahead) -> app "CheckAhead" [integer lo; integer hi; rights rights_; integer align; integer ahead]
  | Renew (lo, hi, rights_, align) -> app "Renew" [integer lo; integer hi; rights rights_; integer align]
  | RenewHull (lo, hi, rights_, align) -> app "RenewHull" [integer lo; integer hi; rights rights_; integer align]
  | HalfCheck (side, lo, hi, rights_, align) -> app "HalfCheck" [bound side; integer lo; integer hi; rights rights_; integer align]
  | SpanTest (lo, hi) -> app "SpanTest" [integer lo; integer hi]
  | RenewIf (lo, hi, rights_, align) -> app "RenewIf" [integer lo; integer hi; rights rights_; integer align]
  | Limit x -> app "Limit" [integer x]
  | CheckLimit (lo, hi, rights_, align) -> app "CheckLimit" [integer lo; integer hi; rights rights_; integer align]
  | CheckLocal (local, offset, bytes, rights_, align) -> app "CheckLocal" [term local; integer offset; integer bytes; rights rights_; integer align]
  | CheckFunction -> "CheckFunction"
  | RawLoad (kind, offset) -> app "RawLoad" [load_type kind; integer offset]
  | RawLoadPointer (offset, effects) -> app "RawLoadPointer" [integer offset; list pointer_effect effects]
  | RawCas (kind, offset) -> app "RawCas" [cas_type kind; integer offset]
  | VaArgs -> "VaArgs"
  | VaArg -> "VaArg"
  | Setjmp x -> app "Setjmp" [setjmp_kind x]

let value = function
  | Tmp (TAtom s) -> app "t" [string s]
  | Tmp x -> app "Tmp" [term x]
  | Const x -> app "Const" [integer x]
  | Global x -> app "Global" [term x]

let flight_arg = function
  | FValue x -> app "FValue" [value x]
  | FAddress x -> app "FAddress" [value x]

let flight_lower = function
  | LowerNone -> "LowerNone"
  | LowerOf x -> app "LowerOf" [value x]

let call_result = function
  | CVoid -> "CVoid"
  | CResult (dst, k) -> app "CResult" [term dst; cls k]
  | CTuple x -> app "CTuple" [list (pair term cls) x]

let arg = function
  | Arg (k, operand) -> app "Arg" [cls k; value operand]

let inst = function
  | Let (dst, k, operation, args) -> app "Let" [term dst; cls k; op operation; list value args]
  | Flight (dst, operation, args, lower) -> app "Flight" [term dst; op operation; list flight_arg args; flight_lower lower]
  | RawStore (size, offset, src, addr) -> app "RawStore" [width size; integer offset; value src; value addr]
  | RawStorePointer (offset, src, addr, effects) -> app "RawStorePointer" [integer offset; value src; value addr; list pointer_effect effects]
  | Call (result, callee, args) -> app "Call" [call_result result; value callee; list arg args]
  | RawCall (result, callee, args) -> app "RawCall" [call_result result; value callee; list arg args]
  | LocalAlloc (local, bytes) -> app "LocalAlloc" [term local; integer bytes]
  | Loc (file, line) -> app "Loc" [term file; integer line]
  | Touch x -> app "Touch" [term x]

let target = function
  | To x -> app "To" [term x]
  | Poll x -> app "Poll" [term x]

let jump = function
  | JGoto x -> app "JGoto" [target x]
  | JBranch (test, yes, no) -> app "JBranch" [value test; target yes; target no]
  | JRet x -> app "JRet" [value x]
  | JRets x -> app "JRets" [list value x]
  | JRetVoid -> "JRetVoid"
  | JUnreachable -> "JUnreachable"

let phi = function
  | Phi (dst, k, incoming) -> app "Phi" [term dst; cls k; list (pair term value) incoming]

let ret_type = function
  | RClass x -> app "RClass" [cls x]
  | RVoid -> "RVoid"
  | RTuple x -> app "RTuple" [list cls x]

let linkage = function
  | LExport -> "LExport"
  | LLocal -> "LLocal"
  | LWeak -> "LWeak"
  | LRo x -> app "LRo" [term x]
  | LTls x -> app "LTls" [term x]
  | LInit (which, priority) -> app "LInit" [term which; term priority]
  | LExternWeak -> "LExternWeak"
  | LOther x -> app "LOther" [term x]

let data_item = function
  | Item (size, bits) -> app "Item" [width size; integer bits]
  | Str x -> app "Str" [list integer x]
  | Sym (symbol, offset) -> app "Sym" [term symbol; integer offset]
  | Zero x -> app "Zero" [integer x]
  | ItemOther x -> app "ItemOther" [term x]

let block b =
  app "mkBlock" [term b.b_label; list phi b.b_phis;
    list ~sep:";\n      " inst b.b_insts; jump b.b_jump]

(* Each record begins with its kind and hex-encoded symbol spelling. An
   arbitrary term is a legal name too; the layout pass names it by position.
   Gallina strings above never contain literal tabs or newlines. *)
let record kind name body =
  let spelling = match name with
    | TAtom s ->
        let b = Buffer.create (2 * String.length s) in
        String.iter (fun c -> Printf.bprintf b "%02x" (Char.code c)) s;
        Buffer.contents b
    | _ -> "" in
  Printf.printf "%s\t%s\t%s\030" kind spelling body

let item = function
  | IFunc f ->
      List.iter (fun b -> record "block" f.fn_name (block b)) f.fn_blocks;
      record "func" f.fn_name (String.concat " " ["mkFunc"; term f.fn_name;
        term f.fn_linkage; ret_type f.fn_ret; list (pair cls term) f.fn_params])
  | IOutside (n, t) -> record "item" n (app "IOutside" [term n; term t])
  | IData (n, lk, align, items) ->
      record "item" n (app "IData" [term n; linkage lk; integer align; list data_item items])
  | IAlias (n, lk, target) -> record "item" n (app "IAlias" [term n; term lk; term target])
