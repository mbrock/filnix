(** GNU, Clang, and C23 attributes can alter struct layout, symbol linkage, or
    scope-exit cleanup, so the parser refuses any attribute that the compiler
    does not explicitly classify. This module holds the classification table
    from c_types.pl together with the validation helpers that c_parse.pl runs
    while reading attributes.

    All string comparisons use [String.eqb] rather than pattern matching on
    string literals so extraction stays compact and maps directly to native
    string equality under both OCaml extraction and λANF. *)

From Stdlib Require Import String ZArith List Bool Ascii.
From Frontend Require Import CAst.
Import ListNotations.
Local Open Scope string_scope.

(** ## Attribute classification

    Every recognized attribute is either [AttrHonored], meaning nanofil gives
    it semantic effect or explicitly rejects unsupported uses, or [AttrHint],
    meaning nanofil may drop it without changing program meaning. *)

(** Classification of a recognized attribute name. *)
Inductive attr_kind : Type :=
| AttrHonored
| AttrHint.

Definition str_in (s : string) (xs : list string) : bool :=
  existsb (String.eqb s) xs.

Definition honored_attr_names : list string :=
  [ "aligned"; "packed"; "nanofil_pack"; "transparent_union";
    "cleanup"; "mode"; "vector_size"; "ext_vector_type";
    "address_space"; "section"; "weak"; "alias"; "weakref";
    "constructor"; "destructor"; "gnu_inline"; "overloadable";
    "common" ].

Definition hint_attr_names : list string :=
  [ "always_inline"; "noinline"; "flatten"; "artificial"; "nodebug";
    "hot"; "cold"; "optimize"; "optnone"; "target"; "min_vector_width";
    "noreturn"; "returns_twice"; "leaf"; "nothrow"; "pure"; "const";
    "malloc"; "alloc_size"; "alloc_align"; "align_value"; "assume_aligned";
    "returns_nonnull"; "nonnull"; "noescape"; "nonnull_if_nonzero";
    "format"; "format_arg"; "sentinel"; "access"; "fd_arg"; "fd_arg_read";
    "fd_arg_write"; "null_terminated_string_arg"; "tainted_args";
    "warn_unused_result"; "nodiscard"; "deprecated"; "unavailable";
    "error"; "warning"; "diagnose_if"; "diagnose_as_builtin"; "enable_if";
    "pass_object_size"; "pass_dynamic_object_size"; "unused"; "maybe_unused";
    "used"; "retain"; "externally_visible"; "visibility"; "noipa";
    "noclone"; "no_icf"; "no_reorder"; "no_instrument_function";
    "no_profile_instrument_function"; "no_sanitize"; "no_sanitize_address";
    "no_sanitize_thread"; "no_sanitize_undefined";
    "no_address_safety_analysis"; "no_stack_protector"; "stack_protect";
    "no_split_stack"; "zero_call_used_regs"; "nocf_check"; "cf_check";
    "indirect_return"; "patchable_function_entry"; "noplt"; "tls_model";
    "uninitialized"; "nocommon"; "sysv_abi"; "stdcall"; "cdecl";
    "fastcall"; "thiscall"; "capability"; "shared_capability"; "lockable";
    "scoped_lockable"; "guarded_by"; "pt_guarded_by"; "guarded_var";
    "pt_guarded_var"; "acquired_before"; "acquired_after";
    "requires_capability"; "requires_shared_capability";
    "exclusive_locks_required"; "shared_locks_required"; "acquire_capability";
    "acquire_shared_capability"; "exclusive_lock_function";
    "shared_lock_function"; "release_capability"; "release_shared_capability";
    "release_generic_capability"; "unlock_function"; "try_acquire_capability";
    "try_acquire_shared_capability"; "exclusive_trylock_function";
    "shared_trylock_function"; "assert_capability";
    "assert_shared_capability"; "assert_exclusive_lock"; "assert_shared_lock";
    "locks_excluded"; "lock_returned"; "no_thread_safety_analysis";
    "force_align_arg_pointer"; "analyzer_noreturn"; "regparm"; "simd";
    "nonstring"; "counted_by"; "strict_flex_array"; "designated_init";
    "flag_enum"; "enum_extensibility"; "warn_if_not_aligned"; "copy";
    "fallthrough"; "likely"; "unlikely"; "assume"; "musttail"; "nomerge";
    "reproducible"; "unsequenced"; "may_alias"; "bitwise" ].

(** Look up an attribute name after stripping GCC's surrounding double
    underscores. *)
Definition known_attribute (w : string) : option attr_kind :=
  if str_in w honored_attr_names then Some AttrHonored
  else if str_in w hint_attr_names then Some AttrHint
  else None.

(** Honored attributes that describe a declared symbol rather than a pointed-to
    type may slide from pointer qualifiers onto the enclosing declaration. *)
Definition is_decl_attribute (w : string) : bool :=
  str_in w [ "weak"; "section"; "alias"; "weakref";
             "constructor"; "destructor"; "gnu_inline"; "common" ].

(** Clang nullability qualifiers on pointer types carry no runtime effect in
    nanofil and are ignored. *)
Definition is_nullability (s : string) : bool :=
  str_in s [ "_Nullable"; "_Nonnull"; "_Null_unspecified"; "_Nullable_result" ].

(** ## Attribute token helpers

    GNU attributes wrap comma-separated items inside nested parentheses and
    allow optional leading and trailing double underscores on each name. *)

(** Strip matching leading and trailing double underscores when the inner name
    is non-empty. *)
Definition strip_dunders (w : string) : string :=
  let n := String.length w in
  if (5 <=? n)%nat then
    if String.eqb (String.substring 0 2 w) "__" &&
       String.eqb (String.substring (n - 2) 2 w) "__"
    then String.substring 2 (n - 4) w
    else w
  else w.

(** Extract the normalized name from the leading token of an attribute item. *)
Definition attr_tok_name (t : attr_tok) : option string :=
  match t with
  | ATok (TId w) | ATok (TKw w) => Some (strip_dunders w)
  | _ => None
  end.

(** Split an attribute token list on top-level commas. *)
Fixpoint split_attr_items_acc (cur : list attr_tok) (ts : list attr_tok)
  : list (list attr_tok) :=
  match ts with
  | [] => [rev_append cur []]
  | ATok (TPunct p) :: rest =>
      if String.eqb p "," then
        rev_append cur [] :: split_attr_items_acc [] rest
      else
        split_attr_items_acc (ATok (TPunct p) :: cur) rest
  | t :: rest =>
      split_attr_items_acc (t :: cur) rest
  end.

Definition attribute_items (ts : list attr_tok) : list (list attr_tok) :=
  split_attr_items_acc [] ts.

(** Collect every normalized attribute name inside a balanced GNU attribute
    argument list. *)
Definition extract_attr_names (ts : list attr_tok) : list string :=
  flat_map
    (fun t =>
       match t with
       | AGroup inner =>
           flat_map
             (fun item =>
                match item with
                | h :: _ =>
                    match attr_tok_name h with
                    | Some w => [w]
                    | None => []
                    end
                | [] => []
                end)
             (attribute_items inner)
       | ATok _ => []
       end)
    ts.

(** Format an integer in decimal for error messages and local-label suffixes. *)
Fixpoint z_pos_to_string_aux (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | O => acc
  | S f =>
      let d := ascii_of_nat (48 + Z.to_nat (z mod 10)) in
      let q := (z / 10)%Z in
      if (q =? 0)%Z then String d acc
      else z_pos_to_string_aux f q (String d acc)
  end.

Definition z_to_string (z : Z) : string :=
  if (z <? 0)%Z then "-" ++ z_pos_to_string_aux 64 (- z) ""
  else z_pos_to_string_aux 64 z "".

Definition loc_to_string (l : c_loc) : string :=
  match l with
  | Loc f n => f ++ ":" ++ z_to_string n
  | LocEof => "end of input"
  end.

(** Verify that every attribute in a GNU attribute list is recognized. *)
Definition check_known_attributes (ts : list attr_tok) (l : c_loc) : c_result unit :=
  let fix go (ws : list string) : c_result unit :=
    match ws with
    | [] => COk tt
    | w :: rest =>
        match known_attribute w with
        | Some _ => go rest
        | None => CErr (loc_to_string l ++ ": attribute " ++ w ++ " is not supported")
        end
    end in
  go (extract_attr_names ts).

(** Verify that every attribute in a discarded position is only a hint. *)
Definition check_hint_attributes (ts : list attr_tok) (l : c_loc) : c_result unit :=
  let fix go (ws : list string) : c_result unit :=
    match ws with
    | [] => COk tt
    | w :: rest =>
        match known_attribute w with
        | Some AttrHonored =>
            CErr (loc_to_string l ++ ": attribute " ++ w ++ " is not supported in this position")
        | _ => go rest
        end
    end in
  go (extract_attr_names ts).

(** Return the first honored attribute name in a specifier list, if any. *)
Definition first_honored_attr (specs : list c_spec) : option string :=
  let fix go_names (ws : list string) : option string :=
    match ws with
    | [] => None
    | w :: rest =>
        match known_attribute w with
        | Some AttrHonored => Some w
        | _ => go_names rest
        end
    end in
  let fix go_specs (ss : list c_spec) : option string :=
    match ss with
    | [] => None
    | SpAttr ts :: rest =>
        match go_names (extract_attr_names ts) with
        | Some w => Some w
        | None => go_specs rest
        end
    | _ :: rest => go_specs rest
    end in
  go_specs specs.

(** Check whether all honored attributes in a GNU attribute list are symbol
    declaration attributes eligible to slide off a pointer qualifier list. *)
Definition all_honored_are_decl (ts : list attr_tok) : bool :=
  forallb
    (fun w =>
       match known_attribute w with
       | Some AttrHonored => is_decl_attribute w
       | _ => true
       end)
    (extract_attr_names ts).

(** Remove a bare `packed` item from a single-group GNU attribute list on an
    enum definition, reporting whether `packed` was present. *)
Fixpoint remove_packed_item (items : list (list attr_tok))
  : option (list (list attr_tok)) :=
  match items with
  | [] => None
  | [t] :: rest =>
      match attr_tok_name t with
      | Some w =>
          if String.eqb w "packed" then Some rest
          else
            match remove_packed_item rest with
            | Some r => Some ([t] :: r)
            | None => None
            end
      | None =>
          match remove_packed_item rest with
          | Some r => Some ([t] :: r)
          | None => None
          end
      end
  | item :: rest =>
      match remove_packed_item rest with
      | Some r => Some (item :: r)
      | None => None
      end
  end.

Fixpoint join_attr_items (items : list (list attr_tok)) : list attr_tok :=
  match items with
  | [] => []
  | [i] => i
  | i :: rest => (i ++ (ATok (TPunct ",") :: join_attr_items rest))%list
  end.

Definition select_packed (ts : list attr_tok) : option (list attr_tok) :=
  match ts with
  | [AGroup inner] =>
      match remove_packed_item (attribute_items inner) with
      | Some others => Some [AGroup (join_attr_items others)]
      | None => None
      end
  | _ => None
  end.

(** Map supported `__declspec(...)` forms to equivalent GNU attribute lists. *)
Definition declspec_attr (ts : list attr_tok) : option (list attr_tok) :=
  match ts with
  | ATok (TId w) :: arg =>
      if String.eqb w "align" then
        Some [AGroup (ATok (TId "aligned") :: arg)]
      else if str_in w [ "noreturn"; "noinline"; "noalias"; "deprecated";
                         "nothrow"; "restrict"; "dllexport"; "dllimport";
                         "novtable" ] then
        Some [AGroup (ATok (TId w) :: arg)]
      else None
  | _ => None
  end.

(** Validate a C23 `[[...]]` attribute entry and reject honored ones that
    nanofil does not preserve in C23 syntax. *)
Definition check_c23_known (prefix : option string) (name0 : string) (l : c_loc)
  : c_result unit :=
  let check_hint (w : string) : c_result unit :=
    match known_attribute w with
    | Some AttrHonored =>
        let shown :=
          match prefix with
          | None => w
          | Some p => p ++ "::" ++ w
          end in
        CErr (loc_to_string l ++ ": the C23 attribute [[" ++ shown ++ "]] is not supported")
    | _ => COk tt
    end in
  match prefix with
  | None =>
      let name := strip_dunders name0 in
      if str_in name [ "deprecated"; "fallthrough"; "maybe_unused"; "nodiscard";
                       "noreturn"; "_Noreturn"; "reproducible"; "unsequenced" ]
      then COk tt
      else
        match known_attribute name with
        | None => CErr (loc_to_string l ++ ": attribute " ++ name ++ " is not supported")
        | Some _ => check_hint name
        end
  | Some p =>
      if str_in p [ "gnu"; "__gnu__"; "clang"; "_Clang" ] then
        let w := strip_dunders name0 in
        match known_attribute w with
        | None => CErr (loc_to_string l ++ ": attribute " ++ w ++ " is not supported")
        | Some _ => check_hint w
        end
      else COk tt
  end.
