(** These checked bodies implement cancellation-state changes and printf-buffer
    completion in user-glibc 2.44. The fixture supports instruction proofs
    without treating either function as an external contract.

    rocq/glibc/stdio/code.sh reproduces these terms from the pinned capture
    with gallina.pl. Do not edit. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** This term contains the selected checked function bodies. *)
Definition printf_state_term : term :=
  TApp "module" [TList [
    cap_fn{ "export" "__GI___pthread_setcancelstate" [param "w" %"v0"; param "p" %"v2"] -> "w"
      {
        @"start":
          %"v9" : "w" = op "cmp"("slt", "w") %"v0", #0
          => br %"v9" ? "L11" : "L10";
        @"L10":
          %"v13" : "w" = op "cmp"("sgt", "w") %"v0", #1
          => goto "L11";
        @"L11" [phi %"v15" : "w" = ("start" => #1, "L10" => %"v13")]:
          => br %"v15" ? "L5" : "L7";
        @"L5":
          => ret #22;
        @"L7":
          call %"v17" : "p" = $"zthread_self_cookie"();
          %"v20" = %"v17" +p #792;
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"v20";
          %"v21" : "w" = op "raw_load"("sw", int 0) %"chk0"
          => goto "L22";
        @"L22" [phi %"pr.1" : "w" = ("L7" => %"v21", "L71" => %"pr.2")]:
          %"v30" : "w" = op "cmp"("eq", "w") %"v0", #1
          => br %"v30" ? "L26" : "L27";
        @"L26":
          %"v33" : "w" = "or" %"pr.1", #1
          => goto "L28";
        @"L27":
          %"v37" : "w" = "and" %"pr.1", #4294967294
          => goto "L28";
        @"L28" [phi %"v38" : "w" = ("L26" => %"v33", "L27" => %"v37")]:
          %"v43" : "l" = "ptoi" %"v2";
          %"v44" : "l" = "ptoi" #0;
          %"v45" : "w" = op "cmp"("ne", "l") %"v43", %"v44"
          => br %"v45" ? "L39" : "L41";
        @"L39":
          %"v52" : "w" = "and" %"pr.1", #1
          => br %"v52" ? "L49" : "L48";
        @"L48":
          => goto "L49";
        @"L49" [phi %"v53" : "w" = ("L48" => #0, "L39" => #1)]:
          %"chk1" : "a" = op "check"(int 0, int 4, "write", int 1) %"v2";
          store "w" [%"chk1" + 0] <- %"v53"
          => goto "L41";
        @"L41":
          %"v59" : "w" = op "cmp"("eq", "w") %"pr.1", %"v38"
          => br %"v59" ? "L24" : "L56";
        @"L56":
          %"v65" = %"v17" +p #792;
          %"chk2" : "a" = op "half_check"("lower", int 0, int 4, "write", int 4) %"chk0", %"v65";
          %"v68" : "w" = op "raw_cas"("sw", int 0) %"chk2", %"pr.1", %"v38";
          %"v69" : "w" = op "cmp"("eq", "w") %"v68", %"pr.1"
          => br %"v69" ? "L71" : "L70";
        @"L70":
          => goto "L71";
        @"L71" [phi %"pr.2" : "w" = ("L56" => %"pr.1", "L70" => %"v68")]:
          => br %"v69" ? "iw_1.start" : poll "L22";
        @"iw_1.start":
          %"iw_1.v12" : "w" = "and" %"v38", #59;
          %"iw_1.v16" : "w" = op "cmp"("eq", "w") %"iw_1.v12", #10
          => br %"iw_1.v16" ? "L72" : "L24";
        @"L72":
          (op "flight"(%"v80", "copy", [#18446744073709551615], "none"));
          call %"iw_2.v3" : "p" = $"zthread_self_cookie"();
          %"iw_2.v5" = %"iw_2.v3" +p #1608;
          %"chk3" : "a" = op "check"(int 0, int 8, "write", int 8) %"iw_2.v5";
          store.ptr [%"chk3" + 0] <- %"v80";
          %"iw_2.v9" = %"iw_2.v3" +p #792;
          %"chk4" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk3", %"iw_2.v9";
          %"iw_2.v10" : "w" = op "raw_load"("sw", int 0) %"chk4"
          => goto "iw_2.L12";
        @"iw_2.L12" [phi %"iw_2.pr.1" : "w" = ("iw_2.L38" => %"iw_2.pr.2", "L72" => %"iw_2.v10")]:
          %"iw_2.v17" : "w" = "or" %"iw_2.pr.1", #1;
          %"iw_2.v19" : "w" = "or" %"iw_2.v17", #16;
          %"iw_2.v23" : "w" = "and" %"iw_2.v19", #4294967293;
          %"iw_2.v29" : "w" = op "cmp"("eq", "w") %"iw_2.pr.1", %"iw_2.v23"
          => br %"iw_2.v29" ? "iw_2.L14" : "iw_2.L13";
        @"iw_2.L13":
          %"iw_2.v32" = %"iw_2.v3" +p #792;
          %"chk5" : "a" = op "half_check"("lower", int 0, int 4, "write", int 4) %"chk3", %"iw_2.v32";
          %"iw_2.v35" : "w" = op "raw_cas"("sw", int 0) %"chk5", %"iw_2.pr.1", %"iw_2.v23";
          %"iw_2.v36" : "w" = op "cmp"("eq", "w") %"iw_2.v35", %"iw_2.pr.1"
          => br %"iw_2.v36" ? "iw_2.L38" : "iw_2.L37";
        @"iw_2.L37":
          => goto "iw_2.L38";
        @"iw_2.L38" [phi %"iw_2.pr.2" : "w" = ("iw_2.L13" => %"iw_2.pr.1", "iw_2.L37" => %"iw_2.v35")]:
          %"iw_2.v39" : "w" = op "cmp"("ne", "w") %"iw_2.v35", %"iw_2.pr.1"
          => br %"iw_2.v39" ? poll "iw_2.L12" : "iw_2.L14";
        @"iw_2.L14":
          %"iw_2.v41" = %"iw_2.v3" +p #784;
          %"chk6" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk3", %"iw_2.v41";
          %"iw_2.v42" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          call void $"__GI___pthread_unwind"("p" %"iw_2.v42")
          => goto "L24";
        @"L24":
          => ret #0
      } };
    cap_fn{ "export" "__printf_buffer_done" [param "p" %"v0"] -> "w"
      {
        @"start":
          %"iw_1.v3" = %"v0" +p #32;
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"iw_1.v3";
          %"iw_1.v4" : "w" = op "raw_load"("uw", int 0) %"chk0";
          %"iw_1.v5" : "w" = op "cmp"("eq", "w") %"iw_1.v4", #0
          => br %"iw_1.v5" ? "L2" : "L4";
        @"L2":
          => ret #4294967295;
        @"L4":
          %"v12" = %"v0" +p #8;
          %"chk1" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v12";
          %"v13" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"chk2" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v0";
          %"v15" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk2";
          %"v16" : "l" = "ptoi" %"v13";
          %"v17" : "l" = "ptoi" %"v15";
          %"v18" : "l" = "sub" %"v16", %"v17";
          %"v24" = %"v0" +p #24;
          %"v25" : "l" = op "raw_load"("l", int (-8)) %"chk0";
          %"v27" : "l" = "add" %"v25", %"v18";
          %"v28" : "w" = op "cmp"("ult", "l") %"v27", %"v25";
          %"v29" : "l" = op "ext"("uw") %"v28";
          %"v32" : "l" = op "ext"("sw") %"v27";
          %"v33" : "l" = "sar" %"v32", #63;
          %"v34" : "w" = op "cmp"("ne", "l") %"v27", %"v32";
          %"v35" : "w" = op "cmp"("ne", "l") %"v29", %"v33";
          %"v36" : "w" = "or" %"v34", %"v35"
          => br %"v36" ? "L20" : "L21";
        @"L20":
          %"v37" : "p" = "copy" $"__libc_errno";
          %"chk4" : "a" = op "check"(int 0, int 4, "write", int 1) %"v37";
          store "w" [%"chk4" + 0] <- #75
          => ret #4294967295;
        @"L21":
          %"v40" : "w" = "copy" %"v27"
          => ret %"v40"
      } }
  ]].

From Nanofil Require Import Syntax Transport Semantics.

(** Decoding gives the actual checked function bodies, not their specifications. *)
Definition printf_state_module : module := Eval vm_compute in
  code_module printf_state_term.

(** Computation checks that decoding did not take the empty fallback. *)
Lemma printf_state_decodes : decode_module printf_state_term = Some printf_state_module.
Proof. vm_compute. reflexivity. Qed.

(** Function lookup selects a decoded body for the subsequent instruction proofs. *)
Definition printf_state_fn (n : string) : func :=
  code_function printf_state_module n.

(** This body changes the thread's cancellation flag and optionally saves its old value. *)
Definition glibc___pthread_setcancelstate : func := Eval vm_compute in
  printf_state_fn "__GI___pthread_setcancelstate".

(** This body returns the accumulated count or reports failure and integer overflow. *)
Definition glibc___printf_buffer_done : func := Eval vm_compute in
  printf_state_fn "__printf_buffer_done".

(** Lookup finds the cancellation body rather than the empty fallback. *)
Lemma printf_state_find_cancel :
  find_direct (TAtom "__GI___pthread_setcancelstate") printf_state_module =
  Some (Defined glibc___pthread_setcancelstate).
Proof. vm_compute. reflexivity. Qed.

(** Lookup finds the completion body rather than the empty fallback. *)
Lemma printf_state_find_done :
  find_direct (TAtom "__printf_buffer_done") printf_state_module =
  Some (Defined glibc___printf_buffer_done).
Proof. vm_compute. reflexivity. Qed.
