(** Each frame rewrite must preserve exactly the finite set of admitted names.
    These equivalences quantify over every name, including names outside the list.
    Each proof checks one reviewed conversion without assuming any runtime rules. *)

From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax.
From Glibc Require Import GlibcEnv.
Import ListNotations.
Open Scope string_scope.

(* hi_atexit/HiAtexitPutsNl.v: hi_puts_L180. *)
Lemma HiAtexitPutsNl_hi_puts_L180_names (x : name) :
  List.In x (atoms ["v0"; "v6"; "v12"; "chk1"]) <->
  (x = TAtom "v0" \/ x = TAtom "v6" \/ x = TAtom "v12" \/ x = TAtom "chk1").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions HiAtexitPutsNl_hi_puts_L180_names.

(* libio/LibioFputsCall.v: wp_fputs_L113. *)
Lemma LibioFputsCall_wp_fputs_L113_names (x : name) :
  List.In x (atoms ["v0"; "v6"; "v2"; "chk0"]) <->
  (x = TAtom "v0" \/ x = TAtom "v6" \/ x = TAtom "v2" \/ x = TAtom "chk0").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioFputsCall_wp_fputs_L113_names.

(* libio/LibioFputsCall.v: wp_fputs_L161. *)
Lemma LibioFputsCall_wp_fputs_L161_names (x : name) :
  List.In x (atoms ["v0"; "v6"; "v2"; "chk0"]) <->
  (x = TAtom "v0" \/ x = TAtom "v6" \/ x = TAtom "v2" \/ x = TAtom "chk0").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioFputsCall_wp_fputs_L161_names.

(* libio/LibioPuts.v: Hnl. *)
Lemma LibioPuts_Hnl_names (x : name) :
  List.In x (atoms ["v0"; "v6"; "v12"; "chk1"]) <->
  (x = TAtom "v0" \/ x = TAtom "v6" \/ x = TAtom "v12" \/ x = TAtom "chk1").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioPuts_Hnl_names.

(* libio/LibioPutsCall.v: wp_puts_L162_for. *)
Lemma LibioPutsCall_wp_puts_L162_for_names (x : name) :
  List.In x (atoms ["v0"; "v6"; "v12"; "chk1"]) <->
  (x = TAtom "v0" \/ x = TAtom "v6" \/ x = TAtom "v12" \/ x = TAtom "chk1").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioPutsCall_wp_puts_L162_for_names.

(* libio/LibioPutsMode.v: wp_puts_L109_for. *)
Lemma LibioPutsMode_wp_puts_L109_for_names (x : name) :
  List.In x (atoms ["v0"; "v6"; "v12"; "chk1"]) <->
  (x = TAtom "v0" \/ x = TAtom "v6" \/ x = TAtom "v12" \/ x = TAtom "chk1").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioPutsMode_wp_puts_L109_for_names.

(* libio/LibioPutsNl.v: wp_puts_L180. *)
Lemma LibioPutsNl_wp_puts_L180_names (x : name) :
  List.In x (atoms ["v0"; "v6"; "v12"; "chk1"]) <->
  (x = TAtom "v0" \/ x = TAtom "v6" \/ x = TAtom "v12" \/ x = TAtom "chk1").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioPutsNl_wp_puts_L180_names.

(* libio/LibioWrite.v: Hcall. *)
Lemma LibioWrite_Hcall_names (x : name) :
  List.In x (atoms ["v0"; "v4"; "pr.1"; "pr.2"]) <->
  (x = TAtom "v0" \/ x = TAtom "v4" \/ x = TAtom "pr.1" \/ x = TAtom "pr.2").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioWrite_Hcall_names.

(* libio/LibioWriteCall.v: wp_file_write_call. *)
Lemma LibioWriteCall_wp_file_write_call_names (x : name) :
  List.In x (atoms ["v0"; "v4"; "pr.1"; "pr.2"]) <->
  (x = TAtom "v0" \/ x = TAtom "v4" \/ x = TAtom "pr.1" \/ x = TAtom "pr.2").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioWriteCall_wp_file_write_call_names.

(* libio/LibioWriteCallDq.v: wp_file_write_call_dq. *)
Lemma LibioWriteCallDq_wp_file_write_call_dq_names (x : name) :
  List.In x (atoms ["v0"; "v4"; "pr.1"; "pr.2"]) <->
  (x = TAtom "v0" \/ x = TAtom "v4" \/ x = TAtom "pr.1" \/ x = TAtom "pr.2").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioWriteCallDq_wp_file_write_call_dq_names.

(* libio/LibioWriteCallDq.v: wp_file_write_call_nocancel_dq. *)
Lemma LibioWriteCallDq_wp_file_write_call_nocancel_dq_names (x : name) :
  List.In x (atoms ["v0"; "v4"; "pr.1"; "pr.2"]) <->
  (x = TAtom "v0" \/ x = TAtom "v4" \/ x = TAtom "pr.1" \/ x = TAtom "pr.2").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioWriteCallDq_wp_file_write_call_nocancel_dq_names.

(* libio/LibioWriteJoinDq.v: wp_file_write_join_dq. *)
Lemma LibioWriteJoinDq_wp_file_write_join_dq_names (x : name) :
  List.In x (atoms ["v0"; "v4"; "pr.1"; "pr.2"]) <->
  (x = TAtom "v0" \/ x = TAtom "v4" \/ x = TAtom "pr.1" \/ x = TAtom "pr.2").
Proof. cbn [atoms List.map List.In]. intuition congruence. Qed.
Print Assumptions LibioWriteJoinDq_wp_file_write_join_dq_names.
