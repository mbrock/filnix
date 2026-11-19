(** Startup locates Hello's streams, global cells and exit records.
    These two records identify the objects and specify which names and
    bounds main expects when it starts. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Values Memory Semantics.
From Glibc Require Import FileInv AtexitLogic HelloLiterals.
Open Scope Z_scope.

(** The linked program supplies the stream, name, option, allocator and
    exit-state objects read by the proof. This record identifies their
    addresses and bounds without fixing a particular memory layout. *)
Record hello_objs : Type := mkHelloObjs {
  ho_out : ptr; ho_err : ptr; ho_in : ptr;
  ho_so : Z; ho_soreg : region; ho_se : Z; ho_sereg : region;
  ho_oa : Z; ho_oareg : region; ho_oi : Z; ho_oireg : region;
  ho_vb : Z; ho_vreg : region; ho_sb : Z; ho_sreg : region; ho_eb : Z; ho_ereg : region;
  ho_x : exit_objs; ho_el : Z; ho_elr : region; ho_cp : ptr; ho_fcp : ptr;
  ho_mp : Z; ho_mpreg : region; ho_tc : Z; ho_tcreg : region; ho_dm : Z; ho_dmreg : region;
  ho_pb : Z; ho_nb : Z; ho_nsb : Z; ho_preg : region; ho_nreg : region; ho_nsreg : region;
  ho_lp : ptr; ho_tp : ptr
}.

(** The entry contract names the globals read by main and records their
    cell bounds. These facts do not depend on a logic instance. *)
Record hello_layout (ge : genv) (o : hello_objs) : Prop := mkHelloLayout {
  hy_lits : forall s, In s hello_lits -> lookup (TAtom s) (ge_globals ge) = Some (sym_ptr ge s);
  hy_cp : lookup (TAtom "close_stdout") (ge_globals ge) = Some (ho_cp o);
  hy_so : lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr (ho_so o) (Obj (ho_so o)));
  hy_so_at : 0 <= ho_so o /\ ho_so o mod 8 = 0 /\ ho_so o + 8 <= r_end (ho_soreg o) /\ r_end (ho_soreg o) <= 2 ^ 48;
  hy_se : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr (ho_se o) (Obj (ho_se o)));
  hy_se_at : 0 <= ho_se o /\ ho_se o mod 8 = 0 /\ ho_se o + 8 <= r_end (ho_sereg o) /\ r_end (ho_sereg o) <= 2 ^ 48;
  hy_oa : lookup (TAtom "optarg") (ge_globals ge) = Some (mkPtr (ho_oa o) (Obj (ho_oa o)));
  hy_oa_at : 0 <= ho_oa o /\ ho_oa o mod 8 = 0 /\ ho_oa o + 8 <= r_end (ho_oareg o) /\ r_end (ho_oareg o) <= 2 ^ 48;
  hy_oi : lookup (TAtom "optind") (ge_globals ge) = Some (mkPtr (ho_oi o) (Obj (ho_oi o)));
  hy_oi_at : 0 <= ho_oi o /\ ho_oi o + 4 <= r_end (ho_oireg o) /\ r_end (ho_oireg o) <= 2 ^ 48;
  hy_pb : lookup (TAtom "program_name") (ge_globals ge) = Some (mkPtr (ho_pb o) (Obj (ho_pb o)));
  hy_pb_at : 0 <= ho_pb o /\ ho_pb o mod 8 = 0 /\ ho_pb o + 8 <= r_end (ho_preg o) /\ r_end (ho_preg o) <= 2 ^ 48;
  hy_eb_at : 0 < ho_eb o /\ ho_eb o + 4 <= r_end (ho_ereg o) /\ r_end (ho_ereg o) <= 2 ^ 48
}.
