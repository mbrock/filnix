(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_fn___GI___underflow : func :=
  mkFunc (a "__GI___underflow") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v24") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v24")]);
      (Let (a "v25") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v26") W (Cmp Eq W) [(t "v25"); (Const 0)])] (JBranch (t "v26") (To (a "L20")) (To (a "L22"))));
  (mkBlock (a "L20") [] [(Flight (a "v28") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk1") A (Renew 0 4 Write 1) [(t "chk0"); (t "v28")]);
      (RawStore Ww 0 (Const 4294967295) (t "chk1"))] (JGoto (To (a "L22"))));
  (mkBlock (a "L22") [] [(Flight (a "v31") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v32") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v55") W (Cmp Ne W) [(t "v32"); (Const 4294967295)])] (JBranch (t "v55") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L4") [] [(Flight (a "v64") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v65") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v66") W (Cmp Eq W) [(t "v65"); (Const 0)])] (JBranch (t "v66") (To (a "L69")) (To (a "L62"))));
  (mkBlock (a "L69") [] [(Flight (a "v83") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v84") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v85") W (Cmp Eq W) [(t "v84"); (Const 0)])] (JBranch (t "v85") (To (a "L79")) (To (a "L81"))));
  (mkBlock (a "L79") [] [(Flight (a "v87") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk5") A (Renew 0 4 Write 1) [(t "chk0"); (t "v87")]);
      (RawStore Ww 0 (Const 4294967295) (t "chk5"))] (JGoto (To (a "L81"))));
  (mkBlock (a "L81") [] [(Flight (a "v90") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v91") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")])] (JGoto (To (a "L62"))));
  (mkBlock (a "L62") [] [(Let (a "chk7") A (HalfCheck Lower 0 4 Read 1) [(t "chk0"); (t "v0")]);
      (Let (a "v117") W (RawLoad (LdNarrow Sw) 0) [(t "chk7")]);
      (Let (a "v118") W And [(t "v117"); (Const 2048)])] (JBranch (t "v118") (To (a "L113")) (To (a "L115"))));
  (mkBlock (a "L113") [] [(Call (CResult (a "v123") W) (Global (a "__GI__IO_switch_to_get_mode")) [(Arg P (t "v0"))]);
      (Let (a "v125") W (Cmp Eq W) [(t "v123"); (Const 4294967295)])] (JBranch (t "v125") (To (a "L119")) (To (a "L115"))));
  (mkBlock (a "L119") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L115") [] [(Flight (a "v132") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk8") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v132")]);
      (Let (a "v133") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Flight (a "v135") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk9") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v135")]);
      (Let (a "v136") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Let (a "v137") L Ptoi [(t "v133")]);
      (Let (a "v138") L Ptoi [(t "v136")]);
      (Let (a "v139") W (Cmp Ult L) [(t "v137"); (t "v138")])] (JBranch (t "v139") (To (a "L128")) (To (a "L130"))));
  (mkBlock (a "L128") [] [(Flight (a "v141") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v142") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk11") A (Check 0 1 Read 1) [(t "v142")]);
      (Let (a "v143") W (RawLoad (LdNarrow Ub) 0) [(t "chk11")])] (JRet (t "v143")));
  (mkBlock (a "L130") [] [(Let (a "chk12") A (Renew 0 4 Read 1) [(t "chk7"); (t "v0")]);
      (Let (a "v149") W (RawLoad (LdNarrow Sw) 0) [(t "chk12")]);
      (Let (a "v150") W And [(t "v149"); (Const 256)])] (JBranch (t "v150") (To (a "L145")) (To (a "L147"))));
  (mkBlock (a "L145") [] [(Call CVoid (Global (a "_IO_switch_to_main_get_area")) [(Arg P (t "v0"))]);
      (Flight (a "v156") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk13") A (Renew 0 8 Read 8) [(t "chk8"); (t "v156")]);
      (Let (a "v157") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk13")]);
      (Flight (a "v159") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk14") A (Renew 0 8 Read 8) [(t "chk9"); (t "v159")]);
      (Let (a "v160") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk14")]);
      (Let (a "v161") L Ptoi [(t "v157")]);
      (Let (a "v162") L Ptoi [(t "v160")]);
      (Let (a "v163") W (Cmp Ult L) [(t "v161"); (t "v162")])] (JBranch (t "v163") (To (a "L152")) (To (a "L147"))));
  (mkBlock (a "L152") [] [(Flight (a "v165") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v166") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk13")]);
      (Let (a "chk16") A (Check 0 1 Read 1) [(t "v166")]);
      (Let (a "v167") W (RawLoad (LdNarrow Ub) 0) [(t "chk16")])] (JRet (t "v167")));
  (mkBlock (a "L147") [] [(Flight (a "v173") Add [(FAddress (t "v0")); (FValue (Const 96))] (LowerOf (t "v0")));
      (Let (a "chk17") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v173")]);
      (Let (a "v174") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Let (a "v175") L Ptoi [(t "v174")]);
      (Let (a "v176") L Ptoi [(Const 0)]);
      (Let (a "v177") W (Cmp Ne L) [(t "v175"); (t "v176")])] (JBranch (t "v177") (To (a "L169")) (To (a "L170"))));
  (mkBlock (a "L169") [] [(Flight (a "v183") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk18") A (Renew 0 8 Read 8) [(t "chk9"); (t "v183")]);
      (Let (a "v184") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk18")]);
      (Call (CResult (a "v185") W) (Global (a "glibc_genops#save_for_backup")) [(Arg P (t "v0")); (Arg P (t "v184"))])] (JBranch (t "v185") (To (a "L178")) (To (a "L171"))));
  (mkBlock (a "L178") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L170") [] [(Flight (a "v192") Add [(FAddress (t "v0")); (FValue (Const 80))] (LowerOf (t "v0")));
      (Let (a "chk19") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v192")]);
      (Let (a "v193") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk19")]);
      (Let (a "v194") L Ptoi [(t "v193")]);
      (Let (a "v196") W (Cmp Ne L) [(t "v194"); (t "v176")])] (JBranch (t "v196") (To (a "L188")) (To (a "L171"))));
  (mkBlock (a "L188") [] [(Call CVoid (Global (a "__GI__IO_free_backup_area")) [(Arg P (t "v0"))])] (JGoto (To (a "L171"))));
  (mkBlock (a "L171") [] [(Flight (a "v199") Add [(FAddress (t "v0")); (FValue (Const 216))] (LowerOf (t "v0")));
      (Let (a "chk20") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v199")]);
      (Let (a "v200") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk20")]);
      (Let (a "iw_1.v4") L Ptoi [(t "v200")]);
      (Let (a "iw_1.v7") P Copy [(Global (a "__io_vtables"))]);
      (Let (a "iw_1.v8") L Ptoi [(t "iw_1.v7")]);
      (Let (a "iw_1.v9") L Sub [(t "iw_1.v4"); (t "iw_1.v8")]);
      (Let (a "iw_1.v15") W (Cmp Uge L) [(t "iw_1.v9"); (Const 2352)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L10")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L10") [] [(Call CVoid (Global (a "_IO_vtable_check")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v202") Add [(FAddress (t "v200")); (FValue (Const 32))] (LowerOf (t "v200")));
      (Let (a "chk21") A (Check 0 8 Read 8) [(t "v202")]);
      (Let (a "v203") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk21")]);
      (Let (a "chk22") F CheckFunction [(t "v203")]);
      (RawCall (CResult (a "v205") W) (t "chk22") [(Arg P (t "v0"))])] (JRet (t "v205")))].
