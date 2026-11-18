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

Definition hello_image_fn___GI___wunderflow : func :=
  mkFunc (a "__GI___wunderflow") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v6") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v6")]);
      (Let (a "v7") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v8") W (Cmp Slt W) [(t "v7"); (Const 0)])] (JBranch (t "v8") (To (a "L10")) (To (a "L9"))));
  (mkBlock (a "L9") [] [(Flight (a "v12") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v13") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v14") W (Cmp Eq W) [(t "v13"); (Const 0)])] (JBranch (t "v14") (To (a "L42")) (To (a "L10"))));
  (mkBlock (a "L42") [] [(Call (CResult (a "v59") W) (Global (a "_IO_fwide")) [(Arg P (t "v0")); (Arg W (Const 1))]);
      (Let (a "v61") W (Cmp Ne W) [(t "v59"); (Const 1)])] (JGoto (To (a "L10"))));
  (mkBlock (a "L10") [(Phi (a "v65") W [((a "start"), (Const 1)); ((a "L9"), (Const 0)); ((a "L42"), (t "v61"))])] [] (JBranch (t "v65") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L4") [] [(Flight (a "v71") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk2") A (Renew 0 4 Read 1) [(t "chk0"); (t "v71")]);
      (Let (a "v72") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "v73") W (Cmp Eq W) [(t "v72"); (Const 0)])] (JBranch (t "v73") (To (a "L99")) (To (a "L69"))));
  (mkBlock (a "L99") [] [(Call (CResult (a "v116") W) (Global (a "_IO_fwide")) [(Arg P (t "v0")); (Arg W (Const 1))])] (JGoto (To (a "L69"))));
  (mkBlock (a "L69") [] [(Let (a "chk3") A (HalfCheck Lower 0 4 Read 1) [(t "chk0"); (t "v0")]);
      (Let (a "v122") W (RawLoad (LdNarrow Sw) 0) [(t "chk3")]);
      (Let (a "v123") W And [(t "v122"); (Const 2048)])] (JBranch (t "v123") (To (a "L118")) (To (a "L120"))));
  (mkBlock (a "L118") [] [(Call (CResult (a "v128") W) (Global (a "__GI__IO_switch_to_wget_mode")) [(Arg P (t "v0"))]);
      (Let (a "v130") W (Cmp Eq W) [(t "v128"); (Const 4294967295)])] (JBranch (t "v130") (To (a "L124")) (To (a "L120"))));
  (mkBlock (a "L124") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L120") [] [(Flight (a "v136") Add [(FAddress (t "v0")); (FValue (Const 160))] (LowerOf (t "v0")));
      (Let (a "chk4") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v136")]);
      (Let (a "v137") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "chk5") A (Check 0 8 Read 8) [(t "v137")]);
      (Let (a "v138") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")]);
      (Let (a "v141") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Flight (a "v142") Add [(FAddress (t "v141")); (FValue (Const 8))] (LowerOf (t "v141")));
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "v142")]);
      (Let (a "v143") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")]);
      (Let (a "v144") L Ptoi [(t "v138")]);
      (Let (a "v145") L Ptoi [(t "v143")]);
      (Let (a "v146") W (Cmp Ult L) [(t "v144"); (t "v145")])] (JBranch (t "v146") (To (a "L132")) (To (a "L134"))));
  (mkBlock (a "L132") [] [(Flight (a "v148") Add [(FAddress (t "v0")); (FValue (Const 160))] (LowerOf (t "v0")));
      (Let (a "v149") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk4")]);
      (Let (a "chk9") A (Check 0 8 Read 8) [(t "v149")]);
      (Let (a "v150") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Let (a "chk10") A (Check 0 4 Read 1) [(t "v150")]);
      (Let (a "v151") W (RawLoad (LdNarrow Sw) 0) [(t "chk10")])] (JRet (t "v151")));
  (mkBlock (a "L134") [] [(Let (a "chk11") A (Renew 0 4 Read 1) [(t "chk3"); (t "v0")]);
      (Let (a "v157") W (RawLoad (LdNarrow Sw) 0) [(t "chk11")]);
      (Let (a "v158") W And [(t "v157"); (Const 256)])] (JBranch (t "v158") (To (a "L153")) (To (a "L155"))));
  (mkBlock (a "L153") [] [(Call CVoid (Global (a "__GI__IO_switch_to_main_wget_area")) [(Arg P (t "v0"))]);
      (Flight (a "v164") Add [(FAddress (t "v0")); (FValue (Const 160))] (LowerOf (t "v0")));
      (Let (a "chk12") A (Renew 0 8 Read 8) [(t "chk4"); (t "v164")]);
      (Let (a "v165") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk12")]);
      (Let (a "chk13") A (Check 0 8 Read 8) [(t "v165")]);
      (Let (a "v166") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk13")]);
      (Let (a "v169") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk12")]);
      (Flight (a "v170") Add [(FAddress (t "v169")); (FValue (Const 8))] (LowerOf (t "v169")));
      (Let (a "chk15") A (Check 0 8 Read 8) [(t "v170")]);
      (Let (a "v171") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk15")]);
      (Let (a "v172") L Ptoi [(t "v166")]);
      (Let (a "v173") L Ptoi [(t "v171")]);
      (Let (a "v174") W (Cmp Ult L) [(t "v172"); (t "v173")])] (JBranch (t "v174") (To (a "L160")) (To (a "L155"))));
  (mkBlock (a "L160") [] [(Flight (a "v176") Add [(FAddress (t "v0")); (FValue (Const 160))] (LowerOf (t "v0")));
      (Let (a "v177") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk12")]);
      (Let (a "chk17") A (Check 0 8 Read 8) [(t "v177")]);
      (Let (a "v178") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Let (a "chk18") A (Check 0 4 Read 1) [(t "v178")]);
      (Let (a "v179") W (RawLoad (LdNarrow Sw) 0) [(t "chk18")])] (JRet (t "v179")));
  (mkBlock (a "L155") [] [(Flight (a "v185") Add [(FAddress (t "v0")); (FValue (Const 96))] (LowerOf (t "v0")));
      (Let (a "chk19") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v185")]);
      (Let (a "v186") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk19")]);
      (Let (a "v187") L Ptoi [(t "v186")]);
      (Let (a "v188") L Ptoi [(Const 0)]);
      (Let (a "v189") W (Cmp Ne L) [(t "v187"); (t "v188")])] (JBranch (t "v189") (To (a "L181")) (To (a "L182"))));
  (mkBlock (a "L181") [] [(Flight (a "v195") Add [(FAddress (t "v0")); (FValue (Const 160))] (LowerOf (t "v0")));
      (Let (a "chk20") A (Renew 0 8 Read 8) [(t "chk4"); (t "v195")]);
      (Let (a "v196") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk20")]);
      (Flight (a "v197") Add [(FAddress (t "v196")); (FValue (Const 8))] (LowerOf (t "v196")));
      (Let (a "chk21") A (Check 0 8 Read 8) [(t "v197")]);
      (Let (a "v198") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk21")]);
      (Call (CResult (a "v199") W) (Global (a "glibc_wgenops#save_for_wbackup")) [(Arg P (t "v0")); (Arg P (t "v198"))])] (JBranch (t "v199") (To (a "L190")) (To (a "L183"))));
  (mkBlock (a "L190") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L182") [] [(Flight (a "v205") Add [(FAddress (t "v0")); (FValue (Const 160))] (LowerOf (t "v0")));
      (Let (a "chk22") A (Renew 0 8 Read 8) [(t "chk4"); (t "v205")]);
      (Let (a "v206") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk22")]);
      (Flight (a "v207") Add [(FAddress (t "v206")); (FValue (Const 72))] (LowerOf (t "v206")));
      (Let (a "chk23") A (Check 0 8 Read 8) [(t "v207")]);
      (Let (a "v208") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk23")]);
      (Let (a "v209") L Ptoi [(t "v208")]);
      (Let (a "v211") W (Cmp Ne L) [(t "v209"); (t "v188")])] (JBranch (t "v211") (To (a "L201")) (To (a "L183"))));
  (mkBlock (a "L201") [] [(Call CVoid (Global (a "__GI__IO_free_wbackup_area")) [(Arg P (t "v0"))])] (JGoto (To (a "L183"))));
  (mkBlock (a "L183") [] [(Flight (a "v214") Add [(FAddress (t "v0")); (FValue (Const 216))] (LowerOf (t "v0")));
      (Let (a "chk24") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v214")]);
      (Let (a "v215") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk24")]);
      (Let (a "iw_1.v4") L Ptoi [(t "v215")]);
      (Let (a "iw_1.v7") P Copy [(Global (a "__io_vtables"))]);
      (Let (a "iw_1.v8") L Ptoi [(t "iw_1.v7")]);
      (Let (a "iw_1.v9") L Sub [(t "iw_1.v4"); (t "iw_1.v8")]);
      (Let (a "iw_1.v15") W (Cmp Uge L) [(t "iw_1.v9"); (Const 2352)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L10")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L10") [] [(Call CVoid (Global (a "_IO_vtable_check")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v217") Add [(FAddress (t "v215")); (FValue (Const 32))] (LowerOf (t "v215")));
      (Let (a "chk25") A (Check 0 8 Read 8) [(t "v217")]);
      (Let (a "v218") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk25")]);
      (Let (a "chk26") F CheckFunction [(t "v218")]);
      (RawCall (CResult (a "v220") W) (t "chk26") [(Arg P (t "v0"))])] (JRet (t "v220")))].
