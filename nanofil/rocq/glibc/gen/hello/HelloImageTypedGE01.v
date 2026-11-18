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

Definition hello_image_fn_quotearg'23gettext_quote : func :=
  mkFunc (a "quotearg#gettext_quote") (a "local") (RClass P) [(P, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "v17") P (Alloc 4) [(Const 4)]);
      (Let (a "v18") P (Alloc 4) [(Const 8)]);
      (Let (a "v5") P Copy [(Global (a "quotearg#str.82"))]);
      (Call CVoid (Global (a "mbszero")) [(Arg P (t "v18"))]);
      (Let (a "v22") P Copy [(Global (a "quotearg#gettext_quote.quote.83"))]);
      (Call (CResult (a "v24") L) (Global (a "rpl_mbrtoc32")) [(Arg P (t "v17")); (Arg P (t "v22")); (Arg L (Const 3)); (Arg P (t "v18"))]);
      (Let (a "v25") W (Cmp Eq L) [(t "v24"); (Const 3)])] (JBranch (t "v25") (To (a "L26")) (To (a "L27"))));
  (mkBlock (a "L26") [] [(Let (a "chk0") A (Check 0 4 Read 1) [(t "v17")]);
      (Let (a "v28") W (RawLoad (LdNarrow Uw) 0) [(t "chk0")]);
      (Let (a "v29") W (Cmp Eq W) [(t "v28"); (Const 8216)])] (JGoto (To (a "L27"))));
  (mkBlock (a "L27") [(Phi (a "v31") W [((a "start"), (Const 0)); ((a "L26"), (t "v29"))])] [] (JBranch (t "v31") (To (a "L19")) (To (a "L21"))));
  (mkBlock (a "L19") [] [(Let (a "v32") P Copy [(Global (a "quotearg#gettext_quote.quote.83"))]);
      (Let (a "chk1") A (Check 0 1 Read 1) [(t "v0")]);
      (Let (a "v35") W (RawLoad (LdNarrow Sb) 0) [(t "chk1")]);
      (Let (a "v36") W (Cmp Eq W) [(t "v35"); (Const 39)]);
      (Let (a "v37") L (Ext Sw) [(t "v36")]);
      (Let (a "v38") L Shl [(t "v37"); (Const 2)]);
      (Flight (a "v39") Add [(FAddress (t "v32")); (FValue (t "v38"))] (LowerOf (t "v32")))] (JRet (t "v39")));
  (mkBlock (a "L21") [] [(Let (a "v45") W (Cmp Eq W) [(t "v2"); (Const 9)])] (JBranch (t "v45") (To (a "L41")) (To (a "L42"))));
  (mkBlock (a "L41") [] [(Let (a "v46") P Copy [(Global (a "quotearg#str.84"))])] (JGoto (To (a "L43"))));
  (mkBlock (a "L42") [] [(Let (a "v47") P Copy [(Global (a "quotearg#str.85"))])] (JGoto (To (a "L43"))));
  (mkBlock (a "L43") [(Phi (a "v48") P [((a "L41"), (t "v46")); ((a "L42"), (t "v47"))])] [] (JRet (t "v48")))].

Definition hello_image_fn___GI___getdents64 : func :=
  mkFunc (a "__GI___getdents64") (a "export") (RClass L) [(W, (a "v0")); (P, (a "v2")); (L, (a "v4"))] [(mkBlock (a "start") [] [(Call (CResult (a "v9") W) (Global (a "zsys_getdents")) [(Arg W (t "v0")); (Arg P (t "v2")); (Arg L (t "v4"))]);
      (Let (a "v10") L (Ext Sw) [(t "v9")])] (JRet (t "v10")))].

Definition hello_image_fn_glibc_dcigettext'23get_output_charset : func :=
  mkFunc (a "glibc_dcigettext#get_output_charset") (a "local") (RClass P) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v6") L Ptoi [(t "v0")]);
      (Let (a "v7") L Ptoi [(Const 0)]);
      (Let (a "v8") W (Cmp Ne L) [(t "v6"); (t "v7")])] (JBranch (t "v8") (To (a "L9")) (To (a "L10"))));
  (mkBlock (a "L9") [] [(Flight (a "v12") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v12")]);
      (Let (a "v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v14") L Ptoi [(t "v13")]);
      (Let (a "v16") W (Cmp Ne L) [(t "v14"); (t "v7")])] (JGoto (To (a "L10"))));
  (mkBlock (a "L10") [(Phi (a "v18") W [((a "start"), (Const 0)); ((a "L9"), (t "v16"))])] [] (JBranch (t "v18") (To (a "L2")) (To (a "L3"))));
  (mkBlock (a "L2") [] [(Flight (a "v20") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v20")]);
      (Let (a "v21") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")])] (JRet (t "v21")));
  (mkBlock (a "L3") [] [(Let (a "v26") P Copy [(Global (a "glibc_dcigettext#get_output_charset.output_charset_cached.287"))]);
      (Let (a "chk2") A (Check 0 4 Read 1) [(t "v26")]);
      (Let (a "v27") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "v28") W (Cmp Eq W) [(t "v27"); (Const 0)])] (JBranch (t "v28") (To (a "L23")) (To (a "L25"))));
  (mkBlock (a "L23") [] [(Let (a "v30") P Copy [(Global (a "glibc_dcigettext#str.288"))]);
      (Call (CResult (a "v31") P) (Global (a "__GI_getenv")) [(Arg P (t "v30"))]);
      (Let (a "v36") L Ptoi [(t "v31")]);
      (Let (a "v38") W (Cmp Ne L) [(t "v36"); (t "v7")])] (JBranch (t "v38") (To (a "L39")) (To (a "L40"))));
  (mkBlock (a "L39") [] [(Let (a "chk3") A (Check 0 1 Read 1) [(t "v31")]);
      (Let (a "v43") W (RawLoad (LdNarrow Sb) 0) [(t "chk3")]);
      (Let (a "v44") W (Cmp Ne W) [(t "v43"); (Const 0)])] (JGoto (To (a "L40"))));
  (mkBlock (a "L40") [(Phi (a "v46") W [((a "L23"), (Const 0)); ((a "L39"), (t "v44"))])] [] (JBranch (t "v46") (To (a "L32")) (To (a "L34"))));
  (mkBlock (a "L32") [] [(Call (CResult (a "v49") L) (Global (a "__GI_strlen")) [(Arg P (t "v31"))]);
      (Let (a "v50") L Add [(t "v49"); (Const 1)]);
      (Call (CResult (a "v53") P) (Global (a "malloc")) [(Arg L (t "v50"))]);
      (Let (a "v58") L Ptoi [(t "v53")]);
      (Let (a "v60") W (Cmp Ne L) [(t "v58"); (t "v7")])] (JBranch (t "v60") (To (a "L54")) (To (a "L56"))));
  (mkBlock (a "L54") [] [(Call (CResult (a "v64") P) (Global (a "__GI_memcpy")) [(Arg P (t "v53")); (Arg P (t "v31")); (Arg L (t "v50"))])] (JGoto (To (a "L56"))));
  (mkBlock (a "L56") [] [(Let (a "v65") P Copy [(Global (a "glibc_dcigettext#get_output_charset.output_charset_cache.286"))]);
      (Let (a "chk4") A (Check 0 8 Write 8) [(t "v65")]);
      (RawStorePointer 0 (t "v53") (t "chk4") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L34"))));
  (mkBlock (a "L34") [] [(Let (a "v67") P Copy [(Global (a "glibc_dcigettext#get_output_charset.output_charset_cached.287"))]);
      (Let (a "chk5") A (Check 0 4 Write 1) [(t "v67")]);
      (RawStore Ww 0 (Const 1) (t "chk5"))] (JGoto (To (a "L25"))));
  (mkBlock (a "L25") [] [(Let (a "v71") P Copy [(Global (a "glibc_dcigettext#get_output_charset.output_charset_cache.286"))]);
      (Let (a "chk6") A (Check 0 8 Read 8) [(t "v71")]);
      (Let (a "v72") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "v73") L Ptoi [(t "v72")]);
      (Let (a "v75") W (Cmp Ne L) [(t "v73"); (t "v7")])] (JBranch (t "v75") (To (a "L68")) (To (a "L69"))));
  (mkBlock (a "L68") [] [(Let (a "v76") P Copy [(Global (a "glibc_dcigettext#get_output_charset.output_charset_cache.286"))]);
      (Let (a "chk7") A (Check 0 8 Read 8) [(t "v76")]);
      (Let (a "v77") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk7")])] (JRet (t "v77")));
  (mkBlock (a "L69") [] [(Let (a "v79") P Copy [(Global (a "__libc_tsd_LOCALE"))]);
      (Let (a "chk8") A (Check 0 8 Read 8) [(t "v79")]);
      (Let (a "v80") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk9") A (Check 0 8 Read 8) [(t "v80")]);
      (Let (a "v82") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Flight (a "v83") Add [(FAddress (t "v82")); (FValue (Const 56))] (LowerOf (t "v82")));
      (Flight (a "v87") Add [(FAddress (t "v83")); (FValue (Const 112))] (LowerOf (t "v83")));
      (Let (a "chk10") A (Check 0 8 Read 8) [(t "v87")]);
      (Let (a "v88") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk10")])] (JRet (t "v88")))].
