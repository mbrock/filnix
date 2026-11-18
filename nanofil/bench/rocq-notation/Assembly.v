(** This sample spells the captured directory allocator and locale alias
    comparison using SSA notation for their instructions and jumps. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Require Import CompactSyntax AssemblySyntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

Definition hello_image_fn___alloc_dir : func :=
  mkFunc (a "__alloc_dir") (a "export") (RClass P)
    [(W, a "v0"); (W, a "v2"); (W, a "v4"); (P, a "v6")]
    [mkBlock (a "start") []
       ir[ %"v11" : W = (Ext Ub) %"v2";
           %"v12" : W = (Cmp Eq W) %"v11", #0 ]
       ir{ br %"v12" ? "L13" : "L14" };
     mkBlock (a "L13") []
       ir[ call %"v16" : W = $"__GI___fcntl64_nocancel"(W %"v0", W #2, W #1);
           %"v17" : W = (Cmp Slt W) %"v16", #0 ]
       ir{ goto "L14" };
     mkBlock (a "L14") [Phi (a "v21") W [(a "start", k 0); (a "L13", t "v17")]]
       []
       ir{ br %"v21" ? "L8" : "L10" };
     mkBlock (a "L8") []
       []
       ir{ ret #0 };
     mkBlock (a "L10") []
       ir[ %"v31" = %"v6" +p #56;
           %"chk0" : A = (Check 0 8 Read 1) %"v31";
           %"v32" : L = (RawLoad LdL 0) %"chk0";
           %"v33" : W = (Cmp Ugt L) %"v32", #32768 ]
       ir{ br %"v33" ? "L27" : "L29" };
     mkBlock (a "L27") []
       ir[ %"v35" = %"v6" +p #56;
           %"v36" : L = (RawLoad LdL 0) %"chk0" ]
       ir{ goto "L29" };
     mkBlock (a "L29") [Phi (a "v37") L [(a "L27", t "v36"); (a "L10", k 32768)]]
       ir[ %"v38" : W = (Cmp Ult L) %"v37", #1048576 ]
       ir{ br %"v38" ? "L24" : "L26" };
     mkBlock (a "L24") []
       ir[ %"v43" = %"v6" +p #56;
           %"v44" : L = (RawLoad LdL 0) %"chk0";
           %"v45" : W = (Cmp Ugt L) %"v44", #32768 ]
       ir{ br %"v45" ? "L39" : "L26" };
     mkBlock (a "L39") []
       ir[ %"v47" = %"v6" +p #56;
           %"v48" : L = (RawLoad LdL 0) %"chk0" ]
       ir{ goto "L26" };
     mkBlock (a "L26") [Phi (a "v50") L [(a "L39", t "v48"); (a "L24", k 32768); (a "L29", k 1048576)]]
       ir[ %"v53" : L = Add %"v50", #48;
           call %"v54" : P = $"malloc"(L %"v53");
           %"v59" : L = Ptoi %"v54";
           %"v60" : L = Ptoi #0;
           %"v61" : W = (Cmp Eq L) %"v59", %"v60" ]
       ir{ br %"v61" ? "L55" : "L57" };
     mkBlock (a "L55") []
       []
       ir{ br %"v11" ? "L62" : "L64" };
     mkBlock (a "L62") []
       ir[ call $"__GI___close_nocancel_nostatus"(W %"v0") ]
       ir{ goto "L64" };
     mkBlock (a "L64") []
       []
       ir{ ret #0 };
     mkBlock (a "L57") []
       ir[ %"chk4" : A = (Check 0 4 Write 1) %"v54";
           store Ww [%"chk4" + 0] <- %"v0";
           %"v71" = %"v54" +p #4;
           %"chk5" : A = (HalfCheck Upper 0 4 Write 1) %"chk4", %"v71";
           store Ww [%"chk5" + 0] <- #0;
           %"v73" = %"v54" +p #8;
           %"chk6" : A = (HalfCheck Upper 0 8 Write 1) %"chk4", %"v73";
           store Wl [%"chk6" + 0] <- %"v50";
           %"v76" = %"v54" +p #16;
           %"chk7" : A = (HalfCheck Upper 0 8 Write 1) %"chk4", %"v76";
           store Wl [%"chk7" + 0] <- #0;
           %"v78" = %"v54" +p #24;
           %"chk8" : A = (HalfCheck Upper 0 8 Write 1) %"chk4", %"v78";
           store Wl [%"chk8" + 0] <- #0;
           %"v80" = %"v54" +p #32;
           %"chk9" : A = (HalfCheck Upper 0 8 Write 1) %"chk4", %"v80";
           store Wl [%"chk9" + 0] <- #0;
           %"v82" = %"v54" +p #40;
           %"chk10" : A = (HalfCheck Upper 0 4 Write 1) %"chk4", %"v82";
           store Ww [%"chk10" + 0] <- #0 ]
       ir{ ret %"v54" }].

Definition hello_image_fn_glibc_localealias'23alias_compare : func :=
  mkFunc (a "glibc_localealias#alias_compare") (a "local") (RClass W)
    [(P, a "v0"); (P, a "v2")]
    [mkBlock (a "start") []
       ir[ %"chk0" : A = (Check 0 8 Read 8) %"v0";
           %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
           %"chk1" : A = (Check 0 8 Read 8) %"v2";
           %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
           %"v8" : P = Copy $"_nl_C_locobj";
           call %"v9" : W = $"__GI___strcasecmp_l"(P %"v5", P %"v7", P %"v8") ]
       ir{ ret %"v9" }].
