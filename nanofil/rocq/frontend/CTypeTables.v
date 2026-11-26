(** Pure builtin signature, atomic, vector intrinsic, library prototype, and
    x86-64 CPU target tables for the Gallina C type checker and lowerer.

    Keeping these static lookup tables separate from CTypeAst.v and CTypes.v
    keeps each Rocq module fast to compile and easy to inspect against
    nanofil/src/c_types.pl. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Frontend Require Import CAst CAttrs CLex CPp CTypeAst.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ## Compound assignment and floating-point builtins *)

Definition compound_assign_binop (op : string) : option c_binop :=
  if String.eqb op "+=" then Some BAdd
  else if String.eqb op "-=" then Some BSub
  else if String.eqb op "*=" then Some BMul
  else if String.eqb op "/=" then Some BDiv
  else if String.eqb op "%=" then Some BMod
  else if String.eqb op "&=" then Some BAnd
  else if String.eqb op "|=" then Some BOr
  else if String.eqb op "^=" then Some BXor
  else if String.eqb op "<<=" then Some BShl
  else if String.eqb op ">>=" then Some BShr
  else None.

Definition nan_builtin (name : string) : option (c_type * Z) :=
  if String.eqb name "__builtin_nan" then Some (TDouble, 9221120237041090560)
  else if String.eqb name "__builtin_nanf" then Some (TFloat, 2143289344)
  else if String.eqb name "__builtin_nanl" then Some (TLDouble, 604458298121296159965184)
  else None.

Definition float_builtin (name : string) : option (c_type * Z) :=
  if String.eqb name "__builtin_huge_val" || String.eqb name "__builtin_inf" then
    Some (TDouble, 9218868437227405312)
  else if String.eqb name "__builtin_huge_valf" || String.eqb name "__builtin_inff" then
    Some (TFloat, 2139095040)
  else if String.eqb name "__builtin_huge_vall" || String.eqb name "__builtin_infl" then
    Some (TLDouble, 604453686435277732577280)
  else nan_builtin name.

Definition classify_builtin_names : list string :=
  [ "__builtin_isinf"; "__builtin_isinf_sign";
    "__builtin_isfinite"; "__builtin_isnormal";
    "__builtin_signbit"; "__builtin_signbitl";
    "__builtin_signbitf"; "__builtin_fpclassify" ].

Definition classify_builtin (name : string) : bool :=
  str_in name classify_builtin_names.

Definition libm_builtin (name : string) : option string :=
  if String.eqb name "__builtin_ceil" then Some "ceil"
  else if String.eqb name "__builtin_floor" then Some "floor"
  else None.

Definition root_builtin (name : string) : option (string * c_type) :=
  if String.eqb name "__builtin_sqrt" then Some ("sqrt", TDouble)
  else if String.eqb name "__builtin_sqrtf" then Some ("sqrtf", TFloat)
  else if String.eqb name "__builtin_sqrtl" then Some ("sqrtl", TLDouble)
  else None.

Definition trunc_builtin (name : string) : option c_type :=
  if String.eqb name "__builtin_trunc" then Some TDouble
  else if String.eqb name "__builtin_truncf" then Some TFloat
  else None.

Definition sign_builtin (name : string) : option (string * c_type) :=
  if String.eqb name "__builtin_fabs" then Some ("abs", TDouble)
  else if String.eqb name "__builtin_fabsf" then Some ("abs", TFloat)
  else if String.eqb name "__builtin_fabsl" then Some ("abs", TLDouble)
  else if String.eqb name "__builtin_copysign" then Some ("copysign", TDouble)
  else if String.eqb name "__builtin_copysignf" then Some ("copysign", TFloat)
  else if String.eqb name "__builtin_copysignl" then Some ("copysign", TLDouble)
  else None.

(** ## Bit, rotation, and overflow builtins *)

Definition rotate_builtin (name : string) : option (string * c_type) :=
  if String.eqb name "__builtin_rotateleft8" then Some ("left", TUChar)
  else if String.eqb name "__builtin_rotateleft16" then Some ("left", TUShort)
  else if String.eqb name "__builtin_rotateleft32" then Some ("left", TUInt)
  else if String.eqb name "__builtin_rotateleft64" then Some ("left", TULong)
  else if String.eqb name "__builtin_rotateright8" then Some ("right", TUChar)
  else if String.eqb name "__builtin_rotateright16" then Some ("right", TUShort)
  else if String.eqb name "__builtin_rotateright32" then Some ("right", TUInt)
  else if String.eqb name "__builtin_rotateright64" then Some ("right", TULong)
  else None.

Definition bit_builtin (name : string) : option (string * c_type) :=
  if String.eqb name "__builtin_ctz" then Some ("ctz", TUInt)
  else if String.eqb name "__builtin_ctzl" then Some ("ctz", TULong)
  else if String.eqb name "__builtin_ctzll" then Some ("ctz", TULLong)
  else if String.eqb name "__builtin_clz" then Some ("clz", TUInt)
  else if String.eqb name "__builtin_clzl" then Some ("clz", TULong)
  else if String.eqb name "__builtin_clzll" then Some ("clz", TULLong)
  else if String.eqb name "__builtin_popcount" then Some ("popcount", TUInt)
  else if String.eqb name "__builtin_popcountl" then Some ("popcount", TULong)
  else if String.eqb name "__builtin_popcountll" then Some ("popcount", TULLong)
  else if String.eqb name "__builtin_ffs" then Some ("ffs", TUInt)
  else if String.eqb name "__builtin_ffsl" then Some ("ffs", TULong)
  else if String.eqb name "__builtin_ffsll" then Some ("ffs", TULLong)
  else None.

Definition overflow_builtin (name : string) : option (string * option c_type) :=
  if String.eqb name "__builtin_add_overflow" then Some ("add", None)
  else if String.eqb name "__builtin_sub_overflow" then Some ("sub", None)
  else if String.eqb name "__builtin_mul_overflow" then Some ("mul", None)
  else if String.eqb name "__builtin_sadd_overflow" then Some ("add", Some TInt)
  else if String.eqb name "__builtin_uadd_overflow" then Some ("add", Some TUInt)
  else if String.eqb name "__builtin_saddl_overflow" then Some ("add", Some TLong)
  else if String.eqb name "__builtin_uaddl_overflow" then Some ("add", Some TULong)
  else if String.eqb name "__builtin_saddll_overflow" then Some ("add", Some TLLong)
  else if String.eqb name "__builtin_uaddll_overflow" then Some ("add", Some TULLong)
  else if String.eqb name "__builtin_ssub_overflow" then Some ("sub", Some TInt)
  else if String.eqb name "__builtin_usub_overflow" then Some ("sub", Some TUInt)
  else if String.eqb name "__builtin_ssubl_overflow" then Some ("sub", Some TLong)
  else if String.eqb name "__builtin_usubl_overflow" then Some ("sub", Some TULong)
  else if String.eqb name "__builtin_ssubll_overflow" then Some ("sub", Some TLLong)
  else if String.eqb name "__builtin_usubll_overflow" then Some ("sub", Some TULLong)
  else if String.eqb name "__builtin_smul_overflow" then Some ("mul", Some TInt)
  else if String.eqb name "__builtin_umul_overflow" then Some ("mul", Some TUInt)
  else if String.eqb name "__builtin_smull_overflow" then Some ("mul", Some TLong)
  else if String.eqb name "__builtin_umull_overflow" then Some ("mul", Some TULong)
  else if String.eqb name "__builtin_smulll_overflow" then Some ("mul", Some TLLong)
  else if String.eqb name "__builtin_umulll_overflow" then Some ("mul", Some TULLong)
  else None.

(** ## SSE and AVX2 vector intrinsic tables *)

Definition generic_vector_builtin (name : string) : bool :=
  str_in name
    [ "__builtin_shufflevector"; "__builtin_convertvector";
      "__builtin_nondeterministic_value";
      "__builtin_elementwise_add_sat"; "__builtin_elementwise_sub_sat";
      "__builtin_elementwise_min"; "__builtin_elementwise_max";
      "__builtin_elementwise_abs" ].

Definition ty_v16qi : c_type := TVec TChar 16 16.
Definition ty_v8hi : c_type := TVec TShort 8 16.
Definition ty_v4si : c_type := TVec TInt 4 16.
Definition ty_v2di : c_type := TVec TLLong 2 16.
Definition ty_v4sf : c_type := TVec TFloat 4 16.
Definition ty_v2df : c_type := TVec TDouble 2 16.
Definition ty_v32qi : c_type := TVec TChar 32 32.
Definition ty_v16hi : c_type := TVec TShort 16 32.
Definition ty_v8si : c_type := TVec TInt 8 32.
Definition ty_v4di : c_type := TVec TLLong 4 32.
Definition ty_v8sf : c_type := TVec TFloat 8 32.
Definition ty_v4df : c_type := TVec TDouble 4 32.

Definition wide_vec_type (t : c_type) : c_type :=
  if c_type_eqb t ty_v16qi then ty_v32qi
  else if c_type_eqb t ty_v8hi then ty_v16hi
  else if c_type_eqb t ty_v4si then ty_v8si
  else if c_type_eqb t ty_v2di then ty_v4di
  else if c_type_eqb t ty_v4sf then ty_v8sf
  else if c_type_eqb t ty_v2df then ty_v4df
  else t.

Definition lane_builtin_pairs : list (string * string) :=
  [ ("packsswb256", "packsswb128");
    ("packuswb256", "packuswb128");
    ("packssdw256", "packssdw128");
    ("packusdw256", "packusdw128");
    ("pavgb256", "pavgb128");
    ("pavgw256", "pavgw128");
    ("pblendvb256", "pblendvb128");
    ("pblendw256", "pblendw128");
    ("pmaddwd256", "pmaddwd128");
    ("pmaddubsw256", "pmaddubsw128");
    ("pmuldq256", "pmuldq128");
    ("pmuludq256", "pmuludq128");
    ("pmulhw256", "pmulhw128");
    ("pmulhuw256", "pmulhuw128");
    ("psadbw256", "psadbw128");
    ("pshufb256", "pshufb128");
    ("psignb256", "psignb128");
    ("psignw256", "psignw128");
    ("psignd256", "psignd128");
    ("phaddw256", "phaddw128");
    ("phaddd256", "phaddd128");
    ("phaddsw256", "phaddsw128");
    ("phsubw256", "phsubw128");
    ("phsubd256", "phsubd128");
    ("phsubsw256", "phsubsw128");
    ("psllwi256", "psllwi128");
    ("pslldi256", "pslldi128");
    ("psllqi256", "psllqi128");
    ("psrlwi256", "psrlwi128");
    ("psrldi256", "psrldi128");
    ("psrlqi256", "psrlqi128");
    ("psrawi256", "psrawi128");
    ("psradi256", "psradi128");
    ("psllw256", "psllw128");
    ("pslld256", "pslld128");
    ("psllq256", "psllq128");
    ("psrlw256", "psrlw128");
    ("psrld256", "psrld128");
    ("psrlq256", "psrlq128");
    ("psraw256", "psraw128");
    ("psrad256", "psrad128");
    ("pslldqi256_byteshift", "pslldqi128_byteshift");
    ("psrldqi256_byteshift", "psrldqi128_byteshift");
    ("palignr256", "palignr128");
    ("pclmulqdq256", "pclmulqdq128");
    ("shufps256", "shufps");
    ("addsubps256", "addsubps");
    ("addsubpd256", "addsubpd");
    ("vfmaddps256", "vfmaddps");
    ("vfmaddpd256", "vfmaddpd");
    ("vfmaddsubps256", "vfmaddsubps");
    ("vfmaddsubpd256", "vfmaddsubpd");
    ("vpermilps256", "vpermilps");
    ("pshufd256", "pshufd");
    ("pshuflw256", "pshuflw");
    ("pshufhw256", "pshufhw") ].

Definition lane_builtin (n256 : string) : option string :=
  assoc_str n256 lane_builtin_pairs.

Definition shift_count_builtin (name : string) : bool :=
  str_in name
    [ "psllw128"; "pslld128"; "psllq128";
      "psrlw128"; "psrld128"; "psrlq128";
      "psraw128"; "psrad128" ].

Definition vector_builtin_base_table : list (string * (list c_type * c_type)) :=
  [ ("pmovmskb128", ([ty_v16qi], TInt));
    ("pmovmskb256", ([ty_v32qi], TInt));
    ("addsubps", ([ty_v4sf; ty_v4sf], ty_v4sf));
    ("addsubpd", ([ty_v2df; ty_v2df], ty_v2df));
    ("vfmaddps", ([ty_v4sf; ty_v4sf; ty_v4sf], ty_v4sf));
    ("vfmaddsubps", ([ty_v4sf; ty_v4sf; ty_v4sf], ty_v4sf));
    ("vfmaddpd", ([ty_v2df; ty_v2df; ty_v2df], ty_v2df));
    ("vfmaddsubpd", ([ty_v2df; ty_v2df; ty_v2df], ty_v2df));
    ("vpermilps", ([ty_v4sf; TInt], ty_v4sf));
    ("vpermilpd", ([ty_v2df; TInt], ty_v2df));
    ("vpermilpd256", ([ty_v4df; TInt], ty_v4df));
    ("shufpd256", ([ty_v4df; ty_v4df; TInt], ty_v4df));
    ("movmskps256", ([ty_v8sf], TInt));
    ("movmskpd256", ([ty_v4df], TInt));
    ("extract128i256", ([ty_v4di; TInt], ty_v2di));
    ("vextractf128_si256", ([ty_v8si; TInt], ty_v4si));
    ("vextractf128_ps256", ([ty_v8sf; TInt], ty_v4sf));
    ("vextractf128_pd256", ([ty_v4df; TInt], ty_v2df));
    ("insert128i256", ([ty_v4di; ty_v2di; TInt], ty_v4di));
    ("vinsertf128_si256", ([ty_v8si; ty_v4si; TInt], ty_v8si));
    ("vinsertf128_ps256", ([ty_v8sf; ty_v4sf; TInt], ty_v8sf));
    ("vinsertf128_pd256", ([ty_v4df; ty_v2df; TInt], ty_v4df));
    ("permti256", ([ty_v4di; ty_v4di; TInt], ty_v4di));
    ("vperm2f128_si256", ([ty_v8si; ty_v8si; TInt], ty_v8si));
    ("vperm2f128_ps256", ([ty_v8sf; ty_v8sf; TInt], ty_v8sf));
    ("vperm2f128_pd256", ([ty_v4df; ty_v4df; TInt], ty_v4df));
    ("permvarsi256", ([ty_v8si; ty_v8si], ty_v8si));
    ("permvarsf256", ([ty_v8sf; ty_v8si], ty_v8sf));
    ("vec_ext_v32qi", ([ty_v32qi; TInt], TChar));
    ("vec_ext_v16hi", ([ty_v16hi; TInt], TShort));
    ("vec_ext_v8si", ([ty_v8si; TInt], TInt));
    ("vec_ext_v4di", ([ty_v4di; TInt], TLLong));
    ("vzeroupper", ([], TVoid));
    ("vzeroall", ([], TVoid));
    ("lddqu", ([TPtr (TQual [QConst] TChar)], ty_v16qi));
    ("movmskps", ([ty_v4sf], TInt));
    ("movmskpd", ([ty_v2df], TInt));
    ("psllwi128", ([ty_v8hi; TInt], ty_v8hi));
    ("psrlwi128", ([ty_v8hi; TInt], ty_v8hi));
    ("psrawi128", ([ty_v8hi; TInt], ty_v8hi));
    ("pslldi128", ([ty_v4si; TInt], ty_v4si));
    ("psrldi128", ([ty_v4si; TInt], ty_v4si));
    ("psradi128", ([ty_v4si; TInt], ty_v4si));
    ("psllqi128", ([ty_v2di; TInt], ty_v2di));
    ("psrlqi128", ([ty_v2di; TInt], ty_v2di));
    ("pslldqi128_byteshift", ([ty_v2di; TInt], ty_v2di));
    ("psrldqi128_byteshift", ([ty_v2di; TInt], ty_v2di));
    ("psllw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("psrlw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("psraw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("pmulhuw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("pmulhw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("pavgw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("psignw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("phaddw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("phsubw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("phaddsw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("phsubsw128", ([ty_v8hi; ty_v8hi], ty_v8hi));
    ("pslld128", ([ty_v4si; ty_v4si], ty_v4si));
    ("psrld128", ([ty_v4si; ty_v4si], ty_v4si));
    ("psrad128", ([ty_v4si; ty_v4si], ty_v4si));
    ("psignd128", ([ty_v4si; ty_v4si], ty_v4si));
    ("phaddd128", ([ty_v4si; ty_v4si], ty_v4si));
    ("phsubd128", ([ty_v4si; ty_v4si], ty_v4si));
    ("psllq128", ([ty_v2di; ty_v2di], ty_v2di));
    ("psrlq128", ([ty_v2di; ty_v2di], ty_v2di));
    ("pshufb128", ([ty_v16qi; ty_v16qi], ty_v16qi));
    ("pavgb128", ([ty_v16qi; ty_v16qi], ty_v16qi));
    ("psignb128", ([ty_v16qi; ty_v16qi], ty_v16qi));
    ("packsswb128", ([ty_v8hi; ty_v8hi], ty_v16qi));
    ("packuswb128", ([ty_v8hi; ty_v8hi], ty_v16qi));
    ("packssdw128", ([ty_v4si; ty_v4si], ty_v8hi));
    ("packusdw128", ([ty_v4si; ty_v4si], ty_v8hi));
    ("pshufd", ([ty_v4si; TInt], ty_v4si));
    ("pshuflw", ([ty_v8hi; TInt], ty_v8hi));
    ("pshufhw", ([ty_v8hi; TInt], ty_v8hi));
    ("palignr128", ([ty_v16qi; ty_v16qi; TInt], ty_v16qi));
    ("pblendvb128", ([ty_v16qi; ty_v16qi; ty_v16qi], ty_v16qi));
    ("pblendw128", ([ty_v8hi; ty_v8hi; TInt], ty_v8hi));
    ("pmuludq128", ([ty_v4si; ty_v4si], ty_v2di));
    ("pmuldq128", ([ty_v4si; ty_v4si], ty_v2di));
    ("pclmulqdq128", ([ty_v2di; ty_v2di; TChar], ty_v2di));
    ("shufpd", ([ty_v2df; ty_v2df; TInt], ty_v2df));
    ("shufps", ([ty_v4sf; ty_v4sf; TInt], ty_v4sf));
    ("pcmpistrm128", ([ty_v16qi; ty_v16qi; TChar], ty_v16qi));
    ("pcmpistri128", ([ty_v16qi; ty_v16qi; TChar], TInt));
    ("pcmpistria128", ([ty_v16qi; ty_v16qi; TChar], TInt));
    ("pcmpistric128", ([ty_v16qi; ty_v16qi; TChar], TInt));
    ("pcmpistrio128", ([ty_v16qi; ty_v16qi; TChar], TInt));
    ("pcmpistris128", ([ty_v16qi; ty_v16qi; TChar], TInt));
    ("pcmpistriz128", ([ty_v16qi; ty_v16qi; TChar], TInt));
    ("pcmpestrm128", ([ty_v16qi; TInt; ty_v16qi; TInt; TChar], ty_v16qi));
    ("pcmpestri128", ([ty_v16qi; TInt; ty_v16qi; TInt; TChar], TInt));
    ("pcmpestria128", ([ty_v16qi; TInt; ty_v16qi; TInt; TChar], TInt));
    ("pcmpestric128", ([ty_v16qi; TInt; ty_v16qi; TInt; TChar], TInt));
    ("pcmpestrio128", ([ty_v16qi; TInt; ty_v16qi; TInt; TChar], TInt));
    ("pcmpestris128", ([ty_v16qi; TInt; ty_v16qi; TInt; TChar], TInt));
    ("pcmpestriz128", ([ty_v16qi; TInt; ty_v16qi; TInt; TChar], TInt));
    ("pmaddwd128", ([ty_v8hi; ty_v8hi], ty_v4si));
    ("pmaddubsw128", ([ty_v16qi; ty_v16qi], ty_v8hi));
    ("psadbw128", ([ty_v16qi; ty_v16qi], ty_v2di));
    ("ptestz128", ([ty_v2di; ty_v2di], TInt));
    ("ptestc128", ([ty_v2di; ty_v2di], TInt));
    ("ptestnzc128", ([ty_v2di; ty_v2di], TInt));
    ("vec_ext_v16qi", ([ty_v16qi; TInt], TChar));
    ("vec_ext_v8hi", ([ty_v8hi; TInt], TShort));
    ("vec_ext_v4si", ([ty_v4si; TInt], TInt));
    ("vec_ext_v2di", ([ty_v2di; TInt], TLLong));
    ("vec_ext_v4sf", ([ty_v4sf; TInt], TFloat));
    ("vec_set_v16qi", ([ty_v16qi; TChar; TInt], ty_v16qi));
    ("vec_set_v8hi", ([ty_v8hi; TShort; TInt], ty_v8hi));
    ("vec_set_v4si", ([ty_v4si; TInt; TInt], ty_v4si));
    ("vec_set_v2di", ([ty_v2di; TLLong; TInt], ty_v2di));
    ("undef128", ([], ty_v2df));
    ("cvtss2si", ([ty_v4sf], TInt));
    ("cvtss2si64", ([ty_v4sf], TLLong));
    ("cvtsd2si", ([ty_v2df], TInt));
    ("cvtsd2si64", ([ty_v2df], TLLong));
    ("cvtpd2ps", ([ty_v2df], ty_v4sf)) ].

Definition vector_builtin (name : string) : option (list c_type * c_type) :=
  if starts_with "__builtin_ia32_" name then
    let short := String.substring 15 (String.length name - 15) name in
    match assoc_str short vector_builtin_base_table with
    | Some res => Some res
    | None =>
        match lane_builtin short with
        | Some n128 =>
            match assoc_str n128 vector_builtin_base_table with
            | Some (ps0, r0) =>
                let ps :=
                  if shift_count_builtin n128 then
                    match ps0 with [p0; c] => [wide_vec_type p0; c] | _ => map wide_vec_type ps0 end
                  else map wide_vec_type ps0 in
                Some (ps, wide_vec_type r0)
            | None => None
            end
        | None => None
        end
    end
  else None.

Definition builtin_type (name : string) : option c_type :=
  if String.eqb name "__builtin_va_start" ||
     String.eqb name "__builtin_va_copy" ||
     String.eqb name "__builtin_va_end" ||
     String.eqb name "__builtin_unreachable" ||
     String.eqb name "__builtin_cpu_init" ||
     String.eqb name "__builtin_trap" then Some TVoid
  else if String.eqb name "__builtin_alloca" ||
          String.eqb name "__builtin_frame_address" ||
          String.eqb name "__builtin_assume_aligned" then Some (TPtr TVoid)
  else if String.eqb name "__builtin_expect" then Some TLong
  else if String.eqb name "__builtin_constant_p" ||
          String.eqb name "__builtin_cpu_supports" ||
          String.eqb name "__builtin_cpu_is" ||
          String.eqb name "__builtin_isnan" ||
          String.eqb name "__builtin_flt_rounds" then Some TInt
  else if String.eqb name "__builtin_bswap16" then Some TUShort
  else if String.eqb name "__builtin_bswap32" then Some TUInt
  else if String.eqb name "__builtin_bswap64" ||
          String.eqb name "__builtin_object_size" ||
          String.eqb name "__builtin_dynamic_object_size" then Some TULong
  else if String.eqb name "__builtin_ia32_rdtsc" then Some TULLong
  else if classify_builtin name then Some TInt
  else
    match overflow_builtin name with
    | Some _ => Some TBool
    | None =>
        match bit_builtin name with
        | Some _ => Some TInt
        | None =>
            match rotate_builtin name with
            | Some (_, t) => Some t
            | None =>
                match libm_builtin name with
                | Some _ => Some TDouble
                | None =>
                    match sign_builtin name with
                    | Some (_, t) => Some t
                    | None =>
                        match root_builtin name with
                        | Some (_, t) => Some t
                        | None =>
                            match trunc_builtin name with
                            | Some t => Some t
                            | None =>
                                match vector_builtin name with
                                | Some (_, t) => Some t
                                | None => None
                                end
                            end
                        end
                    end
                end
            end
        end
    end.

(** ## Atomic, fortified, hint, library, and CPU identification tables *)

Definition ends_with (suf s : string) : bool :=
  let nl := String.length suf in
  let sl := String.length s in
  if (sl <? nl)%nat then false
  else String.eqb (String.substring (sl - nl) nl s) suf.

Definition checking_builtin (name : string) : option (string * string) :=
  if starts_with "__builtin___" name && ends_with "_chk" name then
    let n := String.length name in
    if (16 <=? n)%nat then
      let rest := String.substring 12 (n - 12) name in
      let plain := String.substring 12 (n - 16) name in
      Some ("__" ++ rest, plain)
    else None
  else None.

Definition rmw_builtin_table : list (string * (string * string * string)) :=
  [ ("__c11_atomic_exchange", ("c11", "xchg", "old"));
    ("__c11_atomic_fetch_add", ("c11", "add", "old"));
    ("__c11_atomic_fetch_sub", ("c11", "sub", "old"));
    ("__c11_atomic_fetch_and", ("c11", "and", "old"));
    ("__c11_atomic_fetch_or", ("c11", "or", "old"));
    ("__c11_atomic_fetch_xor", ("c11", "xor", "old"));
    ("__c11_atomic_fetch_nand", ("c11", "nand", "old"));
    ("__c11_atomic_fetch_max", ("c11", "max", "old"));
    ("__c11_atomic_fetch_min", ("c11", "min", "old"));
    ("__atomic_exchange_n", ("gnu", "xchg", "old"));
    ("__atomic_fetch_add", ("gnu", "add", "old"));
    ("__atomic_fetch_sub", ("gnu", "sub", "old"));
    ("__atomic_fetch_and", ("gnu", "and", "old"));
    ("__atomic_fetch_or", ("gnu", "or", "old"));
    ("__atomic_fetch_xor", ("gnu", "xor", "old"));
    ("__atomic_fetch_nand", ("gnu", "nand", "old"));
    ("__atomic_fetch_max", ("gnu", "max", "old"));
    ("__atomic_fetch_min", ("gnu", "min", "old"));
    ("__atomic_add_fetch", ("gnu", "add", "new"));
    ("__atomic_sub_fetch", ("gnu", "sub", "new"));
    ("__atomic_and_fetch", ("gnu", "and", "new"));
    ("__atomic_or_fetch", ("gnu", "or", "new"));
    ("__atomic_xor_fetch", ("gnu", "xor", "new"));
    ("__atomic_nand_fetch", ("gnu", "nand", "new"));
    ("__atomic_max_fetch", ("gnu", "max", "new"));
    ("__atomic_min_fetch", ("gnu", "min", "new"));
    ("__sync_lock_test_and_set", ("sync", "xchg", "old"));
    ("__sync_fetch_and_add", ("sync", "add", "old"));
    ("__sync_fetch_and_sub", ("sync", "sub", "old"));
    ("__sync_fetch_and_and", ("sync", "and", "old"));
    ("__sync_fetch_and_or", ("sync", "or", "old"));
    ("__sync_fetch_and_xor", ("sync", "xor", "old"));
    ("__sync_fetch_and_nand", ("sync", "nand", "old"));
    ("__sync_add_and_fetch", ("sync", "add", "new"));
    ("__sync_sub_and_fetch", ("sync", "sub", "new"));
    ("__sync_and_and_fetch", ("sync", "and", "new"));
    ("__sync_or_and_fetch", ("sync", "or", "new"));
    ("__sync_xor_and_fetch", ("sync", "xor", "new"));
    ("__sync_nand_and_fetch", ("sync", "nand", "new")) ].

Definition rmw_builtin (name : string) : option (string * string * string) :=
  assoc_str name rmw_builtin_table.

Definition fence_builtin (name : string) : bool :=
  str_in name
    [ "__c11_atomic_thread_fence"; "__c11_atomic_signal_fence";
      "__atomic_thread_fence"; "__atomic_signal_fence" ].

Definition rmw_atomic (name : string) : bool :=
  match rmw_builtin name with
  | Some _ => true
  | None =>
      str_in name
        [ "__c11_atomic_compare_exchange_strong";
          "__c11_atomic_compare_exchange_weak";
          "__atomic_compare_exchange_n";
          "__sync_val_compare_and_swap";
          "__sync_bool_compare_and_swap";
          "__sync_lock_release";
          "__sync_synchronize";
          "__atomic_test_and_set";
          "__atomic_clear" ]
  end.

Definition atomic_name (name : string) : bool :=
  str_in name
    [ "__atomic_load_n"; "__atomic_store_n";
      "__c11_atomic_load"; "__c11_atomic_store";
      "__c11_atomic_init" ] ||
  fence_builtin name || rmw_atomic name.

Definition hint_builtin (name : string) (args : list c_expr) : option c_expr :=
  if String.eqb name "__builtin_assume" then
    match args with [_] => Some (ENum 0 SufNone RadDec) | _ => None end
  else if String.eqb name "__builtin_prefetch" then
    match args with p :: _ => Some p | [] => None end
  else if String.eqb name "__builtin_ia32_pause" then
    match args with [] => Some (ENum 0 SufNone RadDec) | _ => None end
  else None.

Definition type_class_number (t : c_type) : option Z :=
  match t with
  | TVoid => Some 0
  | TIntK IBool => Some 4
  | TIntK _ => Some 1
  | TFloatK _ => Some 8
  | TPtr _ | TArray _ _ | TFunc _ _ _ => Some 5
  | TStruct _ => Some 12
  | TUnion _ => Some 13
  | _ => None
  end.

Inductive proto_ty_tag : Type :=
| PTVp | PTCvp | PTCp | PTCcp | PTInt | PTLong | PTSize | PTVoid.

Definition proto_type_spec (tag : proto_ty_tag) : list c_spec * c_dcl_type :=
  match tag with
  | PTVp => ([SpTspec "void"], DTPtr DTBase [])
  | PTCvp => ([SpQual "const"; SpTspec "void"], DTPtr DTBase [])
  | PTCp => ([SpTspec "char"], DTPtr DTBase [])
  | PTCcp => ([SpQual "const"; SpTspec "char"], DTPtr DTBase [])
  | PTInt => ([SpTspec "int"], DTBase)
  | PTLong => ([SpTspec "long"], DTBase)
  | PTSize => ([SpTspec "unsigned"; SpTspec "long"], DTBase)
  | PTVoid => ([SpTspec "void"], DTBase)
  end.

Definition library_proto_table : list (string * proto_ty_tag * list proto_ty_tag) :=
  [ ("memcpy", PTVp, [PTVp; PTCvp; PTSize]);
    ("memmove", PTVp, [PTVp; PTCvp; PTSize]);
    ("memset", PTVp, [PTVp; PTInt; PTSize]);
    ("memcmp", PTInt, [PTCvp; PTCvp; PTSize]);
    ("memchr", PTVp, [PTCvp; PTInt; PTSize]);
    ("mempcpy", PTVp, [PTVp; PTCvp; PTSize]);
    ("strlen", PTSize, [PTCcp]);
    ("strcmp", PTInt, [PTCcp; PTCcp]);
    ("strncmp", PTInt, [PTCcp; PTCcp; PTSize]);
    ("strcpy", PTCp, [PTCp; PTCcp]);
    ("strncpy", PTCp, [PTCp; PTCcp; PTSize]);
    ("stpcpy", PTCp, [PTCp; PTCcp]);
    ("strcat", PTCp, [PTCp; PTCcp]);
    ("strncat", PTCp, [PTCp; PTCcp; PTSize]);
    ("strchr", PTCp, [PTCcp; PTInt]);
    ("strrchr", PTCp, [PTCcp; PTInt]);
    ("strstr", PTCp, [PTCcp; PTCcp]);
    ("strdup", PTCp, [PTCcp]);
    ("malloc", PTVp, [PTSize]);
    ("calloc", PTVp, [PTSize; PTSize]);
    ("realloc", PTVp, [PTVp; PTSize]);
    ("free", PTVoid, [PTVp]);
    ("abort", PTVoid, []);
    ("abs", PTInt, [PTInt]);
    ("labs", PTLong, [PTLong]) ].

Definition builtin_declarations : list c_item :=
  map (fun '(fn_name, ret_tag, arg_tags) =>
    let '(r_specs, r_dcl) := proto_type_spec ret_tag in
    let ps := map (fun a =>
      let '(sp, d) := proto_type_spec a in Param sp (Dcl None d None)) arg_tags in
    let bname := "__builtin_" ++ fn_name in
    IDecl (Loc "builtin" 0) r_specs
      [InitDecl (Dcl (Some bname) (DTFunc r_dcl (PParams ps false)) (Some fn_name)) None])
    library_proto_table.

Definition filcc_refused_mnemonics : list string :=
  [ ".byte"; "call"; "clflush"; "cli"; "clts"; "emms"; "enter"; "fxsave";
    "hlt"; "icebp"; "in"; "inb"; "inl"; "insb"; "insl"; "insw"; "int";
    "int1"; "int3"; "into"; "inw"; "invd"; "iret"; "iretq"; "jmp"; "leave";
    "lgdt"; "lidt"; "lmsw"; "lock"; "monitor"; "mwait"; "out"; "outb";
    "outl"; "outsb"; "outsl"; "outsw"; "outw"; "pop"; "popf"; "push";
    "pushf"; "rdmsr"; "rdpmc"; "rdseed"; "rep"; "ret"; "sgdt"; "sidt";
    "std"; "sti"; "swapgs"; "syscall"; "sysenter"; "sysexit"; "sysret";
    "ud1"; "wbinvd"; "wrmsr"; "xsave" ].

Definition filcc_refused_mnemonic (m : string) : bool :=
  str_in m filcc_refused_mnemonics.

Definition cpu_feature_table : list (string * (string * Z * Z)) :=
  [ ("cmov", ("__cpu_model", 12, 1));
    ("mmx", ("__cpu_model", 12, 2));
    ("popcnt", ("__cpu_model", 12, 4));
    ("sse", ("__cpu_model", 12, 8));
    ("sse2", ("__cpu_model", 12, 16));
    ("sse3", ("__cpu_model", 12, 32));
    ("ssse3", ("__cpu_model", 12, 64));
    ("sse4.1", ("__cpu_model", 12, 128));
    ("sse4.2", ("__cpu_model", 12, 256));
    ("avx", ("__cpu_model", 12, 512));
    ("avx2", ("__cpu_model", 12, 1024));
    ("sse4a", ("__cpu_model", 12, 2048));
    ("fma4", ("__cpu_model", 12, 4096));
    ("xop", ("__cpu_model", 12, 8192));
    ("fma", ("__cpu_model", 12, 16384));
    ("avx512f", ("__cpu_model", 12, 32768));
    ("bmi", ("__cpu_model", 12, 65536));
    ("bmi2", ("__cpu_model", 12, 131072));
    ("aes", ("__cpu_model", 12, 262144));
    ("pclmul", ("__cpu_model", 12, 524288));
    ("avx512vl", ("__cpu_model", 12, 1048576));
    ("avx512bw", ("__cpu_model", 12, 2097152));
    ("avx512dq", ("__cpu_model", 12, 4194304));
    ("avx512cd", ("__cpu_model", 12, 8388608));
    ("avx512vbmi", ("__cpu_model", 12, 67108864));
    ("avx512ifma", ("__cpu_model", 12, 134217728));
    ("avx5124vnniw", ("__cpu_model", 12, 268435456));
    ("avx5124fmaps", ("__cpu_model", 12, 536870912));
    ("avx512vpopcntdq", ("__cpu_model", 12, 1073741824));
    ("avx512vbmi2", ("__cpu_model", 12, 2147483648));
    ("gfni", ("__cpu_features2", 0, 1));
    ("vpclmulqdq", ("__cpu_features2", 0, 2));
    ("avx512vnni", ("__cpu_features2", 0, 4));
    ("avx512bitalg", ("__cpu_features2", 0, 8));
    ("avx512bf16", ("__cpu_features2", 0, 16));
    ("avx512vp2intersect", ("__cpu_features2", 0, 32));
    ("adx", ("__cpu_features2", 0, 256));
    ("cldemote", ("__cpu_features2", 0, 1024));
    ("clflushopt", ("__cpu_features2", 0, 2048));
    ("clwb", ("__cpu_features2", 0, 4096));
    ("clzero", ("__cpu_features2", 0, 8192));
    ("enqcmd", ("__cpu_features2", 0, 65536));
    ("f16c", ("__cpu_features2", 0, 131072));
    ("fsgsbase", ("__cpu_features2", 0, 262144));
    ("lwp", ("__cpu_features2", 0, 16777216));
    ("lzcnt", ("__cpu_features2", 0, 33554432));
    ("movbe", ("__cpu_features2", 0, 67108864));
    ("movdir64b", ("__cpu_features2", 0, 134217728));
    ("movdiri", ("__cpu_features2", 0, 268435456));
    ("mwaitx", ("__cpu_features2", 0, 536870912));
    ("pconfig", ("__cpu_features2", 0, 2147483648));
    ("pku", ("__cpu_features2", 4, 1));
    ("prfchw", ("__cpu_features2", 4, 4));
    ("ptwrite", ("__cpu_features2", 4, 8));
    ("rdpid", ("__cpu_features2", 4, 16));
    ("rdrnd", ("__cpu_features2", 4, 32));
    ("rdseed", ("__cpu_features2", 4, 64));
    ("rtm", ("__cpu_features2", 4, 128));
    ("serialize", ("__cpu_features2", 4, 256));
    ("sgx", ("__cpu_features2", 4, 512));
    ("sha", ("__cpu_features2", 4, 1024));
    ("shstk", ("__cpu_features2", 4, 2048));
    ("tbm", ("__cpu_features2", 4, 4096));
    ("tsxldtrk", ("__cpu_features2", 4, 8192));
    ("vaes", ("__cpu_features2", 4, 16384));
    ("waitpkg", ("__cpu_features2", 4, 32768));
    ("wbnoinvd", ("__cpu_features2", 4, 65536));
    ("xsave", ("__cpu_features2", 4, 131072));
    ("xsavec", ("__cpu_features2", 4, 262144));
    ("xsaveopt", ("__cpu_features2", 4, 524288));
    ("xsaves", ("__cpu_features2", 4, 1048576));
    ("amx-tile", ("__cpu_features2", 4, 2097152));
    ("amx-int8", ("__cpu_features2", 4, 4194304));
    ("amx-bf16", ("__cpu_features2", 4, 8388608));
    ("uintr", ("__cpu_features2", 4, 16777216));
    ("hreset", ("__cpu_features2", 4, 33554432));
    ("kl", ("__cpu_features2", 4, 67108864));
    ("widekl", ("__cpu_features2", 4, 268435456));
    ("avxvnni", ("__cpu_features2", 4, 536870912));
    ("avx512fp16", ("__cpu_features2", 4, 1073741824));
    ("x86-64", ("__cpu_features2", 4, 2147483648));
    ("x86-64-v2", ("__cpu_features2", 8, 1));
    ("x86-64-v3", ("__cpu_features2", 8, 2));
    ("x86-64-v4", ("__cpu_features2", 8, 4));
    ("avxifma", ("__cpu_features2", 8, 8));
    ("avxvnniint8", ("__cpu_features2", 8, 16));
    ("avxneconvert", ("__cpu_features2", 8, 32));
    ("cmpccxadd", ("__cpu_features2", 8, 64));
    ("amx-fp16", ("__cpu_features2", 8, 128));
    ("prefetchi", ("__cpu_features2", 8, 256));
    ("raoint", ("__cpu_features2", 8, 512));
    ("amx-complex", ("__cpu_features2", 8, 1024));
    ("avxvnniint16", ("__cpu_features2", 8, 2048));
    ("sm3", ("__cpu_features2", 8, 4096));
    ("sha512", ("__cpu_features2", 8, 8192));
    ("sm4", ("__cpu_features2", 8, 16384));
    ("apxf", ("__cpu_features2", 8, 32768));
    ("usermsr", ("__cpu_features2", 8, 65536));
    ("avx10.1-256", ("__cpu_features2", 8, 131072));
    ("avx10.1-512", ("__cpu_features2", 8, 262144));
    ("avx10.2-256", ("__cpu_features2", 8, 524288));
    ("avx10.2-512", ("__cpu_features2", 8, 1048576)) ].

Definition cpu_feature (name : string) : option (string * Z * Z) :=
  assoc_str name cpu_feature_table.

Definition cpu_model_table : list (string * (Z * Z)) :=
  [ ("intel", (0, 1)); ("amd", (0, 2));
    ("atom", (4, 1)); ("core2", (4, 2));
    ("corei7", (4, 3)); ("amdfam10h", (4, 4));
    ("amdfam15h", (4, 5)); ("amdfam17h", (4, 10));
    ("amdfam19h", (4, 15)); ("amdfam1ah", (4, 20));
    ("bonnell", (4, 1)); ("silvermont", (4, 6));
    ("slm", (4, 6)); ("knl", (4, 7));
    ("knm", (4, 11)); ("goldmont", (4, 12));
    ("goldmont-plus", (4, 13)); ("tremont", (4, 14));
    ("sierraforest", (4, 17)); ("grandridge", (4, 18));
    ("clearwaterforest", (4, 19)); ("nehalem", (8, 1));
    ("westmere", (8, 2)); ("sandybridge", (8, 3));
    ("ivybridge", (8, 12)); ("haswell", (8, 13));
    ("broadwell", (8, 14)); ("skylake", (8, 15));
    ("skylake-avx512", (8, 16)); ("cannonlake", (8, 17));
    ("icelake-client", (8, 18)); ("icelake-server", (8, 19));
    ("cascadelake", (8, 21)); ("tigerlake", (8, 22));
    ("cooperlake", (8, 23)); ("sapphirerapids", (8, 24));
    ("alderlake", (8, 25)); ("raptorlake", (8, 25));
    ("meteorlake", (8, 25)); ("rocketlake", (8, 27));
    ("graniterapids", (8, 30)); ("graniterapids-d", (8, 31));
    ("arrowlake", (8, 32)); ("arrowlake-s", (8, 33));
    ("lunarlake", (8, 33)); ("pantherlake", (8, 34));
    ("gracemont", (8, 25)); ("emeraldrapids", (8, 24));
    ("diamondrapids", (8, 36)); ("barcelona", (8, 4));
    ("shanghai", (8, 5)); ("istanbul", (8, 6));
    ("btver1", (4, 8)); ("btver2", (4, 9));
    ("bdver1", (8, 7)); ("bdver2", (8, 8));
    ("bdver3", (8, 9)); ("bdver4", (8, 10));
    ("znver1", (8, 11)); ("znver2", (8, 20));
    ("znver3", (8, 26)); ("znver4", (8, 29));
    ("znver5", (8, 35)) ].

Definition cpu_model_value (name : string) : option (Z * Z) :=
  assoc_str name cpu_model_table.
