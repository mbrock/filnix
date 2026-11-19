(** This file defines checked IR from glibc’s `stdio-common/errname.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRBytes IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___get_errname : func :=
  ir_fn{ "export" "__get_errname"(W %"v0") -> (RClass P) {
  @"start":
    %"v8" : W = (Cmp Slt W) %"v0", #0
    => br %"v8" ? "L10" : "L9";
  @"L9":
    %"v15" : L = (Ext Sw) %"v0";
    %"v16" : W = (Cmp Uge L) %"v15", #134
    => goto "L10";
  @"L10" [%"v18" : W = phi("start" => #1, "L9" => %"v16")]:
    => br %"v18" ? "L20" : "L19";
  @"L19":
    %"v22" : W = (Cmp Sgt W) %"v0", #0
    => br %"v22" ? "L23" : "L20";
  @"L23":
    %"v25" : P = Copy $"glibc_errname#_sys_errnameidx";
    %"v27" : L = (Ext Sw) %"v0";
    %"v28" : L = Shl %"v27", #1;
    %"v29" = %"v25" +p %"v28";
    %"chk0" : A = (Check 0 2 Read 1) %"v29";
    %"v30" : W = (RawLoad (LdNarrow Uh) 0) %"chk0";
    %"v31" : W = (Cmp Eq W) %"v30", #0
    => goto "L20";
  @"L20" [%"v35" : W = phi("L10" => #1, "L19" => #0, "L23" => %"v31")]:
    => br %"v35" ? "L4" : "L6";
  @"L4":
    => ret #0;
  @"L6":
    %"v37" : P = Copy $"glibc_errname#_sys_errname";
    %"v38" : P = Copy $"glibc_errname#_sys_errnameidx";
    %"v40" : L = (Ext Sw) %"v0";
    %"v41" : L = Shl %"v40", #1;
    %"v42" = %"v38" +p %"v41";
    %"chk1" : A = (Check 0 2 Read 1) %"v42";
    %"v43" : W = (RawLoad (LdNarrow Uh) 0) %"chk1";
    %"v44" : L = (Ext Uw) %"v43";
    %"v45" = %"v37" +p %"v44"
    => ret %"v45"
} }.

Definition item_glibc_errname'23_sys_errname : item :=
  (IData (a "glibc_errname#_sys_errname") (LRo (a "local")) 1 (app (app (app ["0"%irbytes; (Zero 1); "EPERM"%irbytes; (Zero 1); "ENOENT"%irbytes; (Zero 1); "ESRCH"%irbytes; (Zero 1); "EINTR"%irbytes; (Zero 1); "EIO"%irbytes; (Zero 1); "ENXIO"%irbytes; (Zero 1); "E2BIG"%irbytes; (Zero 1); "ENOEXEC"%irbytes; (Zero 1); "EBADF"%irbytes; (Zero 1); "ECHILD"%irbytes; (Zero 1); "EDEADLK"%irbytes; (Zero 1); "ENOMEM"%irbytes; (Zero 1); "EACCES"%irbytes; (Zero 1); "EFAULT"%irbytes; (Zero 1); "ENOTBLK"%irbytes; (Zero 1); "EBUSY"%irbytes] [(Zero 1); "EEXIST"%irbytes; (Zero 1); "EXDEV"%irbytes; (Zero 1); "ENODEV"%irbytes; (Zero 1); "ENOTDIR"%irbytes; (Zero 1); "EISDIR"%irbytes; (Zero 1); "EINVAL"%irbytes; (Zero 1); "EMFILE"%irbytes; (Zero 1); "ENFILE"%irbytes; (Zero 1); "ENOTTY"%irbytes; (Zero 1); "ETXTBSY"%irbytes; (Zero 1); "EFBIG"%irbytes; (Zero 1); "ENOSPC"%irbytes; (Zero 1); "ESPIPE"%irbytes; (Zero 1); "EROFS"%irbytes; (Zero 1); "EMLINK"%irbytes; (Zero 1); "EPIPE"%irbytes; (Zero 1)]) (app ["EDOM"%irbytes; (Zero 1); "ERANGE"%irbytes; (Zero 1); "EAGAIN"%irbytes; (Zero 1); "EINPROGRESS"%irbytes; (Zero 1); "EALREADY"%irbytes; (Zero 1); "ENOTSOCK"%irbytes; (Zero 1); "EMSGSIZE"%irbytes; (Zero 1); "EPROTOTYPE"%irbytes; (Zero 1); "ENOPROTOOPT"%irbytes; (Zero 1); "EPROTONOSUPPORT"%irbytes; (Zero 1); "ESOCKTNOSUPPORT"%irbytes; (Zero 1); "EOPNOTSUPP"%irbytes; (Zero 1); "EPFNOSUPPORT"%irbytes; (Zero 1); "EAFNOSUPPORT"%irbytes; (Zero 1); "EADDRINUSE"%irbytes; (Zero 1); "EADDRNOTAVAIL"%irbytes; (Zero 1); "ENETDOWN"%irbytes] [(Zero 1); "ENETUNREACH"%irbytes; (Zero 1); "ENETRESET"%irbytes; (Zero 1); "ECONNABORTED"%irbytes; (Zero 1); "ECONNRESET"%irbytes; (Zero 1); "ENOBUFS"%irbytes; (Zero 1); "EISCONN"%irbytes; (Zero 1); "ENOTCONN"%irbytes; (Zero 1); "EDESTADDRREQ"%irbytes; (Zero 1); "ESHUTDOWN"%irbytes; (Zero 1); "ETOOMANYREFS"%irbytes; (Zero 1); "ETIMEDOUT"%irbytes; (Zero 1); "ECONNREFUSED"%irbytes; (Zero 1); "ELOOP"%irbytes; (Zero 1); "ENAMETOOLONG"%irbytes; (Zero 1); "EHOSTDOWN"%irbytes; (Zero 1); "EHOSTUNREACH"%irbytes; (Zero 1)])) (app (app ["ENOTEMPTY"%irbytes; (Zero 1); "EUSERS"%irbytes; (Zero 1); "EDQUOT"%irbytes; (Zero 1); "ESTALE"%irbytes; (Zero 1); "EREMOTE"%irbytes; (Zero 1); "ENOLCK"%irbytes; (Zero 1); "ENOSYS"%irbytes; (Zero 1); "EILSEQ"%irbytes; (Zero 1); "EBADMSG"%irbytes; (Zero 1); "EIDRM"%irbytes; (Zero 1); "EMULTIHOP"%irbytes; (Zero 1); "ENODATA"%irbytes; (Zero 1); "ENOLINK"%irbytes; (Zero 1); "ENOMSG"%irbytes; (Zero 1); "ENOSR"%irbytes; (Zero 1); "ENOSTR"%irbytes; (Zero 1); "EOVERFLOW"%irbytes] [(Zero 1); "EPROTO"%irbytes; (Zero 1); "ETIME"%irbytes; (Zero 1); "ECANCELED"%irbytes; (Zero 1); "EOWNERDEAD"%irbytes; (Zero 1); "ENOTRECOVERABLE"%irbytes; (Zero 1); "ERESTART"%irbytes; (Zero 1); "ECHRNG"%irbytes; (Zero 1); "EL2NSYNC"%irbytes; (Zero 1); "EL3HLT"%irbytes; (Zero 1); "EL3RST"%irbytes; (Zero 1); "ELNRNG"%irbytes; (Zero 1); "EUNATCH"%irbytes; (Zero 1); "ENOCSI"%irbytes; (Zero 1); "EL2HLT"%irbytes; (Zero 1); "EBADE"%irbytes; (Zero 1); "EBADR"%irbytes; (Zero 1)]) (app ["EXFULL"%irbytes; (Zero 1); "ENOANO"%irbytes; (Zero 1); "EBADRQC"%irbytes; (Zero 1); "EBADSLT"%irbytes; (Zero 1); "EBFONT"%irbytes; (Zero 1); "ENONET"%irbytes; (Zero 1); "ENOPKG"%irbytes; (Zero 1); "EADV"%irbytes; (Zero 1); "ESRMNT"%irbytes; (Zero 1); "ECOMM"%irbytes; (Zero 1); "EDOTDOT"%irbytes; (Zero 1); "ENOTUNIQ"%irbytes; (Zero 1); "EBADFD"%irbytes; (Zero 1); "EREMCHG"%irbytes; (Zero 1); "ELIBACC"%irbytes; (Zero 1); "ELIBBAD"%irbytes; (Zero 1); "ELIBSCN"%irbytes] [(Zero 1); "ELIBMAX"%irbytes; (Zero 1); "ELIBEXEC"%irbytes; (Zero 1); "ESTRPIPE"%irbytes; (Zero 1); "EUCLEAN"%irbytes; (Zero 1); "ENOTNAM"%irbytes; (Zero 1); "ENAVAIL"%irbytes; (Zero 1); "EISNAM"%irbytes; (Zero 1); "EREMOTEIO"%irbytes; (Zero 1); "ENOMEDIUM"%irbytes; (Zero 1); "EMEDIUMTYPE"%irbytes; (Zero 1); "ENOKEY"%irbytes; (Zero 1); "EKEYEXPIRED"%irbytes; (Zero 1); "EKEYREVOKED"%irbytes; (Zero 1); "EKEYREJECTED"%irbytes; (Zero 1); "ERFKILL"%irbytes; (Zero 1); "EHWPOISON"%irbytes; (Zero 1)])))).

Definition item_glibc_errname'23_sys_errnameidx : item :=
  (IData (a "glibc_errname#_sys_errnameidx") (LRo (a "local")) 2 (app (app [(Item Wh 0); (Item Wh 2); (Item Wh 8); (Item Wh 15); (Item Wh 21); (Item Wh 27); (Item Wh 31); (Item Wh 37); (Item Wh 43); (Item Wh 51); (Item Wh 57); (Item Wh 229); (Item Wh 72); (Item Wh 79); (Item Wh 86); (Item Wh 93); (Item Wh 101); (Item Wh 107); (Item Wh 114); (Item Wh 120); (Item Wh 127); (Item Wh 135); (Item Wh 142); (Item Wh 156); (Item Wh 149); (Item Wh 163); (Item Wh 170); (Item Wh 178); (Item Wh 184); (Item Wh 191); (Item Wh 198); (Item Wh 204); (Item Wh 211)] [(Item Wh 217); (Item Wh 222); (Item Wh 64); (Item Wh 537); (Item Wh 612); (Item Wh 619); (Item Wh 573); (Item Wh 531); (Zero 2); (Item Wh 673); (Item Wh 641); (Item Wh 762); (Item Wh 769); (Item Wh 778); (Item Wh 785); (Item Wh 792); (Item Wh 799); (Item Wh 807); (Item Wh 814); (Item Wh 821); (Item Wh 827); (Item Wh 833); (Item Wh 840); (Item Wh 847); (Item Wh 855); (Zero 2); (Item Wh 863); (Item Wh 686); (Item Wh 657); (Item Wh 710); (Item Wh 680); (Item Wh 870); (Item Wh 877); (Item Wh 604)]) (app [(Item Wh 665); (Item Wh 884); (Item Wh 889); (Item Wh 896); (Item Wh 703); (Item Wh 647); (Item Wh 902); (Item Wh 633); (Item Wh 693); (Item Wh 910); (Item Wh 919); (Item Wh 926); (Item Wh 934); (Item Wh 942); (Item Wh 950); (Item Wh 958); (Item Wh 966); (Item Wh 626); (Item Wh 753); (Item Wh 975); (Item Wh 583); (Item Wh 257); (Item Wh 472); (Item Wh 266); (Item Wh 275); (Item Wh 286); (Item Wh 298); (Item Wh 314); (Item Wh 330); (Item Wh 341); (Item Wh 354); (Item Wh 367); (Item Wh 378)] [(Item Wh 392); (Item Wh 401); (Item Wh 413); (Item Wh 423); (Item Wh 436); (Item Wh 447); (Item Wh 455); (Item Wh 463); (Item Wh 485); (Item Wh 495); (Item Wh 508); (Item Wh 518); (Item Wh 550); (Item Wh 560); (Item Wh 248); (Item Wh 236); (Item Wh 597); (Item Wh 984); (Item Wh 992); (Item Wh 1000); (Item Wh 1008); (Item Wh 1015); (Item Wh 590); (Item Wh 1025); (Item Wh 1035); (Item Wh 716); (Item Wh 1047); (Item Wh 1054); (Item Wh 1066); (Item Wh 1078); (Item Wh 726); (Item Wh 737); (Item Wh 1091); (Item Wh 1099)]))).
