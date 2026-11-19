(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_intl_dcgettext_os Unit_intl_dcigettext_os Unit_locale_localename_os Unit_misc_tsearch_os Unit_nptl_pthread_rwlock_rdlock_os Unit_nptl_pthread_rwlock_unlock_os Unit_string_memcpy_os Unit_string_mempcpy_os.
From Glibc Require Import Unit_string_stpcpy_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).


(** ## Provenance

    The producer linked GNU Hello's 81 checked objects with 333 user glibc
    units by `rocq/scripts/link.pl --ctors main,__libc_start_main`. The objects come from the
    flake output `checks.x86_64-linux.nanofil-hello-fixture.captured`, and the units come from
    the capture `/nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44`.
    These SHA-256 digests identify the inputs and the result:

    - objects, by name and term digest: `5b7ba233e0adedaff060ffdce2b533211d3d360ee7af82a2201a816c261fe53b`
    - units, by name and term digest: `a6dedf5c33d6c177ae56c94ebc438b2ed0ea4ef314de4e22c4faf28d4a61c243`
    - the whole linked image: `d41e2c79f1408cfbb4b74c9b5c980cf5f934f08e940a152cebce3054f146b8b9`

    The producer selected the items below from the full linked image.
    It checked that each selected name has one item and that its term
    agrees with the term in the `intl/GettextLink` fixture.

    - __GI___dcgettext: unique function, sha256 c3cafe1a70b0e8086b934298a41dcab92d2853b65720ec2131df79874e8c1a54, equal to reference
    - __dcigettext: unique function, sha256 fe22c599f4b9ba7096ace92eee536f83cc73f2cdf0dc3d72f2b23bea99eb06cc, equal to reference
    - __current_locale_name: unique function, sha256 6e0c342508151c9e63ec8505a4418bf2564c9ffa10650d30037712cac9f78769, equal to reference
    - __GI___tfind: unique function, sha256 90f72e023ac6738aa50b140267eb26cb0e9bb30b7e403a84f7977f14d5ba2e62, equal to reference
    - ___pthread_rwlock_rdlock: unique function, sha256 16c76fcfd20d384dfbd38a259b375afee2add66f56837fcfcca88dd0325bb0a1, equal to reference
    - __GI___pthread_rwlock_rdlock: unique alias (export) of ___pthread_rwlock_rdlock, sha256 919717840eebee74045f6e4862ef56b053789ea70b2171491328c64a773b0f31, equal to reference
    - ___pthread_rwlock_unlock: unique function, sha256 3c1869662c8428acb685e6d9d8c3792f7ca0aa59bd966af440d9205b3b3e6d60, equal to reference
    - __GI___pthread_rwlock_unlock: unique alias (export) of ___pthread_rwlock_unlock, sha256 3b044fcd93962498e34466ba86de48eaebe008a12e68ec1306ecdf0f18f540d4, equal to reference
    - __GI_memcpy: unique function, sha256 20acbd0a31aef562725c2ffaa8b17c33821910940a8ea68aae7916b500c8ed16, equal to reference
    - __GI___mempcpy: unique function, sha256 68fd33c62846eb473cf31ff4ce80e0e2b13176eeedb5ddb402675c6d4e73b961, equal to reference
    - __GI_mempcpy: unique alias (export) of __GI___mempcpy, sha256 8b84480b764c2f3d0f3dfd59bb4371ae88af8167bd6fb4756721ffe561f99ab9, equal to reference
    - __GI___stpcpy: unique function, sha256 13059ae962fd0c5b424ac1a5403a9b0be39c364e7c4734baec0885d7b100c1e3, equal to reference
    - __GI_stpcpy: unique alias (weak) of __GI___stpcpy, sha256 cd71936287b85db024adc88731d7038a6b8dfa141fad8c2df3174c6a215544d6, equal to reference
*)
Definition hellogettextimage_module : module :=
  [IFunc Unit_intl_dcgettext_os.fn___GI___dcgettext;
  IFunc Unit_intl_dcigettext_os.fn___dcigettext;
  IFunc Unit_locale_localename_os.fn___current_locale_name;
  IFunc Unit_misc_tsearch_os.fn___GI___tfind;
  IFunc Unit_nptl_pthread_rwlock_rdlock_os.fn____pthread_rwlock_rdlock;
  Unit_nptl_pthread_rwlock_rdlock_os.item___GI___pthread_rwlock_rdlock;
  IFunc Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock;
  Unit_nptl_pthread_rwlock_unlock_os.item___GI___pthread_rwlock_unlock;
  IFunc Unit_string_memcpy_os.fn___GI_memcpy;
  IFunc Unit_string_mempcpy_os.fn___GI___mempcpy;
  Unit_string_mempcpy_os.item___GI_mempcpy;
  IFunc Unit_string_stpcpy_os.fn___GI___stpcpy;
  Unit_string_stpcpy_os.item___GI_stpcpy].
