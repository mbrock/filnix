(** This file contains part of glibc's checked option-parser module.
    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition getopt_blocks_03 : list term :=
  [
        cap_blk{ @"L302":
          %"v306" : "w" = op "raw_load"("sw", int 0) %"chk100";
          %"v307" : "l" = op "ext"("sw") %"v306";
          %"v308" : "l" = "shl" %"v307", #3;
          %"v309" = %"v2" +p %"v308";
          %"chk109" : "a" = op "check"(int 0, int 8, "read", int 8) %"v309";
          %"v310" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk109";
          %"v311" = %"v310" +p #1;
          %"chk110" : "a" = op "check"(int 0, int 1, "read", int 1) %"v311";
          %"v312" : "w" = op "raw_load"("sb", int 0) %"chk110";
          %"v313" : "w" = op "cmp"("eq", "w") %"v312", #0
          => goto "L303" };
        cap_blk{ @"L303" [phi %"v315" : "w" = ("L268" => #1, "L302" => %"v313")]:
          => br %"v315" ? "L289" : "L291" };
        cap_blk{ @"L289":
          %"v320" = %"v12" +p #40;
          %"chk111" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk0", %"v320";
          %"v321" : "w" = op "raw_load"("uw", int 0) %"chk111";
          %"v322" : "w" = op "cmp"("eq", "w") %"v321", #0
          => br %"v322" ? "L316" : "L318" };
        cap_blk{ @"L316":
          => ret #4294967295 };
        cap_blk{ @"L318":
          %"v326" = %"v12" +p #16;
          %"v329" : "w" = op "raw_load"("sw", int 0) %"chk100";
          %"v330" : "w" = "add" %"v329", #1;
          %"chk113" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk113" + 0] <- %"v330";
          %"v331" : "l" = op "ext"("sw") %"v329";
          %"v332" : "l" = "shl" %"v331", #3;
          %"v333" = %"v2" +p %"v332";
          %"chk114" : "a" = op "check"(int 0, int 8, "read", int 8) %"v333";
          %"v334" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk114";
          %"chk115" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v326";
          store.ptr [%"chk115" + 0] <- %"v334"
          => ret #1 };
        cap_blk{ @"L291":
          %"v340" : "l" = "ptoi" %"v6";
          %"v341" : "w" = op "cmp"("ne", "l") %"v340", #0
          => br %"v341" ? "L336" : "L338" };
        cap_blk{ @"L336":
          %"v347" : "w" = op "raw_load"("sw", int 0) %"chk100";
          %"v348" : "l" = op "ext"("sw") %"v347";
          %"v349" : "l" = "shl" %"v348", #3;
          %"v350" = %"v2" +p %"v349";
          %"chk117" : "a" = op "check"(int 0, int 8, "read", int 8) %"v350";
          %"v351" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk117";
          %"v352" = %"v351" +p #1;
          %"chk118" : "a" = op "check"(int 0, int 1, "read", int 1) %"v352";
          %"v353" : "w" = op "raw_load"("sb", int 0) %"chk118";
          %"v354" : "w" = op "cmp"("eq", "w") %"v353", #45
          => br %"v354" ? "L342" : "L344" };
        cap_blk{ @"L342":
          %"v356" = %"v12" +p #32;
          %"v359" : "w" = op "raw_load"("sw", int 0) %"chk100";
          %"v360" : "l" = op "ext"("sw") %"v359";
          %"v361" : "l" = "shl" %"v360", #3;
          %"v362" = %"v2" +p %"v361";
          %"chk120" : "a" = op "check"(int 0, int 8, "read", int 8) %"v362";
          %"v363" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk120";
          %"v364" = %"v363" +p #2;
          %"chk121" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk20", %"v356";
          store.ptr [%"chk121" + 0] <- %"v364";
          %"v373" : "p" = "copy" $"glibc_getopt#str.146";
          call %"v374" : "w" = $"glibc_getopt#process_long_option"("w" %"v0", "p" %"v2", "p" %"pr.1", "p" %"v6", "p" %"v8", "w" %"v10", "p" %"v12", "w" %"pr.3", "p" %"v373")
          => ret %"v374" };
        cap_blk{ @"L344":
          => br %"v10" ? "L380" : "L381" };
        cap_blk{ @"L380":
          %"v384" : "w" = op "raw_load"("sw", int 0) %"chk100";
          %"v385" : "l" = op "ext"("sw") %"v384";
          %"v386" : "l" = "shl" %"v385", #3;
          %"v387" = %"v2" +p %"v386";
          %"chk123" : "a" = op "check"(int 0, int 8, "read", int 8) %"v387";
          %"v388" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk123";
          %"v389" = %"v388" +p #2;
          %"chk124" : "a" = op "check"(int 0, int 1, "read", int 1) %"v389";
          %"v390" : "w" = op "raw_load"("sb", int 0) %"chk124"
          => br %"v390" ? "L381" : "L391" };
        cap_blk{ @"L391":
          %"v396" : "w" = op "raw_load"("sw", int 0) %"chk100";
          %"v397" : "l" = op "ext"("sw") %"v396";
          %"v398" : "l" = "shl" %"v397", #3;
          %"v399" = %"v2" +p %"v398";
          %"chk126" : "a" = op "check"(int 0, int 8, "read", int 8) %"v399";
          %"v400" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk126";
          %"v401" = %"v400" +p #1;
          %"chk127" : "a" = op "check"(int 0, int 1, "read", int 1) %"v401";
          %"v402" : "w" = op "raw_load"("sb", int 0) %"chk127";
          call %"v403" : "p" = $"__GI_strchr"("p" %"pr.1", "w" %"v402");
          %"v404" : "l" = "ptoi" %"v403";
          %"v406" : "w" = op "cmp"("eq", "l") %"v404", #0
          => goto "L381" };
        cap_blk{ @"L381" [phi %"v410" : "w" = ("L344" => #0, "L380" => #1, "L391" => %"v406")]:
          => br %"v410" ? "L376" : "L338" };
        cap_blk{ @"L376":
          %"v413" = %"v12" +p #32;
          %"chk128" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v416" : "w" = op "raw_load"("sw", int 0) %"chk128";
          %"v417" : "l" = op "ext"("sw") %"v416";
          %"v418" : "l" = "shl" %"v417", #3;
          %"v419" = %"v2" +p %"v418";
          %"chk129" : "a" = op "check"(int 0, int 8, "read", int 8) %"v419";
          %"v420" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk129";
          %"v421" = %"v420" +p #1;
          %"chk130" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk20", %"v413";
          store.ptr [%"chk130" + 0] <- %"v421";
          %"v430" : "p" = "copy" $"glibc_getopt#str.147";
          call %"v431" : "w" = $"glibc_getopt#process_long_option"("w" %"v0", "p" %"v2", "p" %"pr.1", "p" %"v6", "p" %"v8", "w" %"v10", "p" %"v12", "w" %"pr.3", "p" %"v430");
          %"v437" : "w" = op "cmp"("ne", "w") %"v431", #4294967295
          => br %"v437" ? "L432" : "L338" };
        cap_blk{ @"L432":
          => ret %"v431" };
        cap_blk{ @"L338":
          %"v441" = %"v12" +p #32;
          %"chk131" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v444" : "w" = op "raw_load"("sw", int 0) %"chk131";
          %"v445" : "l" = op "ext"("sw") %"v444";
          %"v446" : "l" = "shl" %"v445", #3;
          %"v447" = %"v2" +p %"v446";
          %"chk132" : "a" = op "check"(int 0, int 8, "read", int 8) %"v447";
          %"v448" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk132";
          %"v449" = %"v448" +p #1;
          %"chk133" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk20", %"v441";
          store.ptr [%"chk133" + 0] <- %"v449"
          => goto "L75" };
        cap_blk{ @"L75":
          %"v452" = %"v12" +p #32;
          %"chk134" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk20", %"v452";
          %"v453" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk134";
          %"v454" = %"v453" +p #1;
          %"chk135" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk20", %"v452";
          store.ptr [%"chk135" + 0] <- %"v454";
          %"chk136" : "a" = op "check"(int 0, int 1, "read", int 1) %"v453";
          %"v455" : "w" = op "raw_load"("sb", int 0) %"chk136";
          call %"v459" : "p" = $"__GI_strchr"("p" %"pr.1", "w" %"v455");
          %"chk137" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk20", %"v452";
          %"v465" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk137";
          %"chk138" : "a" = op "check"(int 0, int 1, "read", int 1) %"v465";
          %"v466" : "w" = op "raw_load"("sb", int 0) %"chk138";
          %"v467" : "w" = op "cmp"("eq", "w") %"v466", #0
          => br %"v467" ? "L460" : "L462" };
        cap_blk{ @"L460":
          %"chk139" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v469" : "w" = op "raw_load"("sw", int 0) %"chk139";
          %"v470" : "w" = "add" %"v469", #1;
          %"chk140" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk140" + 0] <- %"v470"
          => goto "L462" };
        cap_blk{ @"L462":
          %"v475" : "l" = "ptoi" %"v459";
          %"v477" : "w" = op "cmp"("eq", "l") %"v475", %"v80"
          => br %"v477" ? "L479" : "L478" };
        cap_blk{ @"L478":
          %"v481" : "w" = op "cmp"("eq", "w") %"v455", #58
          => goto "L479" };
        cap_blk{ @"L479" [phi %"v483" : "w" = ("L462" => #1, "L478" => %"v481")]:
          => br %"v483" ? "L485" : "L484" };
        cap_blk{ @"L484":
          %"v487" : "w" = op "cmp"("eq", "w") %"v455", #59
          => goto "L485" };
        cap_blk{ @"L485" [phi %"v489" : "w" = ("L479" => #1, "L484" => %"v487")]:
          => br %"v489" ? "L471" : "L473" };
        cap_blk{ @"L471":
          => br %"pr.3" ? "L490" : "L492" };
        cap_blk{ @"L490":
          %"v494" : "p" = "copy" $"stderr";
          %"chk141" : "a" = op "check"(int 0, int 8, "read", int 8) %"v494";
          %"v495" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk141";
          %"v496" : "p" = "copy" $"__GI__libc_intl_domainname";
          %"v497" : "p" = "copy" $"glibc_getopt#str.148";
          call %"v498" : "p" = $"__GI___dcgettext"("p" %"v496", "p" %"v497", "w" #5);
          %"chk142" : "a" = op "check"(int 0, int 8, "read", int 8) %"v2";
          %"v501" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk142";
          call %"v503" : "w" = $"__fxprintf_nocancel"("p" %"v495", "p" %"v498", "p" %"v501", "w" %"v455")
          => goto "L492" };
        cap_blk{ @"L492":
          %"v505" = %"v12" +p #8;
          %"chk143" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"v505";
          store "w" [%"chk143" + 0] <- %"v455"
          => ret #63 };
        cap_blk{ @"L473":
          %"chk144" : "a" = op "check"(int 0, int 1, "read", int 1) %"v459";
          %"v513" : "w" = op "raw_load"("sb", int 0) %"chk144";
          %"v514" : "w" = op "cmp"("eq", "w") %"v513", #87
          => br %"v514" ? "L515" : "L516" };
        cap_blk{ @"L515":
          %"v518" = %"v459" +p #1;
          %"chk145" : "a" = op "half_check"("upper", int 0, int 1, "read", int 1) %"chk144", %"v518";
          %"v519" : "w" = op "raw_load"("sb", int 0) %"chk145";
          %"v520" : "w" = op "cmp"("eq", "w") %"v519", #59
          => goto "L516" };
        cap_blk{ @"L516" [phi %"v522" : "w" = ("L473" => #0, "L515" => %"v520")]:
          => br %"v522" ? "L523" : "L524" };
        cap_blk{ @"L523":
          %"v526" : "l" = "ptoi" %"v6";
          %"v528" : "w" = op "cmp"("ne", "l") %"v526", %"v80"
          => goto "L524" };
        cap_blk{ @"L524" [phi %"v530" : "w" = ("L516" => #0, "L523" => %"v528")]:
          => br %"v530" ? "L508" : "L510" };
        cap_blk{ @"L508":
          %"v535" = %"v12" +p #32;
          %"v536" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk137";
          %"chk147" : "a" = op "check"(int 0, int 1, "read", int 1) %"v536";
          %"v537" : "w" = op "raw_load"("sb", int 0) %"chk147";
          %"v538" : "w" = op "cmp"("ne", "w") %"v537", #0
          => br %"v538" ? "L531" : "L532" };
        cap_blk{ @"L531":
          %"v540" = %"v12" +p #16;
          %"v542" = %"v12" +p #32;
          %"v543" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk137";
          %"chk149" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v540";
          store.ptr [%"chk149" + 0] <- %"v543"
          => goto "L533" };
        cap_blk{ @"L532":
          %"chk150" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v548" : "w" = op "raw_load"("sw", int 0) %"chk150";
          %"v550" : "w" = op "cmp"("eq", "w") %"v548", %"v0"
          => br %"v550" ? "L544" : "L545" };
        cap_blk{ @"L544":
          => br %"pr.3" ? "L551" : "L553" };
        cap_blk{ @"L551":
          %"v555" : "p" = "copy" $"stderr";
          %"chk151" : "a" = op "check"(int 0, int 8, "read", int 8) %"v555";
          %"v556" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk151";
          %"v557" : "p" = "copy" $"__GI__libc_intl_domainname";
          %"v558" : "p" = "copy" $"glibc_getopt#str.149";
          call %"v559" : "p" = $"__GI___dcgettext"("p" %"v557", "p" %"v558", "w" #5);
          %"chk152" : "a" = op "check"(int 0, int 8, "read", int 8) %"v2";
          %"v562" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk152";
          call %"v564" : "w" = $"__fxprintf_nocancel"("p" %"v556", "p" %"v559", "p" %"v562", "w" %"v455")
          => goto "L553" };
        cap_blk{ @"L553":
          %"v566" = %"v12" +p #8;
          %"chk153" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"v566";
          store "w" [%"chk153" + 0] <- %"v455";
          %"chk154" : "a" = op "renew"(int 0, int 1, "read", int 1) %"chk19", %"pr.1";
          %"v573" : "w" = op "raw_load"("sb", int 0) %"chk154";
          %"v574" : "w" = op "cmp"("eq", "w") %"v573", #58
          => br %"v574" ? "L570" : "L569" };
        cap_blk{ @"L569":
          => goto "L570" };
        cap_blk{ @"L570" [phi %"pr.4" : "w" = ("L569" => #63, "L553" => #58)]:
          %"v575" : "w" = op "ext"("sb") %"pr.4"
          => ret %"v575" };
        cap_blk{ @"L545":
          %"v578" = %"v12" +p #16;
          %"v581" : "w" = op "raw_load"("sw", int 0) %"chk150";
          %"v582" : "l" = op "ext"("sw") %"v581";
          %"v583" : "l" = "shl" %"v582", #3;
          %"v584" = %"v2" +p %"v583";
          %"chk156" : "a" = op "check"(int 0, int 8, "read", int 8) %"v584";
          %"v585" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk156";
          %"chk157" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v578";
          store.ptr [%"chk157" + 0] <- %"v585"
          => goto "L533" };
        cap_blk{ @"L533":
          %"v587" = %"v12" +p #32;
          %"v589" = %"v12" +p #16;
          %"chk158" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"v589";
          %"v590" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk158";
          %"chk159" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk20", %"v587";
          store.ptr [%"chk159" + 0] <- %"v590";
          %"chk160" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v589";
          store.ptr [%"chk160" + 0] <- #0;
          %"v600" : "p" = "copy" $"glibc_getopt#str.150";
          call %"v601" : "w" = $"glibc_getopt#process_long_option"("w" %"v0", "p" %"v2", "p" %"pr.1", "p" %"v6", "p" %"v8", "w" #0, "p" %"v12", "w" %"pr.3", "p" %"v600")
          => ret %"v601" };
        cap_blk{ @"L510":
          %"v607" = %"v459" +p #1;
          %"chk161" : "a" = op "half_check"("upper", int 0, int 1, "read", int 1) %"chk144", %"v607";
          %"v608" : "w" = op "raw_load"("sb", int 0) %"chk161";
          %"v609" : "w" = op "cmp"("eq", "w") %"v608", #58
          => br %"v609" ? "L603" : "L605" };
        cap_blk{ @"L603":
          %"v614" = %"v459" +p #2;
          %"chk162" : "a" = op "half_check"("upper", int 0, int 1, "read", int 1) %"chk144", %"v614";
          %"v615" : "w" = op "raw_load"("sb", int 0) %"chk162";
          %"v616" : "w" = op "cmp"("eq", "w") %"v615", #58
          => br %"v616" ? "L610" : "L611" };
        cap_blk{ @"L610":
          %"v621" = %"v12" +p #32;
          %"v622" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk137";
          %"chk164" : "a" = op "check"(int 0, int 1, "read", int 1) %"v622";
          %"v623" : "w" = op "raw_load"("sb", int 0) %"chk164";
          %"v624" : "w" = op "cmp"("ne", "w") %"v623", #0
          => br %"v624" ? "L617" : "L618" };
        cap_blk{ @"L617":
          %"v626" = %"v12" +p #16;
          %"v628" = %"v12" +p #32;
          %"v629" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk137";
          %"chk166" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v626";
          store.ptr [%"chk166" + 0] <- %"v629";
          %"chk167" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v631" : "w" = op "raw_load"("sw", int 0) %"chk167";
          %"v632" : "w" = "add" %"v631", #1;
          %"chk168" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk168" + 0] <- %"v632"
          => goto "L619" };
        cap_blk{ @"L618":
          %"v634" = %"v12" +p #16;
          %"chk169" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v634";
          store.ptr [%"chk169" + 0] <- #0
          => goto "L619" };
        cap_blk{ @"L619":
          %"v636" = %"v12" +p #32;
          %"chk170" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk20", %"v636";
          store.ptr [%"chk170" + 0] <- #0
          => goto "L605" };
        cap_blk{ @"L611":
          %"v641" = %"v12" +p #32;
          %"v642" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk137";
          %"chk172" : "a" = op "check"(int 0, int 1, "read", int 1) %"v642";
          %"v643" : "w" = op "raw_load"("sb", int 0) %"chk172";
          %"v644" : "w" = op "cmp"("ne", "w") %"v643", #0
          => br %"v644" ? "L637" : "L638" };
        cap_blk{ @"L637":
          %"v646" = %"v12" +p #16;
          %"v648" = %"v12" +p #32;
          %"v649" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk137";
          %"chk174" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v646";
          store.ptr [%"chk174" + 0] <- %"v649";
          %"chk175" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v651" : "w" = op "raw_load"("sw", int 0) %"chk175";
          %"v652" : "w" = "add" %"v651", #1;
          %"chk176" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk176" + 0] <- %"v652"
          => goto "L639" };
        cap_blk{ @"L638":
          %"chk177" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v657" : "w" = op "raw_load"("sw", int 0) %"chk177";
          %"v659" : "w" = op "cmp"("eq", "w") %"v657", %"v0"
          => br %"v659" ? "L653" : "L654" };
        cap_blk{ @"L653":
          => br %"pr.3" ? "L660" : "L662" };
        cap_blk{ @"L660":
          %"v664" : "p" = "copy" $"stderr";
          %"chk178" : "a" = op "check"(int 0, int 8, "read", int 8) %"v664";
          %"v665" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk178";
          %"v666" : "p" = "copy" $"__GI__libc_intl_domainname";
          %"v667" : "p" = "copy" $"glibc_getopt#str.149";
          call %"v668" : "p" = $"__GI___dcgettext"("p" %"v666", "p" %"v667", "w" #5);
          %"chk179" : "a" = op "check"(int 0, int 8, "read", int 8) %"v2";
          %"v671" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk179";
          call %"v673" : "w" = $"__fxprintf_nocancel"("p" %"v665", "p" %"v668", "p" %"v671", "w" %"v455")
          => goto "L662" };
        cap_blk{ @"L662":
          %"v675" = %"v12" +p #8;
          %"chk180" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"v675";
          store "w" [%"chk180" + 0] <- %"v455";
          %"chk181" : "a" = op "renew"(int 0, int 1, "read", int 1) %"chk19", %"pr.1";
          %"v682" : "w" = op "raw_load"("sb", int 0) %"chk181";
          %"v683" : "w" = op "cmp"("eq", "w") %"v682", #58
          => br %"v683" ? "L639" : "L678" };
        cap_blk{ @"L678":
          => goto "L639" };
        cap_blk{ @"L654":
          %"v685" = %"v12" +p #16;
          %"v688" : "w" = op "raw_load"("sw", int 0) %"chk177";
          %"v689" : "w" = "add" %"v688", #1;
          %"chk183" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk183" + 0] <- %"v689";
          %"v690" : "l" = op "ext"("sw") %"v688";
          %"v691" : "l" = "shl" %"v690", #3;
          %"v692" = %"v2" +p %"v691";
          %"chk184" : "a" = op "check"(int 0, int 8, "read", int 8) %"v692";
          %"v693" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk184";
          %"chk185" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v685";
          store.ptr [%"chk185" + 0] <- %"v693"
          => goto "L639" };
        cap_blk{ @"L639" [phi %"pr.7" : "w" = ("L637" => %"v455", "L654" => %"v455", "L678" => #63, "L662" => #58)]:
          %"v695" = %"v12" +p #32;
          %"chk186" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk20", %"v695";
          store.ptr [%"chk186" + 0] <- #0
          => goto "L605" };
        cap_blk{ @"L605" [phi %"pr.5" : "w" = ("L619" => %"v455", "L639" => %"pr.7", "L510" => %"v455")]:
          %"v696" : "w" = op "ext"("sb") %"pr.5"
          => ret %"v696" }
  ].
