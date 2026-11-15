(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition formatter_blocks_05 : list term :=
  [
        TApp "block" [TAtom "L1523"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1547"]; TAtom "w"; TAtom "copy"; TList [TApp "tmp" [TAtom "v1441"]]];
            TApp "let" [TApp "tmp" [TAtom "v1548"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "pr.70"]; TApp "tmp" [TAtom "v1547"]]];
            TApp "let" [TApp "tmp" [TAtom "v1551"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v1548"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 48]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1551"]]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1418"]; TAtom "L1552"; TAtom "L1554"]];
        TApp "block" [TAtom "L1552"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_putc"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 48]]]]];
          TApp "goto" [TAtom "L1554"]];
        TApp "block" [TAtom "L1554"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v1332"]; TAtom "L1557"; TAtom "L1558"]];
        TApp "block" [TAtom "L1557"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.88"]; TAtom "L1566"; TAtom "L1567"]];
        TApp "block" [TAtom "L1566"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1569"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.28"]; TApp "const" [TInt 10]]]];
          TApp "goto" [TAtom "L1567"]];
        TApp "block" [TAtom "L1567"; TList [TApp "phi" [TApp "tmp" [TAtom "v1571"]; TAtom "w"; TList [TApp "-" [TAtom "L1557"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L1566"; TApp "tmp" [TAtom "v1569"]]]]];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#group_number"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v1319"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.34"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v102"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.1"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v1571"]]]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1558"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_write"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.34"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1429"]]]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1443"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.18"]; TAtom "L1581"; TAtom "L1582"]];
        TApp "block" [TAtom "L1581"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_putc"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 45]]]];
            TApp "let" [TApp "tmp" [TAtom "v1587"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "pr.66"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TAtom "L1583"]];
        TApp "block" [TAtom "L1582"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.50"]; TAtom "L1588"; TAtom "L1589"]];
        TApp "block" [TAtom "L1588"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_putc"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 43]]]];
            TApp "let" [TApp "tmp" [TAtom "v1594"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "pr.66"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TAtom "L1583"]];
        TApp "block" [TAtom "L1589"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.44"]; TAtom "L1595"; TAtom "L1583"]];
        TApp "block" [TAtom "L1595"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_putc"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 32]]]];
            TApp "let" [TApp "tmp" [TAtom "v1601"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "pr.66"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TAtom "L1583"]];
        TApp "block" [TAtom "L1583"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.71"]; TAtom "w"; TList [TApp "-" [TAtom "L1581"; TApp "tmp" [TAtom "v1587"]]; TApp "-" [TAtom "L1588"; TApp "tmp" [TAtom "v1594"]]; TApp "-" [TAtom "L1595"; TApp "tmp" [TAtom "v1601"]]; TApp "-" [TAtom "L1589"; TApp "tmp" [TAtom "pr.66"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1606"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "pr.21"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1606"]; TAtom "L1607"; TAtom "L1608"]];
        TApp "block" [TAtom "L1607"; TList [];
          TList [];
          TApp "goto" [TAtom "L1608"]];
        TApp "block" [TAtom "L1608"; TList [TApp "phi" [TApp "tmp" [TAtom "v1611"]; TAtom "w"; TList [TApp "-" [TAtom "L1583"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L1607"; TApp "tmp" [TAtom "pr.40"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v1611"]; TAtom "L1612"; TAtom "L1613"]];
        TApp "block" [TAtom "L1612"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1615"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.28"]; TApp "const" [TInt 16]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1615"]; TAtom "L1613"; TAtom "L1616"]];
        TApp "block" [TAtom "L1616"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1619"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.28"]; TApp "const" [TInt 2]]]];
          TApp "goto" [TAtom "L1613"]];
        TApp "block" [TAtom "L1613"; TList [TApp "phi" [TApp "tmp" [TAtom "v1623"]; TAtom "w"; TList [TApp "-" [TAtom "L1608"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L1612"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L1616"; TApp "tmp" [TAtom "v1619"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v1623"]; TAtom "L1602"; TAtom "L1604"]];
        TApp "block" [TAtom "L1602"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_putc"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 48]]]];
            TApp "let" [TApp "tmp" [TAtom "v1626"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "pr.95"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_putc"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v1626"]]]];
            TApp "let" [TApp "tmp" [TAtom "v1628"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "pr.71"]; TApp "const" [TInt 2]]]];
          TApp "goto" [TAtom "L1604"]];
        TApp "block" [TAtom "L1604"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.74"]; TAtom "w"; TList [TApp "-" [TAtom "L1602"; TApp "tmp" [TAtom "v1628"]]; TApp "-" [TAtom "L1613"; TApp "tmp" [TAtom "pr.71"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v1418"]; TAtom "L1629"; TAtom "L1631"]];
        TApp "block" [TAtom "L1629"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1634"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "pr.74"]; TApp "const" [TInt 1]]]];
          TApp "goto" [TAtom "L1631"]];
        TApp "block" [TAtom "L1631"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.75"]; TAtom "w"; TList [TApp "-" [TAtom "L1629"; TApp "tmp" [TAtom "v1634"]]; TApp "-" [TAtom "L1604"; TApp "tmp" [TAtom "pr.74"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1637"]; TAtom "w"; TAtom "copy"; TList [TApp "tmp" [TAtom "v1441"]]];
            TApp "let" [TApp "tmp" [TAtom "v1638"]; TAtom "w"; TAtom "add"; TList [TApp "tmp" [TAtom "pr.107"]; TApp "tmp" [TAtom "v1637"]]];
            TApp "let" [TApp "tmp" [TAtom "v1639"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "pr.75"]; TApp "tmp" [TAtom "v1638"]]];
            TApp "let" [TApp "tmp" [TAtom "v1641"]; TAtom "w"; TAtom "copy"; TList [TApp "tmp" [TAtom "v1441"]]];
            TApp "let" [TApp "tmp" [TAtom "v1642"]; TAtom "l"; TApp "ext" [TAtom "uw"]; TList [TApp "tmp" [TAtom "v1641"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 48]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1642"]]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1418"]; TAtom "L1643"; TAtom "L1645"]];
        TApp "block" [TAtom "L1643"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_putc"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 48]]]]];
          TApp "goto" [TAtom "L1645"]];
        TApp "block" [TAtom "L1645"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v1332"]; TAtom "L1648"; TAtom "L1649"]];
        TApp "block" [TAtom "L1648"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.88"]; TAtom "L1657"; TAtom "L1658"]];
        TApp "block" [TAtom "L1657"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1660"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.28"]; TApp "const" [TInt 10]]]];
          TApp "goto" [TAtom "L1658"]];
        TApp "block" [TAtom "L1658"; TList [TApp "phi" [TApp "tmp" [TAtom "v1662"]; TAtom "w"; TList [TApp "-" [TAtom "L1648"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L1657"; TApp "tmp" [TAtom "v1660"]]]]];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#group_number"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v1319"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.34"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v102"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.1"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v1662"]]]]];
          TApp "goto" [TAtom "L1650"]];
        TApp "block" [TAtom "L1649"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_write"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.34"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1429"]]]]];
          TApp "goto" [TAtom "L1650"]];
        TApp "block" [TAtom "L1650"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1673"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v1639"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 32]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1673"]]]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1674"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1677"]; TAtom "p"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v4"]]];
            TApp "let" [TApp "tmp" [TAtom "v1682"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "v1677"]]];
            TApp "let" [TApp "tmp" [TAtom "v1684"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "l"]; TList [TApp "tmp" [TAtom "v1682"]; TApp "tmp" [TAtom "v55"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1684"]; TApp "poll" [TAtom "L1209"]; TAtom "L1679"]];
        TApp "block" [TAtom "L1679"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1688"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_vfprintf_internal#str.284"]]];
            TApp "let" [TApp "tmp" [TAtom "v1693"]; TAtom "w"; TApp "cmp" [TAtom "slt"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.82"]; TApp "const" [TInt 5]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1693"]; TAtom "L1695"; TAtom "L1690"]];
        TApp "block" [TAtom "L1690"; TList [];
          TList [];
          TApp "goto" [TAtom "L1695"]];
        TApp "block" [TAtom "L1696"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1701"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v6"]; TApp "const" [TInt 2]]];
            TApp "let" [TApp "tmp" [TAtom "v1702"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v1701"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1702"]; TAtom "L1697"; TAtom "L1699"]];
        TApp "block" [TAtom "L1697"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1707"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.16"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1707"]; TAtom "L1703"; TAtom "L1705"]];
        TApp "block" [TAtom "L1703"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v1710"]; TAtom "l"]; TApp "global" [TAtom "__GI_strlen"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v2"]]]];
            TApp "let" [TApp "tmp" [TAtom "v1711"]; TAtom "l"; TAtom "add"; TList [TApp "tmp" [TAtom "v1710"]; TApp "const" [TInt 1]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v1713"]; TAtom "w"]; TApp "global" [TAtom "__readonly_area"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v2"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1711"]]]]];
          TApp "goto" [TAtom "L1705"]];
        TApp "block" [TAtom "L1705"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.14"]; TAtom "w"; TList [TApp "-" [TAtom "L1703"; TApp "tmp" [TAtom "v1713"]]; TApp "-" [TAtom "L1697"; TApp "tmp" [TAtom "pr.16"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1724"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1724"]; TAtom "L1717"; TAtom "L1725"]];
        TApp "block" [TAtom "L1717"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1718"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_vfprintf_internal#str.285"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__GI___libc_fatal"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v1718"]]]]];
          TApp "goto" [TAtom "L1719"]];
        TApp "block" [TAtom "L1719"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1720"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_vfprintf_internal#str.286"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__GI___libc_fatal"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v1720"]]]]];
          TApp "goto" [TAtom "L1699"]];
        TApp "block" [TAtom "L1725"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1726"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 3]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1726"]; TApp "poll" [TAtom "L1719"]; TAtom "L1727"]];
        TApp "block" [TAtom "L1727"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1728"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 2]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1728"]; TAtom "L1699"; TAtom "L1729"]];
        TApp "block" [TAtom "L1729"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1730"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.14"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1730"]; TAtom "L1699"; TAtom "L1731"]];
        TApp "block" [TAtom "L1731"; TList [];
          TList [];
          TApp "goto" [TAtom "L1699"]];
        TApp "block" [TAtom "L1699"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.13"]; TAtom "w"; TList [TApp "-" [TAtom "L1731"; TApp "tmp" [TAtom "pr.14"]]; TApp "-" [TAtom "L1729"; TApp "tmp" [TAtom "pr.14"]]; TApp "-" [TAtom "L1719"; TApp "tmp" [TAtom "pr.14"]]; TApp "-" [TAtom "L1727"; TApp "tmp" [TAtom "pr.14"]]; TApp "-" [TAtom "L1696"; TApp "tmp" [TAtom "pr.16"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1734"]; TAtom "p"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v4"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v1737"]; TAtom "w"]; TApp "global" [TAtom "__printf_buffer_done"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "branch" [TApp "tmp" [TAtom "pr.62"]; TAtom "L1744"; TAtom "L1745"]];
        TApp "block" [TAtom "L1744"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1750"]; TAtom "l"; TApp "ext" [TAtom "uw"]; TList [TApp "tmp" [TAtom "v1737"]]];
            TApp "let" [TApp "tmp" [TAtom "chk148"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v1734"]]];
            TApp "raw_store" [TAtom "l"; TInt 0; TApp "tmp" [TAtom "v1750"]; TApp "tmp" [TAtom "chk148"]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1745"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.65"]; TAtom "L1751"; TAtom "L1752"]];
        TApp "block" [TAtom "L1751"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1757"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "v1737"]]];
            TApp "let" [TApp "tmp" [TAtom "chk149"]; TAtom "a"; TApp "check" [TInt 0; TInt 1; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v1734"]]];
            TApp "raw_store" [TAtom "b"; TInt 0; TApp "tmp" [TAtom "v1757"]; TApp "tmp" [TAtom "chk149"]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1752"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1762"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.60"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1762"]; TAtom "L1758"; TAtom "L1759"]];
        TApp "block" [TAtom "L1758"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk150"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v1734"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v1737"]; TApp "tmp" [TAtom "chk150"]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1759"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1767"]; TAtom "w"; TApp "ext" [TAtom "sh"]; TList [TApp "tmp" [TAtom "v1737"]]];
            TApp "let" [TApp "tmp" [TAtom "chk151"]; TAtom "a"; TApp "check" [TInt 0; TInt 2; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v1734"]]];
            TApp "raw_store" [TAtom "h"; TInt 0; TApp "tmp" [TAtom "v1767"]; TApp "tmp" [TAtom "chk151"]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1768"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.42"]; TAtom "L1769"; TAtom "L1770"]];
        TApp "block" [TAtom "L1769"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v1774"]; TAtom "p"]; TApp "global" [TAtom "__get_errname"]; TList [TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v19"]]]]];
          TApp "goto" [TAtom "L1771"]];
        TApp "block" [TAtom "L1770"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v1777"]; TAtom "p"]; TApp "global" [TAtom "__GI___strerror_r"]; TList [TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v19"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v13"]]; TApp "arg" [TAtom "l"; TApp "const" [TInt 1000]]]]];
          TApp "goto" [TAtom "L1771"]];
        TApp "block" [TAtom "L1771"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.37"]; TAtom "p"; TList [TApp "-" [TAtom "L1769"; TApp "tmp" [TAtom "v1774"]]; TApp "-" [TAtom "L1770"; TApp "tmp" [TAtom "v1777"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1782"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.37"]]];
            TApp "let" [TApp "tmp" [TAtom "v1784"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v1782"]; TApp "tmp" [TAtom "v55"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1784"]; TAtom "L1778"; TAtom "L1695"]];
        TApp "block" [TAtom "L1778"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1786"]; TAtom "w"; TApp "cmp" [TAtom "slt"; TAtom "w"]; TList [TApp "tmp" [TAtom "v19"]; TApp "const" [TInt 0]]];
            TApp "let" [TApp "tmp" [TAtom "v1788"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v19"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1786"]; TAtom "L1789"; TApp "poll" [TAtom "L1209"]]];
        TApp "block" [TAtom "L1789"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1794"]; TAtom "l"; TAtom "neg"; TList [TApp "tmp" [TAtom "v1788"]]]];
          TApp "goto" [TApp "poll" [TAtom "L1209"]]];
        TApp "block" [TAtom "L1796"; TList [];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "pr.62"]; TAtom "L1801"; TAtom "L1799"]];
        TApp "block" [TAtom "L1799"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1804"]; TAtom "w"; TAtom "sub"; TList [TApp "tmp" [TAtom "pr.66"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "v1809"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.47"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1809"]; TAtom "L1805"; TAtom "L1807"]];
        TApp "block" [TAtom "L1805"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1812"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v1804"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 32]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1812"]]]]];
          TApp "goto" [TAtom "L1807"]];
        TApp "block" [TAtom "L1807"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1815"]; TAtom "w"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v4"]]];
            TApp "let" [TApp "tmp" [TAtom "v1816"]; TAtom "w"; TApp "ext" [TAtom "ub"]; TList [TApp "tmp" [TAtom "v1815"]]];
            TApp "let" [TApp "tmp" [TAtom "v1817"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "v1816"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_putc"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v1817"]]]]];
          TApp "branch" [TApp "tmp" [TAtom "pr.47"]; TAtom "L1818"; TAtom "L1150"]];
        TApp "block" [TAtom "L1818"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1824"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v1804"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 32]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1824"]]]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1825"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1828"]; TAtom "p"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v4"]]]];
          TApp "goto" [TAtom "L1695"]];
        TApp "block" [TAtom "L1695"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.84"]; TAtom "w"; TList [TApp "-" [TAtom "L1825"; TApp "tmp" [TAtom "pr.82"]]; TApp "-" [TAtom "L1690"; TApp "tmp" [TAtom "pr.82"]]; TApp "-" [TAtom "L1679"; TApp "const" [TInt 5]]; TApp "-" [TAtom "L1771"; TApp "tmp" [TAtom "pr.82"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.63"]; TAtom "w"; TList [TApp "-" [TAtom "L1825"; TApp "tmp" [TAtom "pr.62"]]; TApp "-" [TAtom "L1690"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L1679"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L1771"; TApp "const" [TInt 0]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.36"]; TAtom "p"; TList [TApp "-" [TAtom "L1825"; TApp "tmp" [TAtom "v1828"]]; TApp "-" [TAtom "L1690"; TApp "tmp" [TAtom "v1688"]]; TApp "-" [TAtom "L1679"; TApp "tmp" [TAtom "v1688"]]; TApp "-" [TAtom "L1771"; TApp "tmp" [TAtom "pr.37"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1833"]; TAtom "l"; TAtom "ptoi"; TList [TApp "tmp" [TAtom "pr.36"]]];
            TApp "let" [TApp "tmp" [TAtom "v1835"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v1833"]; TApp "tmp" [TAtom "v55"]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1835"]; TAtom "L1829"; TAtom "L1830"]];
        TApp "block" [TAtom "L1829"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1841"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.84"]; TApp "const" [TInt 4294967295]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1841"]; TAtom "L1843"; TAtom "L1842"]];
        TApp "block" [TAtom "L1842"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1849"]; TAtom "w"; TApp "cmp" [TAtom "sge"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.84"]; TApp "const" [TInt 6]]]];
          TApp "goto" [TAtom "L1843"]];
        TApp "block" [TAtom "L1843"; TList [TApp "phi" [TApp "tmp" [TAtom "v1851"]; TAtom "w"; TList [TApp "-" [TAtom "L1829"; TApp "const" [TInt 1]]; TApp "-" [TAtom "L1842"; TApp "tmp" [TAtom "v1849"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v1851"]; TAtom "L1836"; TAtom "L1837"]];
        TApp "block" [TAtom "L1836"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1852"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_vfprintf_internal#null"]]]];
          TApp "goto" [TAtom "L1831"]];
        TApp "block" [TAtom "L1837"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1857"]; TAtom "p"; TAtom "copy"; TList [TApp "global" [TAtom "glibc_vfprintf_internal#str.289"]]]];
          TApp "goto" [TAtom "L1831"]];
        TApp "block" [TAtom "L1830"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1862"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.63"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1862"]; TAtom "L1863"; TAtom "L1864"]];
        TApp "block" [TAtom "L1863"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1865"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "pr.97"]]];
            TApp "let" [TApp "tmp" [TAtom "v1866"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "v1865"]; TApp "const" [TInt 83]]]];
          TApp "goto" [TAtom "L1864"]];
        TApp "block" [TAtom "L1864"; TList [TApp "phi" [TApp "tmp" [TAtom "v1868"]; TAtom "w"; TList [TApp "-" [TAtom "L1830"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L1863"; TApp "tmp" [TAtom "v1866"]]]]];
          TList [];
          TApp "branch" [TApp "tmp" [TAtom "v1868"]; TAtom "L1858"; TAtom "L1859"]];
        TApp "block" [TAtom "L1858"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1874"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.84"]; TApp "const" [TInt 4294967295]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1874"]; TAtom "L1869"; TAtom "L1870"]];
        TApp "block" [TAtom "L1869"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1877"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "pr.84"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v1878"]; TAtom "l"]; TApp "global" [TAtom "__GI___strnlen"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.36"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1877"]]]]];
          TApp "goto" [TAtom "L1871"]];
        TApp "block" [TAtom "L1870"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v1880"]; TAtom "l"]; TApp "global" [TAtom "__GI_strlen"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.36"]]]]];
          TApp "goto" [TAtom "L1871"]];
        TApp "block" [TAtom "L1871"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.111"]; TAtom "l"; TList [TApp "-" [TAtom "L1869"; TApp "tmp" [TAtom "v1878"]]; TApp "-" [TAtom "L1870"; TApp "tmp" [TAtom "v1880"]]]]];
          TList [];
          TApp "goto" [TAtom "L1831"]];
        TApp "block" [TAtom "L1859"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1886"]; TAtom "w"; TApp "cmp" [TAtom "ne"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.47"]; TApp "const" [TInt 0]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#outstring_converted_wide_string"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.36"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "pr.84"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "pr.66"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v1886"]]]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1831"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.109"]; TAtom "l"; TList [TApp "-" [TAtom "L1836"; TApp "const" [TInt 6]]; TApp "-" [TAtom "L1837"; TApp "const" [TInt 0]]; TApp "-" [TAtom "L1871"; TApp "tmp" [TAtom "pr.111"]]]]; TApp "phi" [TApp "tmp" [TAtom "pr.38"]; TAtom "p"; TList [TApp "-" [TAtom "L1836"; TApp "tmp" [TAtom "v1852"]]; TApp "-" [TAtom "L1837"; TApp "tmp" [TAtom "v1857"]]; TApp "-" [TAtom "L1871"; TApp "tmp" [TAtom "pr.36"]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1892"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "pr.66"]]];
            TApp "let" [TApp "tmp" [TAtom "v1893"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "v1892"]; TApp "tmp" [TAtom "pr.109"]]];
            TApp "let" [TApp "tmp" [TAtom "v1894"]; TAtom "w"; TApp "cmp" [TAtom "slt"; TAtom "w"]; TList [TApp "tmp" [TAtom "v1893"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1894"]; TAtom "L1887"; TAtom "L1889"]];
        TApp "block" [TAtom "L1887"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_write"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.38"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "pr.109"]]]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1889"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1903"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.47"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1903"]; TAtom "L1899"; TAtom "L1901"]];
        TApp "block" [TAtom "L1899"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1905"]; TAtom "w"; TAtom "copy"; TList [TApp "tmp" [TAtom "v1893"]]];
            TApp "let" [TApp "tmp" [TAtom "v1906"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v1905"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 32]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1906"]]]]];
          TApp "goto" [TAtom "L1901"]];
        TApp "block" [TAtom "L1901"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_write"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "pr.38"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "pr.109"]]]]];
          TApp "branch" [TApp "tmp" [TAtom "pr.47"]; TAtom "L1910"; TAtom "L1150"]];
        TApp "block" [TAtom "L1910"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1915"]; TAtom "w"; TAtom "copy"; TList [TApp "tmp" [TAtom "v1893"]]];
            TApp "let" [TApp "tmp" [TAtom "v1916"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v1915"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 32]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1916"]]]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1801"; TList [];
          TList [
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v1920"]; TAtom "p"]; TApp "global" [TAtom "__GI_memset"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v1918"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 0]]; TApp "arg" [TAtom "l"; TApp "const" [TInt 8]]]];
            TApp "let" [TApp "tmp" [TAtom "v1922"]; TAtom "w"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v4"]]];
            TApp "call" [TApp "result" [TApp "tmp" [TAtom "v1923"]; TAtom "l"]; TApp "global" [TAtom "__wcrtomb"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v1917"]]; TApp "arg" [TAtom "w"; TApp "tmp" [TAtom "v1922"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v1918"]]]];
            TApp "let" [TApp "tmp" [TAtom "v1930"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "l"]; TList [TApp "tmp" [TAtom "v1923"]; TApp "const" [TInt 18446744073709551615]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1930"]; TAtom "L1924"; TAtom "L1926"]];
        TApp "block" [TAtom "L1924"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_mark_failed"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]]]];
          TApp "goto" [TAtom "L516"]];
        TApp "block" [TAtom "L1926"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1935"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "pr.66"]]];
            TApp "let" [TApp "tmp" [TAtom "v1936"]; TAtom "l"; TAtom "sub"; TList [TApp "tmp" [TAtom "v1935"]; TApp "tmp" [TAtom "v1923"]]];
            TApp "let" [TApp "tmp" [TAtom "v1941"]; TAtom "w"; TApp "cmp" [TAtom "eq"; TAtom "w"]; TList [TApp "tmp" [TAtom "pr.47"]; TApp "const" [TInt 0]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1941"]; TAtom "L1937"; TAtom "L1939"]];
        TApp "block" [TAtom "L1937"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1943"]; TAtom "w"; TAtom "copy"; TList [TApp "tmp" [TAtom "v1936"]]];
            TApp "let" [TApp "tmp" [TAtom "v1944"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v1943"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 32]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1944"]]]]];
          TApp "goto" [TAtom "L1939"]];
        TApp "block" [TAtom "L1939"; TList [];
          TList [
            TApp "call" [TAtom "void"; TApp "global" [TAtom "__printf_buffer_write"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v1917"]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1923"]]]]];
          TApp "branch" [TApp "tmp" [TAtom "pr.47"]; TAtom "L1947"; TAtom "L1150"]];
        TApp "block" [TAtom "L1947"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1952"]; TAtom "w"; TAtom "copy"; TList [TApp "tmp" [TAtom "v1936"]]];
            TApp "let" [TApp "tmp" [TAtom "v1953"]; TAtom "l"; TApp "ext" [TAtom "sw"]; TList [TApp "tmp" [TAtom "v1952"]]];
            TApp "call" [TAtom "void"; TApp "global" [TAtom "glibc_vfprintf_internal#__printf_buffer_pad"]; TList [TApp "arg" [TAtom "p"; TApp "tmp" [TAtom "v0"]]; TApp "arg" [TAtom "w"; TApp "const" [TInt 32]]; TApp "arg" [TAtom "l"; TApp "tmp" [TAtom "v1953"]]]]];
          TApp "goto" [TAtom "L1150"]];
        TApp "block" [TAtom "L1955"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v1960"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v6"]; TApp "const" [TInt 1]]]];
          TApp "branch" [TApp "tmp" [TAtom "v1960"]; TAtom "L1958"; TAtom "L1957"]];
        TApp "block" [TAtom "L1957"; TList [];
          TList [];
          TApp "goto" [TAtom "L1958"]];
        TApp "block" [TAtom "L1958"; TList [TApp "phi" [TApp "tmp" [TAtom "pr.58"]; TAtom "w"; TList [TApp "-" [TAtom "L1957"; TApp "tmp" [TAtom "pr.57"]]; TApp "-" [TAtom "L1955"; TApp "const" [TInt 0]]]]];
          TList [
            TApp "let" [TApp "tmp" [TAtom "chk152"]; TAtom "a"; TApp "check" [TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v1964"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk152"]];
            TApp "flight" [TApp "tmp" [TAtom "v1965"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v1964"]]; TApp "const" [TInt 4]]; TApp "lower" [TApp "tmp" [TAtom "v1964"]]];
            TApp "let" [TApp "tmp" [TAtom "chk153"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk152"]; TApp "tmp" [TAtom "v1965"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk153"]];
            TApp "flight" [TApp "tmp" [TAtom "v1966"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v1964"]]; TApp "const" [TInt 8]]; TApp "lower" [TApp "tmp" [TAtom "v1964"]]];
            TApp "let" [TApp "tmp" [TAtom "chk154"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk152"]; TApp "tmp" [TAtom "v1966"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk154"]];
            TApp "flight" [TApp "tmp" [TAtom "v1967"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v1964"]]; TApp "const" [TInt 12]]; TApp "lower" [TApp "tmp" [TAtom "v1964"]]];
            TApp "let" [TApp "tmp" [TAtom "chk155"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk152"]; TApp "tmp" [TAtom "v1967"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk155"]];
            TApp "flight" [TApp "tmp" [TAtom "v1968"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v1964"]]; TApp "const" [TInt 16]]; TApp "lower" [TApp "tmp" [TAtom "v1964"]]];
            TApp "let" [TApp "tmp" [TAtom "chk156"]; TAtom "a"; TApp "half_check" [TAtom "upper"; TInt 0; TInt 4; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "chk152"]; TApp "tmp" [TAtom "v1968"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "const" [TInt 0]; TApp "tmp" [TAtom "chk156"]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "pr.82"]; TApp "tmp" [TAtom "chk152"]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "pr.66"]; TApp "tmp" [TAtom "chk153"]];
            TApp "let" [TApp "tmp" [TAtom "v1973"]; TAtom "w"; TApp "ext" [TAtom "sb"]; TList [TApp "tmp" [TAtom "pr.97"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v1973"]; TApp "tmp" [TAtom "chk154"]];
            TApp "let" [TApp "tmp" [TAtom "v1976"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v1977"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v1976"]; TApp "const" [TInt 4294967294]]];
            TApp "let" [TApp "tmp" [TAtom "v1978"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "pr.58"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "v1979"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v1977"]; TApp "tmp" [TAtom "v1978"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v1979"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v1984"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v1985"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v1984"]; TApp "const" [TInt 4294967293]]];
            TApp "let" [TApp "tmp" [TAtom "v1986"]; TAtom "w"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.60"]; TApp "const" [TInt 1]]];
            TApp "let" [TApp "tmp" [TAtom "v1987"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v1986"]; TApp "const" [TInt 2]]];
            TApp "let" [TApp "tmp" [TAtom "v1988"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v1985"]; TApp "tmp" [TAtom "v1987"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v1988"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v1993"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v1994"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v1993"]; TApp "const" [TInt 4294967291]]];
            TApp "let" [TApp "tmp" [TAtom "v1995"]; TAtom "w"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.62"]; TApp "const" [TInt 2]]];
            TApp "let" [TApp "tmp" [TAtom "v1996"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v1995"]; TApp "const" [TInt 4]]];
            TApp "let" [TApp "tmp" [TAtom "v1997"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v1994"]; TApp "tmp" [TAtom "v1996"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v1997"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v2002"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2003"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2002"]; TApp "const" [TInt 4294967287]]];
            TApp "let" [TApp "tmp" [TAtom "v2004"]; TAtom "w"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.42"]; TApp "const" [TInt 3]]];
            TApp "let" [TApp "tmp" [TAtom "v2005"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2004"]; TApp "const" [TInt 8]]];
            TApp "let" [TApp "tmp" [TAtom "v2006"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v2003"]; TApp "tmp" [TAtom "v2005"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2006"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v2011"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2012"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2011"]; TApp "const" [TInt 4294967279]]];
            TApp "let" [TApp "tmp" [TAtom "v2013"]; TAtom "w"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.46"]; TApp "const" [TInt 4]]];
            TApp "let" [TApp "tmp" [TAtom "v2014"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2013"]; TApp "const" [TInt 16]]];
            TApp "let" [TApp "tmp" [TAtom "v2015"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v2012"]; TApp "tmp" [TAtom "v2014"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2015"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v2020"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2021"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2020"]; TApp "const" [TInt 4294967263]]];
            TApp "let" [TApp "tmp" [TAtom "v2022"]; TAtom "w"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.47"]; TApp "const" [TInt 5]]];
            TApp "let" [TApp "tmp" [TAtom "v2023"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2022"]; TApp "const" [TInt 32]]];
            TApp "let" [TApp "tmp" [TAtom "v2024"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v2021"]; TApp "tmp" [TAtom "v2023"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2024"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v2029"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2030"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2029"]; TApp "const" [TInt 4294967231]]];
            TApp "let" [TApp "tmp" [TAtom "v2031"]; TAtom "w"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.52"]; TApp "const" [TInt 6]]];
            TApp "let" [TApp "tmp" [TAtom "v2032"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2031"]; TApp "const" [TInt 64]]];
            TApp "let" [TApp "tmp" [TAtom "v2033"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v2030"]; TApp "tmp" [TAtom "v2032"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2033"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v2038"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2039"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2038"]; TApp "const" [TInt 4294967167]]];
            TApp "let" [TApp "tmp" [TAtom "v2040"]; TAtom "w"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.55"]; TApp "const" [TInt 7]]];
            TApp "let" [TApp "tmp" [TAtom "v2041"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2040"]; TApp "const" [TInt 128]]];
            TApp "let" [TApp "tmp" [TAtom "v2042"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v2039"]; TApp "tmp" [TAtom "v2041"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2042"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v2046"]; TAtom "w"; TApp "ext" [TAtom "ub"]; TList [TApp "tmp" [TAtom "pr.92"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2046"]; TApp "tmp" [TAtom "chk156"]];
            TApp "let" [TApp "tmp" [TAtom "v2048"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2049"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2048"]; TApp "const" [TInt 4294967039]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2049"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v2057"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2058"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2057"]; TApp "const" [TInt 4294965247]]];
            TApp "let" [TApp "tmp" [TAtom "v2059"]; TAtom "w"; TAtom "shl"; TList [TApp "tmp" [TAtom "pr.88"]; TApp "const" [TInt 11]]];
            TApp "let" [TApp "tmp" [TAtom "v2060"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2059"]; TApp "const" [TInt 2048]]];
            TApp "let" [TApp "tmp" [TAtom "v2061"]; TAtom "w"; TAtom "or"; TList [TApp "tmp" [TAtom "v2058"]; TApp "tmp" [TAtom "v2060"]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2061"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v2066"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2067"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2066"]; TApp "const" [TInt 4294966271]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2067"]; TApp "tmp" [TAtom "chk155"]];
            TApp "let" [TApp "tmp" [TAtom "v2074"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2075"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2074"]; TApp "const" [TInt 4294963199]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2075"]; TApp "tmp" [TAtom "chk155"]];
            TApp "flight" [TApp "tmp" [TAtom "v2084"]; TAtom "add"; TList [TApp "address" [TApp "tmp" [TAtom "v1964"]]; TApp "const" [TInt 12]]; TApp "lower" [TApp "tmp" [TAtom "v1964"]]];
            TApp "let" [TApp "tmp" [TAtom "v2085"]; TAtom "w"; TApp "raw_load" [TAtom "uw"; TInt 0]; TList [TApp "tmp" [TAtom "chk155"]]];
            TApp "let" [TApp "tmp" [TAtom "v2086"]; TAtom "w"; TAtom "and"; TList [TApp "tmp" [TAtom "v2085"]; TApp "const" [TInt 4294963199]]];
            TApp "raw_store" [TAtom "w"; TInt 0; TApp "tmp" [TAtom "v2086"]; TApp "tmp" [TAtom "chk155"]]];
          TApp "branch" [TApp "tmp" [TAtom "pr.58"]; TAtom "L2092"; TAtom "L2093"]];
        TApp "block" [TAtom "L2092"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v2097"]; TAtom "x"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v4"]]];
            TApp "let" [TApp "tmp" [TAtom "chk187"]; TAtom "a"; TApp "check" [TInt 0; TInt 10; TAtom "write"; TInt 8]; TList [TApp "tmp" [TAtom "v85"]]];
            TApp "raw_store" [TAtom "x"; TInt 0; TApp "tmp" [TAtom "v2097"]; TApp "tmp" [TAtom "chk187"]]];
          TApp "goto" [TAtom "L2083"]];
        TApp "block" [TAtom "L2093"; TList [];
          TList [
            TApp "let" [TApp "tmp" [TAtom "v2099"]; TAtom "d"; TAtom "va_arg"; TList [TApp "tmp" [TAtom "v4"]]];
            TApp "let" [TApp "tmp" [TAtom "chk188"]; TAtom "a"; TApp "check" [TInt 0; TInt 8; TAtom "write"; TInt 1]; TList [TApp "tmp" [TAtom "v85"]]];
            TApp "raw_store" [TAtom "d"; TInt 0; TApp "tmp" [TAtom "v2099"]; TApp "tmp" [TAtom "chk188"]]];
          TApp "goto" [TAtom "L2083"]]
  ].
