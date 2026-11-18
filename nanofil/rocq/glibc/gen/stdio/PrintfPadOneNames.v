(** These notations name the temporaries of compiled functions after the C expression each one holds.
    A proof imports the module of its own function, and then writes and reads a temporary by that name.
    Every name is one token between single guillemets, so it cannot be read as a term about proof variables.
    A name with @ and a label belongs to a later temporary that holds the same expression.
    These names are notations for the temporaries' own names; they add no premise.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String.
From Nanofil Require Import Term.
Open Scope string_scope.

Module PrintfPadOneNames.

Module fn___printf_buffer_pad_1.
Notation "'‹buf›'" := (TAtom "v0").
Notation "'‹ch›'" := (TAtom "v2").
Notation "'‹count›'" := (TAtom "v4").
Notation "'‹count@L15›'" := (TAtom "pr.1").
Notation "'‹to_fill›'" := (TAtom "pr.2").
Notation "'‹buf+32›'" := (TAtom "iw_1.v3").
Notation "'‹chk(buf+32)›'" := (TAtom "chk0").
Notation "'‹buf->mode›'" := (TAtom "iw_1.v4").
Notation "'‹buf->mode==0›'" := (TAtom "iw_1.v5").
Notation "'‹buf+8›'" := (TAtom "v22").
Notation "'‹chk(buf+8)›'" := (TAtom "chk1").
Notation "'‹buf->write_ptr›'" := (TAtom "v23").
Notation "'‹buf+16›'" := (TAtom "v25").
Notation "'‹chk(buf+16)›'" := (TAtom "chk2").
Notation "'‹buf->write_end›'" := (TAtom "v26").
Notation "'‹addr(buf->write_ptr)›'" := (TAtom "v27").
Notation "'‹addr(buf->write_end)›'" := (TAtom "v28").
Notation "'‹addr(buf->write_ptr)==addr(buf->write_end)›'" := (TAtom "v29").
Notation "'‹__printf_buffer_flush()›'" := (TAtom "v33").
Notation "'‹buf+8@L20›'" := (TAtom "v43").
Notation "'‹chk(buf+8)@L20›'" := (TAtom "chk3").
Notation "'‹buf->write_ptr@L20›'" := (TAtom "v44").
Notation "'‹buf+16@L20›'" := (TAtom "v46").
Notation "'‹chk(buf+16)@L20›'" := (TAtom "chk4").
Notation "'‹buf->write_end@L20›'" := (TAtom "v47").
Notation "'‹addr(buf->write_ptr)@L20›'" := (TAtom "v48").
Notation "'‹addr(buf->write_end)@L20›'" := (TAtom "v49").
Notation "'‹addr(buf->write_ptr)!=addr(buf->write_end)›'" := (TAtom "v50").
Notation "'‹&glibc_printf_buffer_pad_1#str.41›'" := (TAtom "v51").
Notation "'‹&glibc_printf_buffer_pad_1#str.42›'" := (TAtom "v52").
Notation "'‹&glibc_printf_buffer_pad_1#str.43›'" := (TAtom "v53").
Notation "'‹buf+16@L41›'" := (TAtom "v56").
Notation "'‹chk(buf+16)@L41›'" := (TAtom "chk5").
Notation "'‹buf->write_end@L41›'" := (TAtom "v57").
Notation "'‹buf+8@L41›'" := (TAtom "v59").
Notation "'‹chk(buf+8)@L41›'" := (TAtom "chk6").
Notation "'‹buf->write_ptr@L41›'" := (TAtom "v60").
Notation "'‹addr(buf->write_end)@L41›'" := (TAtom "v61").
Notation "'‹addr(buf->write_ptr)@L41›'" := (TAtom "v62").
Notation "'‹to_fill@L41›'" := (TAtom "v63").
Notation "'‹to_fill>ucount›'" := (TAtom "v69").
Notation "'‹buf+8@L66›'" := (TAtom "v72").
Notation "'‹buf->write_ptr@L66›'" := (TAtom "v73").
Notation "'‹ch@L66›'" := (TAtom "v74").
Notation "'‹__GI_memset()›'" := (TAtom "v76").
Notation "'‹chk(buf+8)@L66›'" := (TAtom "chk8").
Notation "'‹buf->write_ptr@L66.2›'" := (TAtom "v79").
Notation "'‹chk(buf+8)@L66.2›'" := (TAtom "chk9").
Notation "'‹count@L66›'" := (TAtom "v84").
Notation "'‹count>u0›'" := (TAtom "v86").
End fn___printf_buffer_pad_1.

End PrintfPadOneNames.
