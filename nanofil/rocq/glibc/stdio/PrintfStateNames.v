(** These notations name the temporaries of compiled functions after the C expression each one holds.
    A proof imports the module of its own function, and then writes and reads a temporary by that name.
    Every name is one token between single guillemets, so it cannot be read as a term about proof variables.
    A name with @ and a label belongs to a later temporary that holds the same expression.
    These names are notations for the temporaries' own names; they add no premise.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String.
From Nanofil Require Import Term.
Open Scope string_scope.

Module PrintfStateNames.

Module fn___GI___pthread_setcancelstate.
Notation "'‹state›'" := (TAtom "v0").
Notation "'‹oldstate›'" := (TAtom "v2").
Notation "'‹oldval›'" := (TAtom "pr.1").
Notation "'‹newval›'" := (TAtom "v38").
Notation "'‹oldval@L71›'" := (TAtom "pr.2").
Notation "'‹oldval@iw_2.L12›'" := (TAtom "iw_2.pr.1").
Notation "'‹oldval@iw_2.L38›'" := (TAtom "iw_2.pr.2").
Notation "'‹state<0›'" := (TAtom "v9").
Notation "'‹state>1›'" := (TAtom "v13").
Notation "'‹self›'" := (TAtom "v17").
Notation "'‹self+792›'" := (TAtom "v20").
Notation "'‹chk(self+792)›'" := (TAtom "chk0").
Notation "'‹oldval@L7›'" := (TAtom "v21").
Notation "'‹state==1›'" := (TAtom "v30").
Notation "'‹addr(oldstate)›'" := (TAtom "v43").
Notation "'‹chk(oldstate)›'" := (TAtom "chk1").
Notation "'‹oldval==newval›'" := (TAtom "v59").
Notation "'‹self+792@L56›'" := (TAtom "v65").
Notation "'‹chk(self+792)@L56›'" := (TAtom "chk2").
Notation "'‹oldval@L56›'" := (TAtom "v68").
Notation "'‹oldval==oldval›'" := (TAtom "v69").
Notation "'‹self@L72›'" := (TAtom "iw_2.v3").
Notation "'‹self+1608›'" := (TAtom "iw_2.v5").
Notation "'‹chk(self+1608)›'" := (TAtom "chk3").
Notation "'‹self+792@L72›'" := (TAtom "iw_2.v9").
Notation "'‹chk(self+792)@L72›'" := (TAtom "chk4").
Notation "'‹oldval@L72›'" := (TAtom "iw_2.v10").
Notation "'‹newval@iw_2.L12›'" := (TAtom "iw_2.v19").
Notation "'‹newval@iw_2.L12.2›'" := (TAtom "iw_2.v23").
Notation "'‹oldval==newval@iw_2.L12›'" := (TAtom "iw_2.v29").
Notation "'‹self+792@iw_2.L13›'" := (TAtom "iw_2.v32").
Notation "'‹chk(self+792)@iw_2.L13›'" := (TAtom "chk5").
Notation "'‹oldval@iw_2.L13›'" := (TAtom "iw_2.v35").
Notation "'‹oldval==oldval@iw_2.L13›'" := (TAtom "iw_2.v36").
Notation "'‹oldval!=oldval›'" := (TAtom "iw_2.v39").
Notation "'‹self+784›'" := (TAtom "iw_2.v41").
Notation "'‹chk(self+784)›'" := (TAtom "chk6").
Notation "'‹self->cleanup_jmp_buf›'" := (TAtom "iw_2.v42").
End fn___GI___pthread_setcancelstate.

Module fn___printf_buffer_done.
Notation "'‹buf›'" := (TAtom "v0").
Notation "'‹buf+32›'" := (TAtom "iw_1.v3").
Notation "'‹chk(buf+32)›'" := (TAtom "chk0").
Notation "'‹buf->mode›'" := (TAtom "iw_1.v4").
Notation "'‹buf->mode==0›'" := (TAtom "iw_1.v5").
Notation "'‹buf+8›'" := (TAtom "v12").
Notation "'‹chk(buf+8)›'" := (TAtom "chk1").
Notation "'‹buf->write_ptr›'" := (TAtom "v13").
Notation "'‹chk(buf)›'" := (TAtom "chk2").
Notation "'‹buf->write_base›'" := (TAtom "v15").
Notation "'‹addr(buf->write_ptr)›'" := (TAtom "v16").
Notation "'‹addr(buf->write_base)›'" := (TAtom "v17").
Notation "'‹written_current›'" := (TAtom "v18").
Notation "'‹buf+24›'" := (TAtom "v24").
Notation "'‹buf->written›'" := (TAtom "v25").
Notation "'‹written_total›'" := (TAtom "v27").
Notation "'‹written_total<ubuf->written›'" := (TAtom "v28").
Notation "'‹&__libc_errno›'" := (TAtom "v37").
Notation "'‹chk(&__libc_errno)›'" := (TAtom "chk4").
Notation "'‹written_total@L21›'" := (TAtom "v40").
End fn___printf_buffer_done.

End PrintfStateNames.
