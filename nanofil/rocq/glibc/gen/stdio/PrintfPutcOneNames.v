(** These notations name the temporaries of compiled functions after the C expression each one holds.
    A proof imports the module of its own function, and then writes and reads a temporary by that name.
    Every name is one token between single guillemets, so it cannot be read as a term about proof variables.
    A name with @ and a label belongs to a later temporary that holds the same expression.
    These names are notations for the temporaries' own names; they add no premise.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String.
From Nanofil Require Import Term.
Open Scope string_scope.

Module PrintfPutcOneNames.

Module fn___printf_buffer_putc_1.
Notation "'‹buf›'" := (TAtom "v0").
Notation "'‹ch›'" := (TAtom "v2").
Notation "'‹buf+32›'" := (TAtom "iw_1.v3").
Notation "'‹chk(buf+32)›'" := (TAtom "chk0").
Notation "'‹buf->mode›'" := (TAtom "iw_1.v4").
Notation "'‹buf->mode==0›'" := (TAtom "iw_1.v5").
Notation "'‹__printf_buffer_flush()›'" := (TAtom "v15").
Notation "'‹buf+8›'" := (TAtom "v25").
Notation "'‹chk(buf+8)›'" := (TAtom "chk1").
Notation "'‹buf->write_ptr›'" := (TAtom "v26").
Notation "'‹buf+16›'" := (TAtom "v28").
Notation "'‹chk(buf+16)›'" := (TAtom "chk2").
Notation "'‹buf->write_end›'" := (TAtom "v29").
Notation "'‹addr(buf->write_ptr)›'" := (TAtom "v30").
Notation "'‹addr(buf->write_end)›'" := (TAtom "v31").
Notation "'‹addr(buf->write_ptr)<uaddr(buf->write_end)›'" := (TAtom "v32").
Notation "'‹&glibc_printf_buffer_putc_1#str.39›'" := (TAtom "v33").
Notation "'‹&glibc_printf_buffer_putc_1#str.40›'" := (TAtom "v34").
Notation "'‹&glibc_printf_buffer_putc_1#str.41›'" := (TAtom "v35").
Notation "'‹buf+8@L23›'" := (TAtom "v37").
Notation "'‹chk(buf+8)@L23›'" := (TAtom "chk3").
Notation "'‹buf->write_ptr@L23›'" := (TAtom "v38").
Notation "'‹buf->write_ptr+1›'" := (TAtom "v39").
Notation "'‹chk(buf+8)@L23.2›'" := (TAtom "chk4").
Notation "'‹ch@L23›'" := (TAtom "v40").
Notation "'‹chk(buf->write_ptr)›'" := (TAtom "chk5").
End fn___printf_buffer_putc_1.

End PrintfPutcOneNames.
