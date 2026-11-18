(** These notations name the temporaries of compiled functions after the C expression each one holds.
    A proof imports the module of its own function, and then writes and reads a temporary by that name.
    Every name is one token between single guillemets, so it cannot be read as a term about proof variables.
    A name with @ and a label belongs to a later temporary that holds the same expression.
    These names are notations for the temporaries' own names; they add no premise.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String.
From Nanofil Require Import Term.
Open Scope string_scope.

Module PrintfBufferIoNames.

Module fn___printf_buffer_write.
Notation "'‹buf›'" := (TAtom "v0").
Notation "'‹s›'" := (TAtom "v2").
Notation "'‹count›'" := (TAtom "v4").
Notation "'‹count@L15›'" := (TAtom "pr.2").
Notation "'‹s@L15›'" := (TAtom "pr.1").
Notation "'‹to_copy›'" := (TAtom "pr.3").
Notation "'‹buf+32›'" := (TAtom "iw_1.v3").
Notation "'‹chk(buf+32)›'" := (TAtom "chk0").
Notation "'‹buf->mode›'" := (TAtom "iw_1.v4").
Notation "'‹buf->mode==0›'" := (TAtom "iw_1.v5").
Notation "'‹count>u0›'" := (TAtom "v19").
Notation "'‹buf+8›'" := (TAtom "v24").
Notation "'‹chk(buf+8)›'" := (TAtom "chk1").
Notation "'‹buf->write_ptr›'" := (TAtom "v25").
Notation "'‹buf+16›'" := (TAtom "v27").
Notation "'‹chk(buf+16)›'" := (TAtom "chk2").
Notation "'‹buf->write_end›'" := (TAtom "v28").
Notation "'‹addr(buf->write_ptr)›'" := (TAtom "v29").
Notation "'‹addr(buf->write_end)›'" := (TAtom "v30").
Notation "'‹addr(buf->write_ptr)==addr(buf->write_end)›'" := (TAtom "v31").
Notation "'‹__printf_buffer_flush()›'" := (TAtom "v35").
Notation "'‹buf+8@L22›'" := (TAtom "v45").
Notation "'‹chk(buf+8)@L22›'" := (TAtom "chk3").
Notation "'‹buf->write_ptr@L22›'" := (TAtom "v46").
Notation "'‹buf+16@L22›'" := (TAtom "v48").
Notation "'‹chk(buf+16)@L22›'" := (TAtom "chk4").
Notation "'‹buf->write_end@L22›'" := (TAtom "v49").
Notation "'‹addr(buf->write_ptr)@L22›'" := (TAtom "v50").
Notation "'‹addr(buf->write_end)@L22›'" := (TAtom "v51").
Notation "'‹addr(buf->write_ptr)!=addr(buf->write_end)›'" := (TAtom "v52").
Notation "'‹&glibc_printf_buffer_write#str.41›'" := (TAtom "v53").
Notation "'‹&glibc_printf_buffer_write#str.42›'" := (TAtom "v54").
Notation "'‹&glibc_printf_buffer_write#str.43›'" := (TAtom "v55").
Notation "'‹buf+16@L43›'" := (TAtom "v58").
Notation "'‹chk(buf+16)@L43›'" := (TAtom "chk5").
Notation "'‹buf->write_end@L43›'" := (TAtom "v59").
Notation "'‹buf+8@L43›'" := (TAtom "v61").
Notation "'‹chk(buf+8)@L43›'" := (TAtom "chk6").
Notation "'‹buf->write_ptr@L43›'" := (TAtom "v62").
Notation "'‹addr(buf->write_end)@L43›'" := (TAtom "v63").
Notation "'‹addr(buf->write_ptr)@L43›'" := (TAtom "v64").
Notation "'‹to_copy@L43›'" := (TAtom "v65").
Notation "'‹to_copy>ucount›'" := (TAtom "v71").
Notation "'‹buf+8@L68›'" := (TAtom "v74").
Notation "'‹buf->write_ptr@L68›'" := (TAtom "v75").
Notation "'‹__GI_memcpy()›'" := (TAtom "v78").
Notation "'‹chk(buf+8)@L68›'" := (TAtom "chk8").
Notation "'‹buf->write_ptr@L68.2›'" := (TAtom "v81").
Notation "'‹chk(buf+8)@L68.2›'" := (TAtom "chk9").
Notation "'‹s@L68›'" := (TAtom "v86").
Notation "'‹count@L68›'" := (TAtom "v89").
End fn___printf_buffer_write.

Module fn___printf_buffer_flush.
Notation "'‹buf›'" := (TAtom "v0").
Notation "'‹buf+32›'" := (TAtom "iw_1.v3").
Notation "'‹chk(buf+32)›'" := (TAtom "chk0").
Notation "'‹buf->mode›'" := (TAtom "iw_1.v4").
Notation "'‹buf->mode==0›'" := (TAtom "iw_1.v5").
Notation "'‹buf+32@iw_2.start›'" := (TAtom "iw_2.v3").
Notation "'‹buf->mode@iw_2.start›'" := (TAtom "iw_2.v4").
Notation "'‹buf->mode<u6›'" := (TAtom "iw_2.v30").
Notation "'‹&__libc_errno›'" := (TAtom "iw_2.v19").
Notation "'‹chk(&__libc_errno)›'" := (TAtom "chk2").
Notation "'‹buf+32@iw_2.L18›'" := (TAtom "iw_2.iw_1.v3").
Notation "'‹chk(buf+32)@iw_2.L18›'" := (TAtom "chk3").
Notation "'‹buf->mode<u3›'" := (TAtom "iw_2.v33").
Notation "'‹buf->mode==0@iw_2.L34›'" := (TAtom "iw_2.v36").
Notation "'‹buf->mode==1›'" := (TAtom "iw_2.v38").
Notation "'‹buf->mode==2›'" := (TAtom "iw_2.v40").
Notation "'‹buf->mode==3›'" := (TAtom "iw_2.v42").
Notation "'‹buf->mode==4›'" := (TAtom "iw_2.v44").
Notation "'‹buf->mode==5›'" := (TAtom "iw_2.v46").
Notation "'‹buf->mode<u9›'" := (TAtom "iw_2.v48").
Notation "'‹buf->mode==6›'" := (TAtom "iw_2.v51").
Notation "'‹buf->mode==7›'" := (TAtom "iw_2.v53").
Notation "'‹buf->mode==8›'" := (TAtom "iw_2.v55").
Notation "'‹buf->mode==9›'" := (TAtom "iw_2.v57").
Notation "'‹buf->mode==10›'" := (TAtom "iw_2.v59").
Notation "'‹buf->mode==11›'" := (TAtom "iw_2.v61").
Notation "'‹buf+32@iw_3.start›'" := (TAtom "iw_3.v3").
Notation "'‹chk(buf+32)@iw_3.start›'" := (TAtom "chk4").
Notation "'‹buf->mode@iw_3.start›'" := (TAtom "iw_3.v4").
Notation "'‹buf->mode==0@iw_3.start›'" := (TAtom "iw_3.v5").
Notation "'‹buf+8›'" := (TAtom "v25").
Notation "'‹chk(buf+8)›'" := (TAtom "chk5").
Notation "'‹buf->write_ptr›'" := (TAtom "v26").
Notation "'‹buf+16›'" := (TAtom "v28").
Notation "'‹buf->write_end›'" := (TAtom "v29").
Notation "'‹addr(buf->write_ptr)›'" := (TAtom "v30").
Notation "'‹addr(buf->write_end)›'" := (TAtom "v31").
Notation "'‹addr(buf->write_ptr)!=addr(buf->write_end)›'" := (TAtom "v32").
Notation "'‹&glibc_printf_buffer_flush#str.39›'" := (TAtom "v33").
Notation "'‹&glibc_printf_buffer_flush#str.40›'" := (TAtom "v34").
Notation "'‹&glibc_printf_buffer_flush#str.41›'" := (TAtom "v35").
End fn___printf_buffer_flush.

End PrintfBufferIoNames.
