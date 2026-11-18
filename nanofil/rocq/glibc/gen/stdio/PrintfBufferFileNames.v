(** These notations name the temporaries of compiled functions after the C expression each one holds.
    A proof imports the module of its own function, and then writes and reads a temporary by that name.
    Every name is one token between single guillemets, so it cannot be read as a term about proof variables.
    A name with @ and a label belongs to a later temporary that holds the same expression.
    These names are notations for the temporaries' own names; they add no premise.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String.
From Nanofil Require Import Term.
Open Scope string_scope.

Module PrintfBufferFileNames.

Module fn___printf_buffer_to_file_switch.
Notation "'‹buf›'" := (TAtom "v0").
Notation "'‹buf+40›'" := (TAtom "v6").
Notation "'‹chk(buf+40)›'" := (TAtom "chk0").
Notation "'‹buf->fp›'" := (TAtom "v7").
Notation "'‹buf->fp+40›'" := (TAtom "v8").
Notation "'‹chk(buf->fp+40)›'" := (TAtom "chk1").
Notation "'‹buf->fp->_IO_write_ptr›'" := (TAtom "v9").
Notation "'‹buf->fp@start›'" := (TAtom "v12").
Notation "'‹buf->fp+48›'" := (TAtom "v13").
Notation "'‹chk(buf->fp+48)›'" := (TAtom "chk3").
Notation "'‹buf->fp->_IO_write_end›'" := (TAtom "v14").
Notation "'‹addr(buf->fp->_IO_write_ptr)›'" := (TAtom "v15").
Notation "'‹addr(buf->fp->_IO_write_end)›'" := (TAtom "v16").
Notation "'‹addr(buf->fp->_IO_write_ptr)<uaddr(buf->fp->_IO_write_end)›'" := (TAtom "v17").
Notation "'‹buf+8›'" := (TAtom "v19").
Notation "'‹buf+40@L2›'" := (TAtom "v21").
Notation "'‹buf->fp@L2›'" := (TAtom "v22").
Notation "'‹buf->fp+40@L2›'" := (TAtom "v23").
Notation "'‹chk(buf->fp+40)@L2›'" := (TAtom "chk5").
Notation "'‹buf->fp->_IO_write_ptr@L2›'" := (TAtom "v24").
Notation "'‹chk(buf+8)›'" := (TAtom "chk6").
Notation "'‹buf+16›'" := (TAtom "v26").
Notation "'‹chk(buf+40)@L2›'" := (TAtom "chk7").
Notation "'‹buf->fp@L2.2›'" := (TAtom "v29").
Notation "'‹buf->fp+48@L2›'" := (TAtom "v30").
Notation "'‹chk(buf->fp+48)@L2›'" := (TAtom "chk8").
Notation "'‹buf->fp->_IO_write_end@L2›'" := (TAtom "v31").
Notation "'‹chk(buf+16)›'" := (TAtom "chk9").
Notation "'‹buf+8@L3›'" := (TAtom "v33").
Notation "'‹buf+48›'" := (TAtom "v35").
Notation "'‹chk(buf+8)@L3›'" := (TAtom "chk10").
Notation "'‹buf+16@L3›'" := (TAtom "v37").
Notation "'‹buf+48+128›'" := (TAtom "v43").
Notation "'‹chk(buf+16)@L3›'" := (TAtom "chk11").
Notation "'‹buf+8@L4›'" := (TAtom "v46").
Notation "'‹chk(buf+8)@L4›'" := (TAtom "chk12").
Notation "'‹buf->base.write_ptr›'" := (TAtom "v47").
Notation "'‹chk(buf)›'" := (TAtom "chk13").
End fn___printf_buffer_to_file_switch.

Module fn___printf_buffer_flush_to_file.
Notation "'‹buf›'" := (TAtom "v0").
Notation "'‹buf+24›'" := (TAtom "v3").
Notation "'‹chk(buf+24)›'" := (TAtom "chk0").
Notation "'‹buf->base.written›'" := (TAtom "v4").
Notation "'‹buf+8›'" := (TAtom "v6").
Notation "'‹chk(buf+8)›'" := (TAtom "chk1").
Notation "'‹buf->base.write_ptr›'" := (TAtom "v7").
Notation "'‹chk(buf)›'" := (TAtom "chk2").
Notation "'‹buf->base.write_base›'" := (TAtom "v9").
Notation "'‹addr(buf->base.write_ptr)›'" := (TAtom "v10").
Notation "'‹addr(buf->base.write_base)›'" := (TAtom "v11").
Notation "'‹chk(buf+24)@start›'" := (TAtom "chk3").
Notation "'‹buf+16›'" := (TAtom "v18").
Notation "'‹buf->base.write_end›'" := (TAtom "v19").
Notation "'‹buf+48›'" := (TAtom "v21").
Notation "'‹buf+48+128›'" := (TAtom "v25").
Notation "'‹addr(buf->base.write_end)›'" := (TAtom "v26").
Notation "'‹addr(buf+48+128)›'" := (TAtom "v27").
Notation "'‹addr(buf->base.write_end)==addr(buf+48+128)›'" := (TAtom "v28").
Notation "'‹buf+8@L14›'" := (TAtom "v31").
Notation "'‹buf->base.write_ptr@L14›'" := (TAtom "v32").
Notation "'‹buf+48@L14›'" := (TAtom "v34").
Notation "'‹addr(buf->base.write_ptr)@L14›'" := (TAtom "v35").
Notation "'‹addr(buf+48)›'" := (TAtom "v36").
Notation "'‹count›'" := (TAtom "v37").
Notation "'‹buf+40›'" := (TAtom "v42").
Notation "'‹chk(buf+40)›'" := (TAtom "chk6").
Notation "'‹buf->fp›'" := (TAtom "v43").
Notation "'‹buf->fp+216›'" := (TAtom "v44").
Notation "'‹chk(buf->fp+216)›'" := (TAtom "chk7").
Notation "'‹[buf->fp+216]›'" := (TAtom "v45").
Notation "'‹ptr›'" := (TAtom "iw_1.v4").
Notation "'‹&__io_vtables›'" := (TAtom "iw_1.v7").
Notation "'‹addr(&__io_vtables)›'" := (TAtom "iw_1.v8").
Notation "'‹offset›'" := (TAtom "iw_1.v9").
Notation "'‹offset>=u2352›'" := (TAtom "iw_1.v15").
Notation "'‹[buf->fp+216]+56›'" := (TAtom "v47").
Notation "'‹chk([buf->fp+216]+56)›'" := (TAtom "chk8").
Notation "'‹[[buf->fp+216]+56]›'" := (TAtom "v48").
Notation "'‹buf+40@iw_1.join›'" := (TAtom "v50").
Notation "'‹chk(buf+40)@iw_1.join›'" := (TAtom "chk9").
Notation "'‹buf->fp@iw_1.join›'" := (TAtom "v51").
Notation "'‹buf+48@iw_1.join›'" := (TAtom "v53").
Notation "'‹buf+32›'" := (TAtom "iw_2.v3").
Notation "'‹chk(buf+32)›'" := (TAtom "chk11").
Notation "'‹buf+16@L15›'" := (TAtom "v66").
Notation "'‹buf->base.write_end@L15›'" := (TAtom "v67").
Notation "'‹buf+48@L15›'" := (TAtom "v69").
Notation "'‹buf+48+1›'" := (TAtom "v70").
Notation "'‹addr(buf->base.write_end)@L15›'" := (TAtom "v71").
Notation "'‹addr(buf+48+1)›'" := (TAtom "v72").
Notation "'‹addr(buf->base.write_end)==addr(buf+48+1)›'" := (TAtom "v73").
Notation "'‹buf+8@L62›'" := (TAtom "v78").
Notation "'‹buf->base.write_ptr@L62›'" := (TAtom "v79").
Notation "'‹buf+16@L62›'" := (TAtom "v81").
Notation "'‹buf->base.write_end@L62›'" := (TAtom "v82").
Notation "'‹addr(buf->base.write_ptr)@L62›'" := (TAtom "v83").
Notation "'‹addr(buf->base.write_end)@L62›'" := (TAtom "v84").
Notation "'‹addr(buf->base.write_ptr)==addr(buf->base.write_end)›'" := (TAtom "v85").
Notation "'‹buf+40@L74›'" := (TAtom "v90").
Notation "'‹chk(buf+40)@L74›'" := (TAtom "chk15").
Notation "'‹buf->fp@L74›'" := (TAtom "v91").
Notation "'‹buf+48@L74›'" := (TAtom "v93").
Notation "'‹chk(buf+48)›'" := (TAtom "chk16").
Notation "'‹buf->stage›'" := (TAtom "v94").
Notation "'‹__GI___overflow()›'" := (TAtom "v96").
Notation "'‹__GI___overflow()==4294967295›'" := (TAtom "v98").
Notation "'‹buf+32@iw_3.start›'" := (TAtom "iw_3.v3").
Notation "'‹chk(buf+32)@iw_3.start›'" := (TAtom "chk17").
Notation "'‹buf+16@L16›'" := (TAtom "v107").
Notation "'‹buf->base.write_end@L16›'" := (TAtom "v108").
Notation "'‹buf+40@L16›'" := (TAtom "v110").
Notation "'‹chk(buf+40)@L16›'" := (TAtom "chk19").
Notation "'‹buf->fp@L16›'" := (TAtom "v111").
Notation "'‹buf->fp+48›'" := (TAtom "v112").
Notation "'‹chk(buf->fp+48)›'" := (TAtom "chk20").
Notation "'‹buf->fp->_IO_write_end›'" := (TAtom "v113").
Notation "'‹addr(buf->base.write_end)@L16›'" := (TAtom "v114").
Notation "'‹addr(buf->fp->_IO_write_end)›'" := (TAtom "v115").
Notation "'‹addr(buf->base.write_end)==addr(buf->fp->_IO_write_end)›'" := (TAtom "v116").
Notation "'‹&glibc_printf_buffer_to_file#str.266›'" := (TAtom "v117").
Notation "'‹&glibc_printf_buffer_to_file#str.267›'" := (TAtom "v118").
Notation "'‹&glibc_printf_buffer_to_file#str.268›'" := (TAtom "v119").
Notation "'‹buf+40@L105›'" := (TAtom "v121").
Notation "'‹chk(buf+40)@L105›'" := (TAtom "chk21").
Notation "'‹buf->fp@L105›'" := (TAtom "v122").
Notation "'‹buf->fp+40›'" := (TAtom "v123").
Notation "'‹buf+8@L105›'" := (TAtom "v125").
Notation "'‹chk(buf+8)@L105›'" := (TAtom "chk22").
Notation "'‹buf->base.write_ptr@L105›'" := (TAtom "v126").
Notation "'‹chk(buf->fp+40)›'" := (TAtom "chk23").
Notation "'‹chk(buf+8)@L105.2›'" := (TAtom "chk24").
Notation "'‹buf->base.write_ptr@L105.2›'" := (TAtom "v132").
Notation "'‹buf+16@L105›'" := (TAtom "v134").
Notation "'‹chk(buf+16)›'" := (TAtom "chk25").
Notation "'‹buf->base.write_end@L105›'" := (TAtom "v135").
Notation "'‹addr(buf->base.write_ptr)@L105›'" := (TAtom "v136").
Notation "'‹addr(buf->base.write_end)@L105›'" := (TAtom "v137").
Notation "'‹addr(buf->base.write_ptr)==addr(buf->base.write_end)@L105›'" := (TAtom "v138").
Notation "'‹buf+8@L127›'" := (TAtom "v140").
Notation "'‹buf+48@L127›'" := (TAtom "v142").
Notation "'‹chk(buf+8)@L127›'" := (TAtom "chk26").
Notation "'‹buf+16@L127›'" := (TAtom "v144").
Notation "'‹buf+48+1@L127›'" := (TAtom "v147").
Notation "'‹chk(buf+16)@L127›'" := (TAtom "chk27").
Notation "'‹buf+8@L129›'" := (TAtom "v150").
Notation "'‹chk(buf+8)@L129›'" := (TAtom "chk28").
Notation "'‹buf->base.write_ptr@L129›'" := (TAtom "v151").
Notation "'‹chk(buf)@L129›'" := (TAtom "chk29").
End fn___printf_buffer_flush_to_file.

Module fn___printf_buffer_to_file_init.
Notation "'‹buf›'" := (TAtom "v0").
Notation "'‹fp›'" := (TAtom "v2").
Notation "'‹buf+48›'" := (TAtom "v6").
Notation "'‹buf+48+128›'" := (TAtom "iw_1.v12").
Notation "'‹chk(buf)›'" := (TAtom "chk0").
Notation "'‹buf+8›'" := (TAtom "iw_1.iw_1.v11").
Notation "'‹chk(buf+8)›'" := (TAtom "chk1").
Notation "'‹buf+16›'" := (TAtom "iw_1.iw_1.v14").
Notation "'‹chk(buf+16)›'" := (TAtom "chk2").
Notation "'‹buf+24›'" := (TAtom "iw_1.iw_1.v17").
Notation "'‹chk(buf+24)›'" := (TAtom "chk3").
Notation "'‹buf+32›'" := (TAtom "iw_1.iw_1.v19").
Notation "'‹chk(buf+32)›'" := (TAtom "chk4").
Notation "'‹buf+40›'" := (TAtom "v11").
Notation "'‹chk(buf+40)›'" := (TAtom "chk5").
End fn___printf_buffer_to_file_init.

Module fn___printf_buffer_to_file_done.
Notation "'‹buf›'" := (TAtom "v0").
Notation "'‹buf+32›'" := (TAtom "iw_1.v3").
Notation "'‹chk(buf+32)›'" := (TAtom "chk0").
Notation "'‹buf->mode›'" := (TAtom "iw_1.v4").
Notation "'‹buf->mode==0›'" := (TAtom "iw_1.v5").
Notation "'‹__printf_buffer_done()›'" := (TAtom "v12").
End fn___printf_buffer_to_file_done.

End PrintfBufferFileNames.
