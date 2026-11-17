(** These notations name the temporaries of compiled functions after the C expression each one holds.
    A proof imports the module of its own function, and then writes and reads a temporary by that name.
    Every name is one token between single guillemets, so it cannot be read as a term about proof variables.
    A name with @ and a label belongs to a later temporary that holds the same expression.
    These names are notations for the temporaries' own names; they add no premise.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String.
From Nanofil Require Import Term.
Open Scope string_scope.

Module FxprintfNormalNames.

Module fn___vfxprintf.
Notation "'‹fp›'" := (TAtom "v0").
Notation "'‹fmt›'" := (TAtom "v2").
Notation "'‹ap›'" := (TAtom "v4").
Notation "'‹mode_flags›'" := (TAtom "v6").
Notation "'‹fp@L10›'" := (TAtom "pr.1").
Notation "'‹res›'" := (TAtom "iw_1.pr.3").
Notation "'‹res@iw_1.join›'" := (TAtom "v110").
Notation "'‹__oldval›'" := (TAtom "v167").
Notation "'‹addr(fp)›'" := (TAtom "v12").
Notation "'‹&stderr›'" := (TAtom "v15").
Notation "'‹chk(&stderr)›'" := (TAtom "chk0").
Notation "'‹stderr›'" := (TAtom "v16").
Notation "'‹chk(fp)›'" := (TAtom "chk1").
Notation "'‹fp->_flags›'" := (TAtom "v21").
Notation "'‹__self›'" := (TAtom "v28").
Notation "'‹&__libc_single_threaded_internal›'" := (TAtom "v32").
Notation "'‹chk(&__libc_single_threaded_internal)›'" := (TAtom "chk2").
Notation "'‹__libc_single_threaded_internal›'" := (TAtom "v33").
Notation "'‹__libc_single_threaded_internal!=0›'" := (TAtom "v34").
Notation "'‹fp+136›'" := (TAtom "v38").
Notation "'‹chk(fp+136)›'" := (TAtom "chk3").
Notation "'‹fp->_lock›'" := (TAtom "v39").
Notation "'‹fp->_lock+8›'" := (TAtom "v40").
Notation "'‹chk(fp->_lock+8)›'" := (TAtom "chk4").
Notation "'‹fp->_lock->owner›'" := (TAtom "v41").
Notation "'‹addr(fp->_lock->owner)›'" := (TAtom "v42").
Notation "'‹fp+136@L29›'" := (TAtom "v48").
Notation "'‹chk(fp+136)@L29›'" := (TAtom "chk5").
Notation "'‹fp->_lock@L29›'" := (TAtom "v49").
Notation "'‹chk(fp->_lock)›'" := (TAtom "chk6").
Notation "'‹fp->_lock@L29.2›'" := (TAtom "v52").
Notation "'‹fp->_lock+8@L29›'" := (TAtom "v53").
Notation "'‹chk(fp->_lock+8)@L29›'" := (TAtom "chk8").
Notation "'‹fp+136@L30›'" := (TAtom "v59").
Notation "'‹chk(fp+136)@L30›'" := (TAtom "chk9").
Notation "'‹fp->_lock@L30›'" := (TAtom "v60").
Notation "'‹fp->_lock+8@L30›'" := (TAtom "v61").
Notation "'‹chk(fp->_lock+8)@L30›'" := (TAtom "chk10").
Notation "'‹fp->_lock->owner@L30›'" := (TAtom "v62").
Notation "'‹addr(fp->_lock->owner)@L30›'" := (TAtom "v64").
Notation "'‹addr(__self)›'" := (TAtom "v65").
Notation "'‹addr(fp->_lock->owner)!=addr(__self)›'" := (TAtom "v66").
Notation "'‹fp+136@L55›'" := (TAtom "v69").
Notation "'‹__futex›'" := (TAtom "v70").
Notation "'‹chk(__futex)›'" := (TAtom "chk12").
Notation "'‹__atg3_old›'" := (TAtom "v77").
Notation "'‹__atg3_old==0›'" := (TAtom "v78").
Notation "'‹__atg3_old!=0›'" := (TAtom "v81").
Notation "'‹fp+136@L73›'" := (TAtom "v95").
Notation "'‹chk(fp+136)@L73›'" := (TAtom "chk13").
Notation "'‹fp->_lock@L73›'" := (TAtom "v96").
Notation "'‹fp->_lock+8@L73›'" := (TAtom "v97").
Notation "'‹chk(fp->_lock+8)@L73›'" := (TAtom "chk14").
Notation "'‹fp+136@L56›'" := (TAtom "v100").
Notation "'‹fp->_lock@L56›'" := (TAtom "v101").
Notation "'‹fp->_lock+4›'" := (TAtom "v102").
Notation "'‹chk(fp->_lock+4)›'" := (TAtom "chk16").
Notation "'‹fp->_lock->cnt›'" := (TAtom "v103").
Notation "'‹chk(fp->_lock+4)@L56›'" := (TAtom "chk17").
Notation "'‹&fmt›'" := (TAtom "iw_1.v3").
Notation "'‹&mbstate›'" := (TAtom "iw_1.v63").
Notation "'‹&buf›'" := (TAtom "iw_1.v69").
Notation "'‹chk(&fmt)›'" := (TAtom "chk18").
Notation "'‹fp+192›'" := (TAtom "iw_1.v48").
Notation "'‹chk(fp+192)›'" := (TAtom "chk19").
Notation "'‹fp->_mode›'" := (TAtom "iw_1.v49").
Notation "'‹fp->_mode<=0›'" := (TAtom "iw_1.v55").
Notation "'‹chk(&fmt)@iw_1.L8›'" := (TAtom "chk20").
Notation "'‹fmt@iw_1.L8›'" := (TAtom "iw_1.v57").
Notation "'‹__vfprintf_internal()›'" := (TAtom "iw_1.v60").
Notation "'‹chk(&fmt)@iw_1.L10›'" := (TAtom "chk21").
Notation "'‹fmt@iw_1.L10›'" := (TAtom "iw_1.v66").
Notation "'‹__GI_strlen()›'" := (TAtom "iw_1.v67").
Notation "'‹len›'" := (TAtom "iw_1.v68").
Notation "'‹&buf+16›'" := (TAtom "iw_1.iw_1.v4").
Notation "'‹chk(&buf)›'" := (TAtom "chk22").
Notation "'‹&buf+8›'" := (TAtom "iw_1.iw_1.v6").
Notation "'‹chk(&buf+8)›'" := (TAtom "chk23").
Notation "'‹len>u4611686018427387903›'" := (TAtom "iw_1.v75").
Notation "'‹&__libc_errno›'" := (TAtom "iw_1.v78").
Notation "'‹chk(&__libc_errno)›'" := (TAtom "chk24").
Notation "'‹__GI___libc_scratch_buffer_set_array_size()›'" := (TAtom "iw_1.iw_2.v9").
Notation "'‹chk(&buf)@iw_1.L83›'" := (TAtom "chk25").
Notation "'‹wfmt›'" := (TAtom "iw_1.v90").
Notation "'‹__GI_memset()›'" := (TAtom "iw_1.v91").
Notation "'‹res@iw_1.L83›'" := (TAtom "iw_1.v94").
Notation "'‹res@iw_1.L83.2›'" := (TAtom "iw_1.v98").
Notation "'‹res!=4294967295›'" := (TAtom "iw_1.v100").
Notation "'‹res@iw_1.L95›'" := (TAtom "iw_1.v105").
Notation "'‹chk(&buf)@iw_1.L97›'" := (TAtom "chk26").
Notation "'‹fp->data›'" := (TAtom "iw_1.iw_3.v6").
Notation "'‹&buf+16@iw_1.L97›'" := (TAtom "iw_1.iw_3.v8").
Notation "'‹addr(fp->data)›'" := (TAtom "iw_1.iw_3.v9").
Notation "'‹addr(&buf+16)›'" := (TAtom "iw_1.iw_3.v10").
Notation "'‹addr(fp->data)!=addr(&buf+16)›'" := (TAtom "iw_1.iw_3.v11").
Notation "'‹fp->data@iw_1.iw_3.L2›'" := (TAtom "iw_1.iw_3.v13").
Notation "'‹chk(fp)@iw_1.join›'" := (TAtom "chk28").
Notation "'‹fp->_flags@iw_1.join›'" := (TAtom "v115").
Notation "'‹&__libc_single_threaded_internal@L118›'" := (TAtom "v124").
Notation "'‹chk(&__libc_single_threaded_internal)@L118›'" := (TAtom "chk29").
Notation "'‹__libc_single_threaded_internal@L118›'" := (TAtom "v125").
Notation "'‹__libc_single_threaded_internal!=0@L118›'" := (TAtom "v126").
Notation "'‹fp+136@L127›'" := (TAtom "v130").
Notation "'‹chk(fp+136)@L127›'" := (TAtom "chk30").
Notation "'‹fp->_lock@L127›'" := (TAtom "v131").
Notation "'‹fp->_lock+4@L127›'" := (TAtom "v132").
Notation "'‹chk(fp->_lock+4)@L127›'" := (TAtom "chk31").
Notation "'‹fp->_lock->cnt@L127›'" := (TAtom "v133").
Notation "'‹fp->_lock->cnt==0›'" := (TAtom "v134").
Notation "'‹fp+136@L121›'" := (TAtom "v138").
Notation "'‹chk(fp+136)@L121›'" := (TAtom "chk32").
Notation "'‹fp->_lock@L121›'" := (TAtom "v139").
Notation "'‹fp->_lock+8@L121›'" := (TAtom "v140").
Notation "'‹chk(fp->_lock+8)@L121›'" := (TAtom "chk33").
Notation "'‹chk(fp+136)@L121.2›'" := (TAtom "chk34").
Notation "'‹fp->_lock@L121.2›'" := (TAtom "v143").
Notation "'‹chk(fp->_lock)@L121›'" := (TAtom "chk35").
Notation "'‹fp+136@L122›'" := (TAtom "v148").
Notation "'‹chk(fp+136)@L122›'" := (TAtom "chk36").
Notation "'‹fp->_lock@L122›'" := (TAtom "v149").
Notation "'‹fp->_lock+4@L122›'" := (TAtom "v150").
Notation "'‹chk(fp->_lock+4)@L122›'" := (TAtom "chk37").
Notation "'‹fp->_lock->cnt@L122›'" := (TAtom "v151").
Notation "'‹fp->_lock->cnt==0@L122›'" := (TAtom "v152").
Notation "'‹fp+136@L144›'" := (TAtom "v154").
Notation "'‹fp->_lock@L144›'" := (TAtom "v155").
Notation "'‹fp->_lock+8@L144›'" := (TAtom "v156").
Notation "'‹chk(fp->_lock+8)@L144›'" := (TAtom "chk39").
Notation "'‹chk(fp+136)@L144›'" := (TAtom "chk40").
Notation "'‹__futex@L144›'" := (TAtom "v160").
Notation "'‹chk(__futex)@L144›'" := (TAtom "chk41").
Notation "'‹[__futex]›'" := (TAtom "v164").
Notation "'‹chk(__futex)@L165›'" := (TAtom "chk42").
Notation "'‹__oldval>1›'" := (TAtom "v174").
Notation "'‹fp+136@L145›'" := (TAtom "v189").
Notation "'‹fp->_lock@L145›'" := (TAtom "v190").
Notation "'‹fp->_lock+4@L145›'" := (TAtom "v191").
Notation "'‹chk(fp->_lock+4)@L145›'" := (TAtom "chk44").
Notation "'‹fp->_lock->cnt@L145›'" := (TAtom "v192").
Notation "'‹chk(fp->_lock+4)@L145.2›'" := (TAtom "chk45").
End fn___vfxprintf.

Module fn___fxprintf.
Notation "'‹fp›'" := (TAtom "v0").
Notation "'‹fmt›'" := (TAtom "v2").
Notation "'‹&ap›'" := (TAtom "v4").
Notation "'‹chk(&ap)›'" := (TAtom "chk0").
Notation "'‹res›'" := (TAtom "v8").
End fn___fxprintf.

End FxprintfNormalNames.
