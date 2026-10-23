	.text
	.globl	pizlonatedFIP1598_add2
	.type	pizlonatedFIP1598_add2,@function
pizlonatedFIP1598_add2:
	cmpq	%rsp, (%rdi)
	jae	filc_stack_overflow_failure@PLT
	leaq	(%rdx,%rcx), %rdx
	xorl	%eax, %eax
	retq
	.size	pizlonatedFIP1598_add2, .-pizlonatedFIP1598_add2
	.globl	pizlonatedFI1598_add2
	.type	pizlonatedFI1598_add2,@function
	.set	pizlonatedFI1598_add2, pizlonatedFIP1598_add2

	.globl	pizlonated_add2
	.type	pizlonated_add2,@function
pizlonated_add2:
	leaq	pizlonatedFO_add2+16(%rip), %rax
	movq	%rax, %rdx
	retq
	.size	pizlonated_add2, .-pizlonated_add2

# generic entry: unpack two i64 args from the inline buffer, call fast, repack
	.type	nanofil_generic_add2,@function
nanofil_generic_add2:
	pushq	%rbx
	cmpq	$15, %rdx
	jbe	1f
	movq	%rdi, %rbx
	movq	128(%rdi), %rdx
	movq	136(%rdi), %rcx
	callq	pizlonatedFIP1598_add2
	testb	$1, %al
	jne	2f
	movq	%rdx, 128(%rbx)
	movq	$0, 384(%rbx)
	movl	$8, %edx
2:	popq	%rbx
	retq
1:	movl	$16, %esi
	movq	%rdx, %rdi
	xorl	%edx, %edx
	callq	filc_cc_args_check_failure@PLT
	.size	nanofil_generic_add2, .-nanofil_generic_add2

	.section	.data.rel.ro,"aw",@progbits
	.p2align	4
	.type	pizlonatedFO_add2,@object
pizlonatedFO_add2:
	.quad	pizlonatedFO_add2+16
	.quad	(pizlonatedFO_add2+16)+36873221949095936
	.quad	pizlonatedFIP1598_add2
	.quad	nanofil_generic_add2
	.quad	1598
	.size	pizlonatedFO_add2, 40
	.section	".note.GNU-stack","",@progbits
