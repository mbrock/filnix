# `.rept N` ... `.endr` assembles the enclosed statements N times, in data and
# in code, nested or not. A `.rept` used to end the current data block like
# any structural directive: TABLE named an empty object, and the repeated
# `.short`s fell into an unlabeled block that was dropped without a
# diagnostic, so the reference to TABLE failed to link. The data object must
# hold exactly the expanded bytes: rept_oob reads one word past its end and
# traps.
	.text
	.globl	rept_sum
	.type	rept_sum, @function
rept_sum:			#! long()
	xorl	%eax, %eax
	leaq	TABLE(%rip), %rcx
	movq	$8, %rdx
1:
	movzwl	(%rcx), %esi
	addq	%rsi, %rax
	addq	$2, %rcx
	decq	%rdx
	jnz	1b
	.rept	3
	addq	$1000, %rax
	.endr
	ret
	.size	rept_sum, .-rept_sum

	.globl	rept_oob
	.type	rept_oob, @function
rept_oob:			#! long()
	leaq	TABLE(%rip), %rcx
	movzwl	16(%rcx), %eax
	ret
	.size	rept_oob, .-rept_oob

	.section	.rodata
	.p2align	4
TABLE:
	.rept	2
	.short	1, 2
	.rept	2
	.short	30
	.endr
	.endr
	.section	.note.GNU-stack,"",@progbits
