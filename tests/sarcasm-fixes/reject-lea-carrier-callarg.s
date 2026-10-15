# A carrier passed as a call argument is a value use of the phantom save: the
# frame-interior lea is dropped by the rewrite, so the callee would receive
# whatever the argument register held before it (here, the incoming `a`).
# The call's argument registers come from its signature; they are uses of the
# carrier exactly like an explicit operand, so this is rejected at the call.
# (Previously the call only poisoned the caller-saved carrier, and the callee
# silently received `a` with its capability instead of the frame address.)
	.text
	.globl	pass_rows
	.type	pass_rows, @function
pass_rows:			#! void(ptr, ptr)
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp
	movq	%rdi, 0(%rsp)		#! store ptr
	movq	%rsi, 8(%rsp)		#! store ptr
	leaq	0(%rsp), %rdi
	call	use_rows		#! void(ptr)
	addq	$16, %rsp
	popq	%rbp
	ret
	.size	pass_rows, .-pass_rows
	.section	.note.GNU-stack,"",@progbits
