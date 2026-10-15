# The `movq %rsp, %reg` spelling of sarcasm-reject-lea-carrier-callarg-att: a
# stack-pointer save passed as a call argument is a value use of the dropped
# save, so the callee would receive whatever the argument register held before
# it (here, the incoming `a`). The call's signature makes its argument
# registers uses of the carrier, so this is rejected at the call.
	.text
	.globl	pass_rows
	.type	pass_rows, @function
pass_rows:			#! void(ptr, ptr)
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp
	movq	%rdi, 0(%rsp)		#! store ptr
	movq	%rsi, 8(%rsp)		#! store ptr
	movq	%rsp, %rdi
	call	use_rows		#! void(ptr)
	addq	$16, %rsp
	popq	%rbp
	ret
	.size	pass_rows, .-pass_rows
	.section	.note.GNU-stack,"",@progbits
