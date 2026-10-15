	.intel_syntax noprefix
	.text
	.globl pass_rows
	.type pass_rows,@function
# void pass_rows(char *a, char *b): builds char *rows[2] = {a, b} on the
# stack and calls use_rows(rows).
pass_rows: #! void(ptr, ptr)
	push rbp
	mov rbp, rsp
	sub rsp, 16
	mov qword ptr [rsp], rdi #! store ptr
	mov qword ptr [rsp + 8], rsi #! store ptr
	lea rdi, [rsp]
	call use_rows #! void(ptr)
	add rsp, 16
	pop rbp
	ret
