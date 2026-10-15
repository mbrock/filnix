# An `.endr` without a matching `.rept` is rejected (GNU as rejects it too),
# as is a `.rept` that is never closed.
	.section	.rodata
TABLE:
	.short	1
	.endr
	.section	.note.GNU-stack,"",@progbits
