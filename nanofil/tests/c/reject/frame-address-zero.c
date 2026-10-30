// error: :5: __builtin_frame_address(0) is not supported
/* filcc returns the frame's address without a capability (quickjs's
   js_get_stack_pointer); nanofil has no IR term for it, so it refuses
   rather than return some other address. */
unsigned long f(void) { return (unsigned long)__builtin_frame_address(0); }
