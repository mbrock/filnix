// error: this __declspec is not supported
/* __declspec(thread) would make x thread-local; nanofil maps only the
   declspecs that keep code and layout, and align(N). */
__declspec(thread) int x;
