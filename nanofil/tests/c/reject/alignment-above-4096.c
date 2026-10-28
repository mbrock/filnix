// error: an alignment above 4096
/* nanofil aligns an object to 4096 at most (c_types max_alignment). */
_Alignas(8192) char page[1];
