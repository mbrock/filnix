/* Like glibc FILE: the typedef precedes completion, and an unsupported
   bitfield follows an ordinary member whose offset is still known. */
typedef struct stream stream;
struct stream {
    long flags;
    int flags2 : 24;
    char backup;
};

static void seterr(stream *fp) { fp->flags |= 32; }

long member_prefix(long x) {
    seterr((stream *)&x);
    return x;
}
// run: $member_prefix 0
// run: $member_prefix 5
// run: $member_prefix 32
