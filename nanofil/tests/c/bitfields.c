// Bit-fields: layout, loads extended by sign, stores that keep their
// neighbours, promotion, assignment values, initializers and copies.
struct flags {
    unsigned u3 : 3;
    signed s4 : 4;
    unsigned top : 25;          // ends at bit 32: the unit's top bits
    unsigned u32 : 32;
};

struct wide {
    unsigned long long lo : 40, hi : 24;
    long s33 : 33;
    unsigned char c : 3;
    short sh : 9;               // starts in c's byte, a short unit
};

struct mixed {
    char a : 3;
    int : 0;                    // b starts at the next int boundary
    char b : 2;
};

enum code { SOME = 148, OTHER };

struct tagged {
    enum code code : 8;         // values up to 255: an unsigned field
    _Bool flag : 1;
    int straddle : 20, next : 20; // next cannot share straddle's int
};

union either {
    int x : 5;
    unsigned y : 10;
};

struct pair {
    char x, y;
    long long z : 48;           // shares the first eightbyte with x and y
};

struct outer {
    int before;
    struct { unsigned a : 4, b : 4; };
};

static struct flags flags0 = { .s4 = -3, .u3 = 6, .top = 0x1abcdef };
static struct wide wide0 = { 0xfedcba9876, 0xabcdef, -5, 7, -200 };
static struct tagged tagged0 = { OTHER, 1, -1, 12345 };
static union either either0 = { .y = 1000 };

int loads(int which) {
    struct flags f = flags0;
    switch (which) {
    case 0: return f.u3;                        // 6
    case 1: return f.s4;                        // -3, sign extended
    case 2: return f.top == 0x1abcdef;
    case 3: return wide0.lo == 0xfedcba9876ULL && wide0.hi == 0xabcdef;
    case 4: return wide0.s33;                   // -5
    case 5: return wide0.c * 1000 + wide0.sh;   // 7000 - 200
    case 6: return tagged0.code == OTHER && tagged0.flag;
    case 7: return tagged0.straddle * 100000 + tagged0.next;
    case 8: return either0.y;                   // 1000
    case 9: return either0.x;                   // low 5 bits of 1000: 8
    }
    return -1;
}

int stores(int which) {
    struct flags f = flags0;
    struct wide w = wide0;
    switch (which) {
    case 0: f.s4 = 5; return f.u3 * 100 + f.s4 * 10 + (f.top == 0x1abcdef);
    case 1: f.top = 0x1ffffff; return f.u3 + f.s4 + (f.top == 0x1ffffff);
    case 2: w.hi = 1; return w.lo == 0xfedcba9876ULL && w.s33 == -5;
    case 3: w.c = 2; return w.sh;               // -200 survives
    case 4: w.sh = 255; return w.c * 1000 + w.sh;
    case 5: f.u32 = 0xffffffff; return f.u3 + f.s4;
    }
    return -1;
}

int values(int which) {
    struct flags f = { 0 };
    switch (which) {
    case 0: return (f.s4 = 15) == -1;           // the stored value
    case 1: return f.u3 = 13;                   // 5
    case 2: return -1 > f.u3;                   // an int: 0
    case 3: return f.u3 - 4 < 0;                // 1
    case 4: return f.u32 - 1 > 0;               // an unsigned: 1
    case 5: f.u3 = 3; f.u3 /= -1; return f.u3;  // -3 in 3 bits: 5
    case 6: f.s4 = 7; f.s4 += 9; return f.s4;   // 16 in 4 bits: 0
    case 7: { f.u3 = 7; int old = f.u3++; return old * 10 + f.u3; } // 70
    case 8: f.u3 = 7; return ++f.u3;            // 0
    case 9: f.s4 = 7; return ++f.s4;            // -8
    case 10: f.s4 = -8; return f.s4--;          // -8, then 7
    case 11: f.s4 = -8; f.s4--; return f.s4;    // 7
    }
    return -1;
}

static int via(struct flags *p) { p->s4 = -2; return p->u3 + p->s4; }

static long long passed(struct pair p) { return p.z + p.x + p.y; }

int others(int which) {
    struct flags f = flags0;
    struct pair p = { 1, 2, -1000000000000LL };
    struct outer o = { 9, { 3, 12 } };
    struct mixed m = { -2, 1 };
    switch (which) {
    case 0: return via(&f) * 10 + f.s4;         // 4*10 - 2
    case 1: return passed(p) == -999999999997LL;
    case 2: o.b = 5; return o.before * 100 + o.a * 10 + o.b;
    case 3: return m.a * 10 + m.b;              // -2*10 + 1
    case 4: { struct flags g = f; g.u3 = 1; return f.u3 * 10 + g.u3; }
    case 5: {
        int n = 0;
        for (int i = 0; i < 3; i++) {
            struct flags h = { .s4 = i };       // zeroed on every pass
            n = n * 10 + h.u3 + h.s4;
            h.u3 = 7;
        }
        return n;                               // 12
    }
    }
    return -1;
}

int layout(void) {
    return sizeof(struct flags) * 1000000 + sizeof(struct wide) * 10000
        + sizeof(struct mixed) * 100 + _Alignof(struct mixed) * 10
        + sizeof(union either) / 4;             // 8, 16, 5, 1, 1
}

int tagged_sizes(void) {
    return sizeof(struct tagged) * 100 + sizeof(struct pair) * 10
        + _Alignof(struct tagged) / 4;          // 8, 8, 1
}

// run: $loads 0
// run: $loads 1
// run: $loads 2
// run: $loads 3
// run: $loads 4
// run: $loads 5
// run: $loads 6
// run: $loads 7
// run: $loads 8
// run: $loads 9
// run: $stores 0
// run: $stores 1
// run: $stores 2
// run: $stores 3
// run: $stores 4
// run: $stores 5
// run: $values 0
// run: $values 1
// run: $values 2
// run: $values 3
// run: $values 4
// run: $values 5
// run: $values 6
// run: $values 7
// run: $values 8
// run: $values 9
// run: $values 10
// run: $values 11
// run: $others 0
// run: $others 1
// run: $others 2
// run: $others 3
// run: $others 4
// run: $others 5
// run: $layout
// run: $tagged_sizes
