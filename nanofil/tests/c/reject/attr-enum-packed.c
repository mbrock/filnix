// error: attribute packed is not supported in this position
// An enum's attributes were parsed and dropped: clang's sizeof is 1.
enum __attribute__((packed)) E { A, B };
int size = sizeof(enum E);
