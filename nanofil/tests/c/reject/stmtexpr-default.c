// error: switch dispatch into a statement expression is not allowed
int f(int x) { switch (x) { return ({ default: 2; }); } }
