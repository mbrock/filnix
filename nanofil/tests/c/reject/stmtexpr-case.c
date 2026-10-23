// error: switch dispatch into a statement expression is not allowed
int f(int x) { switch (x) { return ({ case 1: 2; }); } return 0; }
