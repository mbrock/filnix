// error: break outside a loop or switch
int f(void) { while (({ break; 1; })) {} return 0; }
