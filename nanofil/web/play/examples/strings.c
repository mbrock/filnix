#include <stdio.h>
#include <string.h>

/* Strings are bytes in Data; reversing one walks two pointers inward. */
static void reverse(char *s) {
    char *end = s + strlen(s) - 1;
    while (s < end) {
        char c = *s;
        *s++ = *end;
        *end-- = c;
    }
}

int main(void) {
    char word[] = "nanofil";
    reverse(word);
    puts(word);
    return 0;
}
