/* String, memory, ctype and conversion functions of libc, printed so
   that two libcs can be compared. */
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int cmp(const void *a, const void *b) { return strcmp(*(char *const *) a, *(char *const *) b); }

int main(void)
{
    char buf[64], big[300];
    const char *s = "The quick brown fox jumps over the lazy dog";
    printf("%zu %zu %d %d %d\n", strlen(s), strlen(""), strcmp("abc", "abd") < 0, strncmp("abcx", "abcy", 3), memcmp("az", "ay", 2) > 0);
    strcpy(buf, "hello"); strcat(buf, ", world"); strncat(buf, "!!!!", 2);
    printf("[%s] [%s] [%s] [%s]\n", buf, strchr(s, 'q'), strrchr(s, 'o'), strstr(s, "lazy"));
    printf("%zu %zu [%s] %p\n", strspn(s, "Teh "), strcspn(s, "xyz"), strpbrk(s, "jz"), (void *) strchr(s, '#'));
    memset(big, 'a', sizeof big); big[sizeof big - 1] = 0;
    memmove(big + 3, big, 100); memcpy(big, "XYZ", 3); big[10] = 0;
    printf("[%s] %zu [%s]\n", big, strlen(big + 11), (char *) memchr(s, 'z', strlen(s)));
    char line[] = "a,b,,c;d", *save, *tok;
    for (tok = strtok_r(line, ",;", &save); tok; tok = strtok_r(NULL, ",;", &save)) printf("<%s>", tok);
    char *d = strdup(s), *n = strndup(s, 9);
    for (char *p = d; *p; p++) *p = isalpha((unsigned char) *p) ? toupper((unsigned char) *p) : '_';
    printf("\n%s %s %d %d %d\n", d, n, isdigit('7') != 0, isspace('\t') != 0, tolower('Q'));
    free(d); free(n);
    char *end;
    printf("%ld %lu %ld %lld %d [%s]\n", strtol("-0x7fz", &end, 16), strtoul("777", NULL, 8), strtol("  42abc", &end, 10), strtoll("-9223372036854775808", NULL, 10), atoi("123"), end);
    const char *words[] = { "pear", "apple", "fig", "banana", "cherry", "date" };
    qsort(words, 6, sizeof *words, cmp);
    const char *key = "fig", **hit = bsearch(&key, words, 6, sizeof *words, cmp);
    for (int i = 0; i < 6; i++) printf("%s ", words[i]);
    printf("| %td\n", hit - words);
    snprintf(buf, 8, "%s-%d", "truncated", 12345);
    printf("[%s] %d\n", buf, snprintf(NULL, 0, "%d%s", 99, "xyz"));
    return 0;
}
