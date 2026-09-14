/* Exercise pointer strings across independently loaded plugin boundaries. */
#include <spa/utils/ptr-string.h>

__attribute__((visibility("default")))
void encode(char *text, size_t size, void *pointer)
{
    snprintf(text, size, SPA_POINTER_FORMAT, SPA_POINTER_VALUE(pointer));
}

__attribute__((visibility("default")))
int decode(const char *text, void **pointer)
{
    return spa_pointer_parse(text, pointer);
}
