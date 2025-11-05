#include <stdio.h>

int
main ()
{
  int c;
  while ((c = getchar ()) != EOF)
    {
      switch (c)
        {
        case '&':
          printf ("&amp;");
          break;
        case '<':
          printf ("&lt;");
          break;
        case '>':
          printf ("&gt;");
          break;
        case '"':
          printf ("&quot;");
          break;
        case '\'':
          printf ("&#39;");
          break;
        default:
          putchar (c);
        }
    }
  return 0;
}
