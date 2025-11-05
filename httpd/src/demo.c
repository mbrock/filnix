#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

int
main ()
{
  char *query = getenv ("QUERY_STRING");
  char *method = getenv ("REQUEST_METHOD");
  char *remote = getenv ("REMOTE_ADDR");

  /* Array to demonstrate bounds checking.  */
  const char *fruits[] = {
    "apple", "banana", "cherry", "date", "elderberry"
  };
  int num_fruits = 5;

  const char *div_style =
    "border: 2px solid #333; padding: 15px; margin: 20px 0; "
    "background: #f0f0f0;";
  const char *pre_style = "background: #fff; padding: 10px;";

  printf ("Content-Type: text/html; charset=utf-8\r\n\r\n");
  printf ("<html>\n");
  printf ("<head>\n");
  printf ("<meta charset=\"utf-8\">\n");
  printf ("<title>%s</title>\n", "Fil-C Memory Safety Demo");
  printf ("</head>\n");
  printf ("<body>\n");
  printf ("<h1>%s</h1>\n", "Memory Safety Interactive Demo");
  printf ("<p>%s</p>\n",
          "This CGI is written in C with Fil-C memory safety!");

  printf ("<h2>%s</h2>\n", "Test Array Bounds Checking");
  printf ("<p>We have an array of %d fruits. ", num_fruits);
  printf ("%s</p>\n", "Try accessing different indices:");
  printf ("<ul>\n");
  for (int i = 0; i < num_fruits; i++)
    printf ("<li><a href=\"?index=%d\">Index %d: %s</a></li>\n",
            i, i, fruits[i]);
  printf ("</ul>\n");

  printf ("<p><strong>%s</strong> ", "Try to break it:");
  printf ("<a href=\"?index=10\">%s</a> | ",
          "Access index 10 (out of bounds!)");
  printf ("<a href=\"?index=-1\">%s</a> | ",
          "Access index -1 (negative!)");
  printf ("<a href=\"?index=999\">%s</a></p>\n",
          "Access index 999 (way out!)");

  /* Parse and handle index parameter.  */
  if (query && strstr (query, "index=") == query)
    {
      int index = atoi (query + 6);
      printf ("<div style='%s'>\n", div_style);
      printf ("<h3>Result for index %d:</h3>\n", index);

      if (index >= 0 && index < num_fruits)
        {
          printf ("<p style='color: green;'>");
          printf ("<strong>✓ Safe access:</strong> ");
          printf ("fruits[%d] = \"%s\"</p>\n", index, fruits[index]);
        }
      else
        {
          printf ("<p style='color: orange;'>");
          printf ("<strong>⚠ Out of bounds attempt!</strong></p>\n");
          printf ("<p>Trying to access fruits[%d]...</p>\n", index);
          printf ("<p><em>%s ",
                  "In unsafe C, this would crash or return garbage.");
          printf ("%s</em></p>\n",
                  "With Fil-C, let's see what happens:");
          printf ("<pre style='%s'>", pre_style);

          /* This will trap with Fil-C's memory safety!  */
          const char *result = fruits[index];
          printf ("Value: %s\n", result);
          printf ("</pre>\n");
        }
      printf ("</div>\n");
    }

  printf ("<h2>%s</h2>\n", "Request Information:");
  printf ("<pre>\n");
  time_t now = time (NULL);
  printf ("Time: %s", ctime (&now));
  printf ("Query String: %s\n", query ? query : "(none)");
  printf ("Request Method: %s\n", method ? method : "unknown");
  printf ("Remote Address: %s\n", remote ? remote : "unknown");
  printf ("</pre>\n");
  printf ("<p><a href=\"hello.cgi\">← Back to main page</a></p>\n");
  printf ("</body>\n");
  printf ("</html>\n");

  return 0;
}
