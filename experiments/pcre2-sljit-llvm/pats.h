static const char html[] =
    "<div class=\"entry-content\" id=\"post-1234\">\n"
    "<p>Hello <a href=\"https://example.com/wp-content/uploads/2026/11/photo-300x200.jpg\" "
    "title=\"A photo\">world</a>, written on 2026-11-09 by admin@example.com and "
    "editor_2@wordpress.com.</p>\n"
    "<img src=\"/wp-content/uploads/img_0042.png\" alt=\"\" width=\"640\" height=\"480\" />\n"
    "[gallery ids=\"12,34,56\" columns=\"3\"] some text here with the quick brown fox "
    "jumps over the lazy dog foobarbaz123 and more words follow after that one;\n"
    "<!-- wp:paragraph {\"align\":\"center\"} --><p class=\"has-text-align-center\">"
    "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor "
    "incididunt ut labore et dolore magna aliqua.</p><!-- /wp:paragraph -->\n"
    "<script type=\"text/javascript\">var x = 1 &amp; 2;</script> &nbsp; &#8217; &hellip;\n";

struct pat {
    const char *name;
    const char *re;
    uint32_t opts;
    const char *subject; /* NULL = repeated html */
};

static const struct pat pats[] = {
    { "tag", "<(/?)([a-z][a-z0-9]*)((?:\\s+[a-z-]+(?:=\"[^\"]*\")?)*)\\s*(/?)>", PCRE2_CASELESS, NULL },
    { "email", "\\b([\\w.]+)@(\\w+)\\.com\\b", 0, NULL },
    { "word", "[^\\s<>]+", 0, NULL },
    { "alt", "(?:foo|bar|baz|quick|lazy)+\\d*", 0, NULL },
    { "entity", "&(?:#\\d+|#x[0-9a-f]+|[a-z]+);", PCRE2_CASELESS, NULL },
    { "shortcode", "\\[(\\[?)(gallery|caption|embed)(?![\\w-])([^\\]/]*(?:/(?!\\])[^\\]/]*)*?)(?:(/)\\]|\\])", 0, NULL },
    { "key", "^[a-z0-9_\\-]+$", PCRE2_CASELESS, "wp_template_part-area_42" },
    { "date", "^\\s*(\\d{4})-(\\d{2})-(\\d{2})\\s*$", 0, "  2026-11-09 " },
    { "utf", "\\p{Lu}\\p{Ll}+", PCRE2_UTF | PCRE2_UCP, NULL },
    { "lit", "consectetur", 0, NULL },
};
