# Parse query string for text parameter
TEXT=$(parse-query text)
[ -z "$TEXT" ] && TEXT="Fil-C"

# Escape for safe HTML output using Fil-C program
TEXT_ESCAPED=$(echo "$TEXT" | html-escape)

cat <<EOF
Content-Type: text/html; charset=utf-8

EOF

cat <<'HEADER'
<html>
<head>
<meta charset="utf-8">
<title>Figlet Font Gallery</title>
<link rel="stylesheet" href="style.css">
</head>
<body>
HEADER

printf '<form method="get">\n'
printf '  <input type="text" id="text" name="text" value="%s">\n' "$TEXT_ESCAPED"
printf '  <input type="submit" value="Render">\n'
printf '</form>\n'
printf '<div class="font-gallery">\n'

# Get all fonts and render each one
figlist | while read -r font; do
  # Try to render font - if it fails, skip to next
  if ! figlet -f "$font" "$TEXT" >/dev/null 2>&1; then
    continue
  fi

  echo "<div class='font-sample'>"
  echo "<div class='font-name'>$(echo "$font" | html-escape)</div>"
  echo "<pre>"
  # Render, strip trailing blanks, HTML-escape
  figlet -f "$font" "$TEXT" 2>/dev/null | \
    sed ':a; /^[[:space:]]*$/ { N; s/\n[[:space:]]*$//; ta; }' | \
    html-escape
  echo "</pre>"
  echo "</div>"
done

printf '</div>\n'

cat <<EOF
<p><a href="hello.cgi" class="back">← Back to main page</a></p>
</body>
</html>
EOF
