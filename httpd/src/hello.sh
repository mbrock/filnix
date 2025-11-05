cat <<EOF
Content-Type: text/html

<html>
<head><title>Fil-C Lighttpd Demo</title></head>
<body>
<h1>Hello from Memory-Safe Lighttpd!</h1>
<p>This web server is built with Fil-C for complete memory safety.</p>
<h2>Features enabled:</h2>
<ul>
  <li>Compression: brotli, zstd, bzip2, gzip</li>
  <li><a href="/dav/">WebDAV</a> with digest authentication (user: demo / pass: demo)</li>
  <li>Lua scripting (mod_magnet)</li>
  <li>Kerberos authentication</li>
</ul>
<h2>CGI Demos:</h2>
<ul>
  <li><a href="hello.cgi">Bash CGI (this page)</a></li>
  <li><a href="demo.cgi">C CGI with memory safety</a></li>
  <li><a href="figlet.cgi">Figlet Font Gallery (streaming)</a></li>
</ul>
<h2>Request info:</h2>
<pre>
Server: $(uname -a)
Time: $(date)
Query: $QUERY_STRING
Request Method: $REQUEST_METHOD
Remote Addr: $REMOTE_ADDR
</pre>
</body>
</html>
EOF
