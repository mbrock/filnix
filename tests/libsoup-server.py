from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        expected = None if self.path == '/plain' else 'filnix=42'
        self.send_response(200 if self.headers.get('Cookie') == expected else 400)
        self.send_header('Content-Length', '6')
        self.end_headers()
        self.wfile.write(b'filnix')


with HTTPServer(('127.0.0.1', 0), Handler) as server:
    Path('port').write_text(str(server.server_port))
    server.serve_forever()
