# ttyd Protocol & Architecture

## WebSocket Protocol

### Connection Setup
- **Subprotocol**: `'tty'` (required)
- **URL**: `ws[s]://host:port[/base-path]/ws`
- **Binary Mode**: `arraybuffer`

### Initial Handshake (Client → Server)
```javascript
const msg = JSON.stringify({
  AuthToken: token,  // empty string if no auth
  columns: term.cols,
  rows: term.rows
});
ws.send(textEncoder.encode(msg));
```

### Message Format
All messages prefixed with single-byte command character.

**Client Commands:**
- `'0'` INPUT - User keyboard/input data
- `'1'` RESIZE_TERMINAL - Terminal size change (deprecated, use JSON)
- `'2'` PAUSE - Flow control pause
- `'3'` RESUME - Flow control resume
- `'{'` JSON_DATA - JSON messages (handshake, resize)

**Server Commands:**
- `'0'` OUTPUT - Terminal output data
- `'1'` SET_WINDOW_TITLE - Browser title update
- `'2'` SET_PREFERENCES - Client configuration JSON

### Sending Input
```javascript
const payload = new Uint8Array(data.length + 1);
payload[0] = '0'.charCodeAt(0);
const encoded = textEncoder.encodeInto(data, payload.subarray(1));
ws.send(payload.subarray(0, encoded.written + 1));
```

### Receiving Output
```javascript
const cmd = String.fromCharCode(data[0]);
const payload = data.subarray(1);

if (cmd === '0') term.write(payload);
else if (cmd === '1') document.title = textDecoder.decode(payload);
else if (cmd === '2') applyPreferences(JSON.parse(textDecoder.decode(payload)));
```

## Backend (C/libwebsockets)

### Stack
- **libwebsockets 4.x** - HTTP/WS server
- **libuv** - Event loop, async I/O
- **pty** - Pseudoterminal, process spawning
- **json-c** - Config parsing

### Process Lifecycle
1. WS_ESTABLISHED → Check auth → Wait for handshake
2. Receive JSON handshake → Parse cols/rows → Spawn PTY process
3. PTY stdout → Prefix `'0'` → WS send
4. WS receive → Strip `'0'` → PTY stdin write
5. Process exit → WS close (1000=normal, 1006=error)

### PTY Callbacks
```c
process_read_cb(process, buf, eof) {
  ctx->pss->pty_buf = buf;
  lws_callback_on_writable(ctx->pss->wsi); // trigger WS send
}

process_exit_cb(process) {
  ctx->pss->lws_close_status = (exit_code == 0) ? 1000 : 1006;
  lws_callback_on_writable(ctx->pss->wsi);
}
```

### Flow Control
Server honors PAUSE/RESUME to prevent buffer overflow:
```c
case PAUSE: process->paused = true; break;
case RESUME: process->paused = false; drain_buffer(); break;
```

Client implements backpressure:
```javascript
written += data.length;
if (written > limit) {
  term.write(data, () => {
    if (--pending < lowWater) ws.send('3'); // RESUME
  });
  if (++pending > highWater) ws.send('2'); // PAUSE
}
```

## Frontend (TypeScript/Preact)

### Component Tree
```
App
└─ Terminal
   └─ Xterm
      ├─ FitAddon - Auto-resize to container
      ├─ WebglAddon/CanvasAddon - GPU rendering
      ├─ WebLinksAddon - Clickable URLs
      ├─ ImageAddon - Sixel graphics
      ├─ Unicode11Addon - Wide char support
      ├─ OverlayAddon - Status overlays
      └─ ZmodemAddon - File transfer (zmodem + trzsz)
```

### Init Sequence
1. Fetch `/token` → Extract auth token
2. Open terminal → Load addons
3. Connect WebSocket → Send handshake
4. Receive SET_WINDOW_TITLE, SET_PREFERENCES
5. Focus terminal, accept input

### Reconnection
```javascript
ws.onclose = (event) => {
  if (event.code !== 1000 && doReconnect) {
    refreshToken().then(connect); // auto-reconnect
  } else {
    term.onKey(e => { if (e.key === 'Enter') connect(); }); // manual
  }
};
```

## File Transfer

### Protocols
- **Zmodem** - Legacy (rz/sz), detects `**\x18B0...` magic bytes
- **Trzsz** - Modern, detects `::TRZSZ:TRANSFER:...`, supports drag-drop

### Flow
1. Detect magic sequence in terminal output
2. Pause terminal stdin, disable input
3. Show file picker (upload) or save dialog (download)
4. Binary transfer over WebSocket (bypasses terminal layer)
5. Resume terminal on completion

### Trzsz Features
- Progress bars with speed/ETA
- Checksums (MD5 verification)
- Directory upload/download
- Drag-drop to browser terminal
- Better handling of poor connections

## Server CLI Options

### Auth
- `-c user:pass` - Basic auth
- `-H X-User` - Reverse proxy header
- Token endpoint `/token` for dynamic auth

### Network
- `-p 7681` - Port (0 = random)
- `-i eth0` - Interface or UNIX socket path
- `-b /prefix` - Base path for reverse proxy
- `-S` - SSL mode (`-C cert.pem -K key.pem`)
- `-6` - Enable IPv6

### Terminal
- `-W` - Writable (allow input, default read-only)
- `-T xterm-256color` - TERM variable
- `-t key=value` - Client option (fontSize=16, etc)
- `-a` - Allow URL args (?arg=foo)

### Process
- `-s N` - Signal on disconnect (default SIGHUP)
- `-w /path` - Working directory
- `-u uid -g gid` - Run as user/group

### Limits
- `-m N` - Max clients
- `-o` - Once (exit after first client)
- `-q` - Exit when no clients connected
- `-O` - Check Origin header

### Custom
- `-I /path/index.html` - Custom frontend

## Client URL Options

Set via query params: `?fontSize=16&enableZmodem=1`

- `rendererType=webgl|canvas|dom` - Renderer
- `disableLeaveAlert=1` - No exit confirmation
- `disableResizeOverlay=1` - Hide resize indicator
- `disableReconnect=1` - No auto-reconnect
- `enableZmodem=1` - rz/sz support
- `enableTrzsz=1` - Modern file transfer
- `enableSixel=1` - Graphics
- `isWindows=1` - CRLF mode
- `titleFixed=Title` - Lock title
- Plus all xterm.js options (fontSize, fontFamily, theme, etc)

## Performance

### Backend
- libuv async I/O (non-blocking PTY)
- libwebsockets permessage-deflate compression
- Buffer pooling, zero-copy where possible
- Backpressure via PAUSE/RESUME

### Frontend
- WebGL rendering (GPU-accelerated)
- Virtual scrollback (render only visible)
- Write batching/throttling
- Binary WebSocket (no UTF-8 overhead)

## Security

- Origin check: validates WSI_TOKEN_ORIGIN vs WSI_TOKEN_HOST
- Read-only default: `-W` required for input
- Auth required: blocks unauthenticated if `-c` set
- Signal on disconnect: SIGHUP kills shell session
- Max clients: prevents connection DoS
- Custom index: validated path, no directory traversal

## Build

### Frontend (`html/`)
```bash
cd html
yarn install
yarn build  # webpack → dist/index.html
```
Output embedded in C: `xxd -i dist/index.html > html.h`

### Backend (`src/`)
```bash
cmake -B build
cmake --build build
```
Dependencies: libwebsockets ≥4.0, json-c, libuv, openssl (optional)
Result: Single `ttyd` binary with embedded HTML

## Common Patterns

**Reverse proxy:**
```bash
ttyd -b /terminal -W bash
# nginx: proxy_pass http://localhost:7681/terminal/
```

**Read-only demo:**
```bash
ttyd -m 50 htop
```

**Secure shell:**
```bash
ttyd -S -C cert.pem -K key.pem -c admin:pass -W bash
```

**One-shot session:**
```bash
ttyd -o -W bash  # exit after disconnect
```

**Custom frontend:**
```bash
ttyd -I custom.html bash  # must implement protocol
```
