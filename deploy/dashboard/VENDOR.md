# Browser assets

The Tagflow example at aa07b0d7eec0b72a5dbc6a8d0ee1098c68b74d09 vendors
htmx.org 4.0.0 from jsDelivr (`dist/htmx.min.js` and
`dist/ext/hx-sse.min.js`). Those files and HTMX-LICENSE are copied into
`experiment/dashboard/static`. Tailwind 4.3.3 is locked in package-lock.json;
its checked-in generated CSS retains the MIT banner.

Filnix applies one owned change to hx-sse 4.0.0. In both cleanup and the
background-visibility handler, consume the promise rejection from
`reader.cancel()`. Cleanup already aborts the fetch and disposes the reader;
cancelling its aborted stream can reject with AbortError. The original code
leaves that promise unhandled on navigation and on the completion event.
Consuming this cleanup promise does not change active read-error reporting,
reconnection, event delivery or rendering. It does not suppress global errors.

Original hx-sse SHA-256: `8a834680c4000a9034d79228872372a92e140c810a075cb6d4a76690dfc13085`.
Reapply or remove this small change intentionally when updating the vendor.
The browser regression asserts no uncaught exceptions across navigation,
completion and failed/slow cursor requests.
