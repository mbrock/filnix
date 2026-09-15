# AV1 decoder fixtures

These two single-frame lossless OBUs are generated test data, not downloaded
media. Each is a 16x16 YUV420 frame at 8 or 10 bits. The luma sample at `(x,y)`
is `(13*x + 7*y) * ((1 << bits) - 1) // 300`; U is `1 << (bits-2)` and V is
`3 << (bits-2)`. Ten-bit input uses little-endian 16-bit words.

Encode the raw planes with native FFmpeg/libaom:

```sh
ffmpeg -f rawvideo -pixel_format yuv420p -video_size 16x16 -framerate 1 \
  -i gradient-8.yuv -c:v libaom-av1 -cpu-used 8 -crf 0 -b:v 0 \
  -frames:v 1 -f obu gradient-8.obu
```

For the ten-bit fixture use `yuv420p10le`. The consumer compares all decoded
samples to the generating formula, exercising both portable C bit-depth paths.
