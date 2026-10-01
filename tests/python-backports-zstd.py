"""Boundary regressions, collected alongside backports-zstd's upstream tests."""

import random
import unittest

from backports import zstd


class TestFilcBoundaries(unittest.TestCase):
    def test_roundtrip_boundaries(self):
        # Both sides of the initial 32 KiB output buffer and zstd's 128 KiB
        # block boundary. Incompressible bytes exercise output buffer growth;
        # repeated bytes exercise large output from small compressed input.
        rng = random.Random(812)
        for size in (0, 1, 32767, 32768, 32769, 131071, 131072, 131073):
            for data in (rng.randbytes(size), b"a" * size):
                with self.subTest(size=size, repeated=data == b"a" * size):
                    frame = zstd.compress(data)
                    self.assertEqual(zstd.decompress(frame), data)
                    self.assertEqual(zstd.get_frame_size(frame), len(frame))
                    self.assertEqual(zstd.get_frame_info(frame).decompressed_size, size)

                    compressor = zstd.ZstdCompressor()
                    chunks = [compressor.compress(data[i:i + 8191])
                              for i in range(0, size, 8191)]
                    chunks.append(compressor.flush(zstd.ZstdCompressor.FLUSH_FRAME))
                    self.assertEqual(zstd.decompress(b"".join(chunks)), data)

    def test_output_limit_and_frame_boundary(self):
        data = random.Random(931).randbytes(131073)
        frame = zstd.compress(data)
        next_frame = zstd.compress(b"second frame\x00\xff")
        for limit in (0, 1, 32767, 32768, 32769, len(data) - 1, len(data), len(data) + 1):
            with self.subTest(limit=limit):
                decoder = zstd.ZstdDecompressor()
                first = decoder.decompress(frame + next_frame, max_length=limit)
                self.assertEqual(first, data[:limit])
                if limit < len(data):
                    self.assertFalse(decoder.eof)
                    self.assertFalse(decoder.needs_input)
                    self.assertEqual(decoder.decompress(b""), data[limit:])
                self.assertTrue(decoder.eof)
                self.assertEqual(decoder.unused_data, next_frame)
        self.assertEqual(zstd.decompress(frame + next_frame), data + b"second frame\x00\xff")

    def test_truncated_and_invalid_input(self):
        frame = zstd.compress(b"boundary\x00\xff" * 4097)
        for invalid in (b"", frame[:1], frame[:-1], b"not a zstd frame"):
            with self.subTest(size=len(invalid)):
                with self.assertRaises(zstd.ZstdError):
                    zstd.decompress(invalid)


if __name__ == "__main__":
    unittest.main()
