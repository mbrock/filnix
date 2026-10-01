// Hardware AES hashing must read only the supplied object, not its cacheline.
#include <QtCore>
#include <private/qsimd_p.h>
#include <array>
#include <memory>

#define CHECK(cond) do { if (!(cond)) { \
  fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond); return 1; \
} } while (0)

int main() {
  CHECK(qEnvironmentVariable("QT_HASH_SEED") == "0");
  CHECK(size_t(QHashSeed::globalSeed()) == 0);
  const auto features = qCpuFeatures();
  if (!qCpuHasFeature(AES) || !qCpuHasFeature(SSE4_2)) {
    fprintf(stderr, "SKIP Qt6 AES hash: CPU lacks AES/SSE4.2\n");
    return 0;
  }
  constexpr size_t seed = 0x123456789abcdef1;
  // Golden values from unmodified native Qt 6.11.2 on padded input, with
  // QT_HASH_SEED=0 (secondary seed zero) and the same nonzero explicit seed.
  // They catch accidental fallback, wrong masking, and wrong Latin-1 expansion.
  const size_t bytesExpected[] = {
    0x1a1f902548d2e3dc, 0xcb59f068b311fe47, 0xdc606d44dbf4424a, 0xaa4b040ea20da1ec,
    0x4b739c6ee5939d6f, 0x8dd8cd57b7974918, 0xaddc943b37d2f700, 0xa5b19d795b77101c,
    0xd0d2c8120af0453b, 0xc912fc7f18b661ef, 0x9a77215b65274dc4, 0xe59b0f1ada1c15f7,
    0xa306f08c687037d7, 0x9d2493fdded94b37, 0x644d9b4a6a81a5f6, 0xee2e11ec9e2aff6e
  };
  const size_t textExpected[] = {
    0x1a1f902548d2e3dc, 0xcb59f068b311fe47, 0x7d9672262f2d68f0, 0xe4131a33bc597a98,
    0xf30d223e0d0572a5, 0x80f5da814c422075, 0x72ece2b444387c58, 0xb93f8ac8415632c9
  };
  alignas(64) static const char16_t shortGlobal[] = {11, 40, 69, 98};
  alignas(64) unsigned char padded[128];
  for (auto &b : padded) b = 0xe7;

  // Select both original short-load dispatches, without disabling AES itself.
  // QT_NO_CPU_FEATURE cannot select them reliably in Qt 6.11.2: its generated
  // feature names include leading spaces but its parser strips those spaces.
  for (const auto disabled : std::array<QCpuFeatureType, 2>{
      CpuFeatureAVX512VL, CpuFeatureAVX512VL | CpuFeatureVAES}) {
    qt_cpu_features[0].store(features & ~disabled, std::memory_order_relaxed);
    CHECK(qCpuHasFeature(AES) && qCpuHasFeature(SSE4_2));
    CHECK(!qCpuHasFeature(AVX512VL));
    if (disabled & CpuFeatureVAES) CHECK(!qCpuHasFeature(VAES));
    CHECK(qHash(QStringView(shortGlobal, 4), seed) == textExpected[4]);
    CHECK(qHashBits(nullptr, 0, seed) == bytesExpected[0]);
    for (int n = 1; n < 16; ++n) {
      auto exact = std::make_unique<unsigned char[]>(n);
      for (int i = 0; i < n; ++i) exact[i] = (i * 29 + 11) & 255;
      CHECK(qHashBits(exact.get(), n, seed) == bytesExpected[n]);
      // Exercise both cacheline halves and unaligned positions. Poison bytes
      // before/after the view must not influence the result.
      for (int offset : {0, 1, 31, 32, 33, 63}) {
        memcpy(padded + offset, exact.get(), n);
        CHECK(qHashBits(padded + offset, n, seed) == bytesExpected[n]);
        memset(padded, 0xe7, sizeof(padded));
      }
    }
    for (int n = 0; n < 8; ++n) {
      auto latin = std::make_unique<char[]>(n);
      auto utf16 = std::make_unique<char16_t[]>(n);
      for (int i = 0; i < n; ++i) {
        latin[i] = char((i * 29 + 11) & 255);
        utf16[i] = (i * 29 + 11) & 255;
      }
      CHECK(qHash(QLatin1StringView(latin.get(), n), seed) == textExpected[n]);
      CHECK(qHash(QStringView(utf16.get(), n), seed) == textExpected[n]);
    }
    // Around the full-block boundary, exact-sized and padded storage agree.
    for (int n : {16, 17, 31, 32, 33, 65}) {
      auto exact = std::make_unique<unsigned char[]>(n);
      for (int i = 0; i < n; ++i) exact[i] = (i * 29 + 11) & 255;
      memcpy(padded + 33, exact.get(), n);
      CHECK(qHashBits(exact.get(), n, seed) == qHashBits(padded + 33, n, seed));
      memset(padded, 0xe7, sizeof(padded));
    }
    fprintf(stderr, "ok Qt6 %s hash: bounded global/heap, bytes 0..15, Latin-1/UTF16 0..7, cacheline offsets and full-block boundaries\n",
      qCpuHasFeature(VAES) ? "VAES256" : "AES128");
  }
  qt_cpu_features[0].store(features, std::memory_order_relaxed);
}
