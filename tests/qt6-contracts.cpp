// Capability regressions for the Qt 6 representations changed by the port.
#include <QtCore>
#include <QtGui/QPainter>
#include <QtSvg/QSvgRenderer>
#include <array>
#include <unistd.h>

#define CHECK(cond)                                                            \
  do {                                                                         \
    if (!(cond)) {                                                             \
      fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);            \
      return 1;                                                                \
    }                                                                          \
  } while (0)

struct alignas(16) Item { int value; };
struct Large { std::array<int, 16> values; };
Q_DECLARE_METATYPE(Large)

int main(int argc, char **argv) {
  QCoreApplication app(argc, argv);
  CHECK(argc == 2);

  Item a{17}, b{93};
  QTaggedPointer<Item> tagged(&a, 3);
  CHECK(tagged->value == 17 && tagged.tag() == 3);
  tagged.setTag(12);
  auto copy = tagged;
  tagged = &b;
  CHECK(tagged->value == 93 && tagged.tag() == 12 && copy->value == 17);
  tagged = nullptr;
  CHECK(tagged.isNull() && tagged.tag() == 12);
  tagged.setTag(7);
  tagged = &a;
  CHECK(tagged->value == 17 && tagged.tag() == 7);
  QTaggedPointer<const Item> constant(&b, 5);
  CHECK(constant->value == 93 && constant.tag() == 5);

  QVariant small = QVariant::fromValue(&a);
  CHECK(small.value<Item *>()->value == 17);
  Large large{};
  large.values[3] = 61;
  large.values[15] = -29;
  QVariant shared = QVariant::fromValue(large), retained = shared;
  get_if<Large>(&shared)->values[3] = 88;
  CHECK(shared.value<Large>().values[3] == 88);
  CHECK(retained.value<Large>().values[3] == 61);
  CHECK(retained.value<Large>().values[15] == -29);
  // A unique large value reuses its shared allocation on emplace, rather
  // than taking the small-value or newly allocated metatype path.
  shared.emplace<Large>().values[6] = 127;
  CHECK(shared.value<Large>().values[6] == 127);
  CHECK(retained.value<Large>().values[15] == -29);
  shared.emplace<QString>(QStringLiteral("new type"));
  CHECK(shared.toString() == "new type");
  shared.emplace<int>(47);
  CHECK(shared.toInt() == 47);

  QReadWriteLock lock;
  {
    QReadLocker read(&lock);
    CHECK(read.readWriteLock() == &lock);
    read.unlock();
    CHECK(lock.tryLockForWrite());
    lock.unlock();
    read.relock();
    CHECK(!lock.tryLockForWrite());
  }
  {
    QWriteLocker write(&lock);
    write.unlock();
    CHECK(lock.tryLockForRead());
    lock.unlock();
    write.relock();
    CHECK(write.readWriteLock() == &lock && !lock.tryLockForRead());
  }
  QSemaphore semaphore;
  QThread *worker = QThread::create([&] { semaphore.acquire(2); });
  worker->start();
  QThread::msleep(30);
  semaphore.release(1);
  CHECK(!worker->wait(30));
  semaphore.release(2);
  CHECK(worker->wait(5000) && semaphore.available() == 1);
  delete worker;

  QProperty<int> input(7), bias(4), output;
  output.setBinding([&] { return input.value() * 3 + bias.value(); });
  CHECK(output.value() == 25);
  int notifications = 0;
  auto observer = output.onValueChanged([&] { ++notifications; });
  Qt::beginPropertyUpdateGroup();
  input = 11;
  bias = 8;
  CHECK(notifications == 0);
  Qt::endPropertyUpdateGroup();
  CHECK(output.value() == 41 && notifications == 1);
  auto binding = output.takeBinding();
  output = 9;
  input = 2;
  CHECK(output.value() == 9 && notifications == 2);
  output.setBinding(binding);
  CHECK(output.value() == 14 && notifications == 3);
  CHECK(qstricmp("AbC", "aBc") == 0);
  CHECK(qstricmp("abc", "ABd") < 0 && qstricmp("ABd", "abc") > 0);
  const char16_t utf16[] = { u'q', u'λ', u'\0' };
  CHECK(QStringView(utf16).size() == 2);
  CHECK(QStringView(utf16 + 1) == QString::fromUtf8("λ"));

  char bytes[] = "abc!";
  QByteArray raw = QByteArray::fromRawData(bytes, 3), detached = raw;
  detached[1] = 'Z';
  CHECK(raw.constData() == bytes && raw == "abc" && detached == "aZc" && bytes[1] == 'b');
  const QChar chars[] = { QChar('x'), QChar(0x03bb), QChar('!') };
  QString text = QString::fromRawData(chars, 2), owned = text;
  owned.append('z');
  CHECK(text.constData() == chars && text == QString::fromUtf8("xλ"));
  CHECK(owned == QString::fromUtf8("xλz"));

  // Source-over blending with partial alpha, an unaligned destination,
  // and rows that need both vector-sized blocks and a short tail.
  QImage source(19, 2, QImage::Format_ARGB32_Premultiplied);
  source.fill(qRgba(32, 64, 96, 128));
  QImage blended(31, 4, QImage::Format_ARGB32_Premultiplied);
  blended.fill(qRgb(16, 48, 80));
  QPainter blendPainter(&blended);
  blendPainter.drawImage(QPoint(3, 1), source);
  blendPainter.end();
  for (int y = 0; y < 4; ++y)
    for (int x = 0; x < 31; ++x) {
      const bool painted = y >= 1 && y < 3 && x >= 3 && x < 22;
      CHECK(blended.pixel(x, y) == (painted ? qRgb(40, 88, 136) : qRgb(16, 48, 80)));
    }

  QSvgRenderer svg(QByteArray(
      "<svg xmlns='http://www.w3.org/2000/svg' width='40' height='20'>"
      "<rect width='13' height='20' fill='#1256ab'/></svg>"));
  CHECK(svg.isValid());
  QImage rendered(40, 20, QImage::Format_ARGB32);
  rendered.fill(Qt::white);
  QPainter painter(&rendered);
  svg.render(&painter);
  painter.end();
  CHECK(rendered.pixel(5, 10) == qRgb(0x12, 0x56, 0xab));
  CHECK(rendered.pixel(30, 10) == qRgb(255, 255, 255));

  QPluginLoader loader(QString::fromLocal8Bit(argv[1]));
  CHECK(loader.metaData()["IID"].toString() == "org.filnix.Qt5Contracts");
  QObject *instance = loader.instance();
  CHECK(instance && instance->property("answer").toString() == "sectionless plugin");
  CHECK(loader.unload());

  QFile plugin(QString::fromLocal8Bit(argv[1]));
  CHECK(plugin.open(QIODevice::ReadOnly));
  QByteArray image = plugin.readAll();
  const QByteArray magic("QTMETADATA !");
  CHECK(image.contains(magic));
  image.replace(magic, QByteArray(magic.size(), '?'));
  QTemporaryDir dir;
  CHECK(dir.isValid());
  const qsizetype page = sysconf(_SC_PAGESIZE);
  CHECK(page > 0);
  // Put truncated metadata exactly at page-aligned EOF: mmap's zero-filled
  // tail must not hide an out-of-bounds read of the four-byte header.
  for (int headerBytes = 0; headerBytes < 4; ++headerBytes) {
    const QByteArray tail = magic + QByteArray(headerBytes, '\0');
    QByteArray malformed = image;
    const qsizetype end = ((image.size() + tail.size() + page - 1) / page) * page;
    malformed.append(QByteArray(end - image.size() - tail.size(), '\0'));
    malformed.append(tail);
    QFile file(dir.filePath(QString::number(headerBytes) + ".so"));
    CHECK(file.open(QIODevice::WriteOnly));
    CHECK(file.write(malformed) == malformed.size());
    file.close();
    QPluginLoader rejected(file.fileName());
    CHECK(rejected.metaData().isEmpty() && !rejected.errorString().isEmpty());
  }
  fprintf(stderr, "ok Qt6 pointer, variant, lock, semaphore, property, string, raw-data, SVG and plugin contracts\n");
}
