// Regression tests for the Fil-C Qt5 raw-data, metadata and QV4 ports.
#include <QtCore>
#include <cmath>
#include <cstdint>
#include <limits>
#include <type_traits>
#include <utility>
#include <vector>
#include <unistd.h>

#ifdef WITH_QML
#include <QtQml>
#include <private/qjsvalue_p.h>
#include <private/qv4persistent_p.h>
#include <private/qv4propertykey_p.h>

static_assert(sizeof(QV4::ReturnedValue) == 8, "ReturnedValue ABI");
static_assert(sizeof(QV4::StaticValue) == 8, "StaticValue ABI");
static_assert(sizeof(QV4::Value) == 8, "Value ABI");
static_assert(sizeof(QV4::PropertyKey) == 8, "PropertyKey ABI");
static_assert(sizeof(QJSValue) == 8, "QJSValue ABI");
static_assert(std::is_trivially_copyable<QV4::ReturnedValue>::value, "value copies");
static_assert(std::is_trivially_copyable<QV4::StaticValue>::value, "static copies");
static_assert(std::is_trivially_copyable<QV4::Value>::value, "heap value copies");
static_assert(std::is_trivially_copyable<QV4::PropertyKey>::value, "key copies");
#endif

#define CHECK(cond)                                                            \
  do {                                                                         \
    if (!(cond)) {                                                             \
      fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);            \
      return 1;                                                                \
    }                                                                          \
  } while (0)

static int rawData() {
  // Both aligned and offset pointers have a deliberately nonzero low byte:
  // treating their stored bytes as empty contents must not accidentally pass.
  alignas(256) char bytes[512] = {};
  alignas(256) QChar chars[256] = {};
  for (int offset : {1, 16}) {
    char *p = bytes + offset;
    CHECK((reinterpret_cast<uintptr_t>(p) & 255) != 0);
    memcpy(p, "abc!", 4);
    QByteArray raw = QByteArray::fromRawData(p, 3);
    CHECK(raw.constData() == p && raw == "abc" && !raw.isNull());
    for (int cycle = 0; cycle < 3; ++cycle) {
      raw.setRawData(nullptr, 0);
      CHECK(raw.isEmpty() && !raw.isNull() && raw.constData()[0] == '\0');
      raw.setRawData(p, 3);
      CHECK(raw.constData() == p && raw == "abc");
    }
    raw.setRawData(p, 0);
    CHECK(raw.isEmpty() && !raw.isNull() && raw.constData() == p);
    raw.setRawData(nullptr, 0);
    CHECK(!raw.isNull() && raw.constData()[0] == '\0');
    raw.setRawData(p, 3);
    QByteArray copy = raw;
    copy[1] = 'Z'; // Detach, do not change the caller's buffer or raw's pointer.
    CHECK(copy == "aZc" && raw == "abc" && p[1] == 'b');
    raw.append('d');
    CHECK(raw == "abcd" && raw.constData()[4] == '\0' && p[3] == '!');
    raw.setRawData(p, 3);
    raw.setRawData(nullptr, 0);
    raw.append('q');
    CHECK(raw == "q" && raw.constData()[1] == '\0');
    QByteArray shared = QByteArray::fromRawData(p, 3), retained = shared;
    shared.setRawData(nullptr, 0);
    CHECK(shared.isNull() && shared.constData()[0] == '\0');
    CHECK(retained.constData() == p && retained == "abc");
    CHECK(QByteArray::fromRawData(nullptr, 0).isNull());
    QByteArray empty = QByteArray::fromRawData(p, 0);
    CHECK(empty.isEmpty() && !empty.isNull() && empty.constData()[0] == '\0');
    empty.setRawData(nullptr, 0);
    CHECK(empty.isNull() && empty.constData()[0] == '\0');
  }
  for (int offset : {1, 8}) {
    QChar *p = chars + offset;
    CHECK((reinterpret_cast<uintptr_t>(p) & 255) != 0);
    p[0] = QChar('a'); p[1] = QChar(0x03bb); p[2] = QChar('c'); p[3] = QChar('!');
    const QString expected = QString::fromUtf8("aλc");
    QString raw = QString::fromRawData(p, 3);
    CHECK(raw.constData() == p && raw == expected && !raw.isNull());
    for (int cycle = 0; cycle < 3; ++cycle) {
      raw.setRawData(nullptr, 0);
      CHECK(raw.isEmpty() && !raw.isNull() && raw.constData()[0].unicode() == 0);
      CHECK(raw.utf16()[0] == 0);
      raw.setRawData(p, 3);
      CHECK(raw.constData() == p && raw == expected);
    }
    raw.setRawData(p, 0);
    CHECK(raw.isEmpty() && !raw.isNull() && raw.constData() == p);
    raw.setRawData(nullptr, 0);
    CHECK(!raw.isNull() && raw.constData()[0].unicode() == 0);
    raw.setRawData(p, 3);
    QString copy = raw;
    copy[1] = QChar('Z');
    CHECK(copy == "aZc" && raw == expected && p[1].unicode() == 0x03bb);
    raw.append('d');
    CHECK(raw == expected + 'd' && raw.constData()[4].unicode() == 0 && p[3] == '!');
    raw.setRawData(p, 3);
    raw.setRawData(nullptr, 0);
    raw.append('q');
    CHECK(raw == "q" && raw.constData()[1].unicode() == 0);
    QString shared = QString::fromRawData(p, 3), retained = shared;
    shared.setRawData(nullptr, 0);
    CHECK(shared.isNull() && shared.constData()[0].unicode() == 0);
    CHECK(retained.constData() == p && retained == expected);
    CHECK(QString::fromRawData(nullptr, 0).isNull());
    QString empty = QString::fromRawData(p, 0);
    CHECK(empty.isEmpty() && !empty.isNull() && empty.constData()[0].unicode() == 0);
    empty.setRawData(nullptr, 0);
    CHECK(empty.isNull() && empty.constData()[0].unicode() == 0);
  }
  fprintf(stderr, "ok raw-data aligned/offset/null/empty/reuse/append/detach\n");
  return 0;
}

static int metadata(const QString &pluginPath) {
  QPluginLoader valid(pluginPath);
  CHECK(valid.metaData().value("IID").toString() == "org.filnix.Qt5Contracts");
  QObject *instance = valid.instance();
  CHECK(instance && instance->property("answer").toString() == "sectionless plugin");
  QFile original(pluginPath);
  CHECK(original.open(QIODevice::ReadOnly));
  const QByteArray elf = original.readAll();
  CHECK(elf.contains("QTMETADATA !"));
  QTemporaryDir dir;
  CHECK(dir.isValid());
  // Positive controls at the exact EOF boundary for both metadata formats.
  QCborMap cbor;
  cbor.insert(2, QStringLiteral("org.filnix.Qt5Contracts"));
  const QList<QByteArray> goodTails = {
      QByteArray("QTMETADATA !") + QByteArray::fromHex("00050f00") + QCborValue(cbor).toCbor(),
      QByteArray("QTMETADATA  ") + QJsonDocument(valid.metaData()).toBinaryData()};
  for (int i = 0; i < goodTails.size(); ++i) {
    const QString path = dir.filePath(QString("valid-%1.so").arg(i));
    QFile file(path);
    CHECK(file.open(QIODevice::WriteOnly));
    CHECK(file.write(elf + goodTails[i]) == elf.size() + goodTails[i].size());
    file.close();
    QPluginLoader loader(path);
    CHECK(loader.metaData().value("IID").toString() == "org.filnix.Qt5Contracts");
  }
  QList<QByteArray> tails;
  tails << QByteArray("QTMETADATA ") // Marker only: missing the format byte.
        << QByteArray("QTMETADATA ?"); // Complete but invalid signature.
  for (int n = 0; n < 4; ++n)
    tails << QByteArray("QTMETADATA !") + QByteArray(n, '\0');
  for (int n = 0; n < 12; ++n)
    tails << QByteArray("QTMETADATA  ") + QByteArray("qbjs\1\0\0\0\0\0\0\0", n);
  // Full legacy header, declared length beyond the remaining file, then
  // beyond the 128 MB limit; CBOR also declares an unavailable huge string.
  tails << QByteArray("QTMETADATA  ") + QByteArray::fromHex("71626a730100000040000000")
        << QByteArray("QTMETADATA  ") + QByteArray::fromHex("71626a7301000000ffffffff")
        << QByteArray("QTMETADATA !") + QByteArray::fromHex("00050f00a1017a7fffffff");
  int index = 0;
  const long pageSize = sysconf(_SC_PAGESIZE);
  CHECK(pageSize > 0);
  for (const QByteArray &tail : tails) {
    const QString path = dir.filePath(QString("decoy-%1.so").arg(index++));
    QFile malformed(path);
    CHECK(malformed.open(QIODevice::WriteOnly));
    // Place EOF at a page boundary too, so mmap's rounding cannot hide an
    // overread of a truncated header in accessible zero-filled page slack.
    const int padding = (pageSize - (elf.size() + tail.size()) % pageSize) % pageSize;
    const QByteArray prefix = elf + QByteArray(padding, '\0');
    CHECK(malformed.write(prefix) == prefix.size());
    CHECK(malformed.write(tail) == tail.size());
    malformed.close();
    // All files remain valid ELF and contain genuine earlier metadata.
    // The backward search chooses the later decoy, which must be rejected
    // normally, not read with the whole file's length or loaded as a plugin.
    QPluginLoader rejected(path);
    CHECK(rejected.metaData().isEmpty());
    CHECK(rejected.errorString().contains("Failed to extract plugin meta data"));
    CHECK(!rejected.load() && !rejected.instance());
  }
  fprintf(stderr, "ok metadata sectionless plugin and %d EOF/length/decoy rejections\n", index);
  return 0;
}

#ifdef WITH_QML
static int values() {
  QJSEngine engine;
  const double numbers[] = {-2147483649.0, -2147483648.0, -2147483647.0,
                            2147483646.0, 2147483647.0, 2147483648.0,
                            4294967295.0, 4294967296.0,
                            -9007199254740991.0, 9007199254740991.0,
                            -0.0, 0.0, 0.125, -0.125,
                            std::numeric_limits<double>::denorm_min(),
                            std::numeric_limits<double>::max(),
                            std::numeric_limits<double>::infinity(),
                            -std::numeric_limits<double>::infinity(),
                            std::numeric_limits<double>::quiet_NaN()};
  QJSValue identity = engine.evaluate("(function(x) { return x; })");
  QJSValue increment = engine.evaluate("(function(x) { return x + 1; })");
  for (double n : numbers) {
    QJSValue input(n), result = identity.call({input});
    CHECK(result.isNumber() && !result.isObject());
    double actual = result.toNumber();
    CHECK(std::isnan(n) ? std::isnan(actual) : actual == n);
    if (n == 0) CHECK(std::signbit(actual) == std::signbit(n));
    QJSValue sum = increment.call({input});
    CHECK(sum.isNumber());
    CHECK(std::isnan(n) ? std::isnan(sum.toNumber()) : sum.toNumber() == n + 1);
  }
  QJSValue boundary = engine.evaluate(R"JS(
    [2147483647 + 1, -2147483648 - 1, 4294967295 >>> 0, 4294967296 >>> 0,
     2147483648 | 0, 1 / -0, Object.is(-0, 0), NaN === NaN,
     Number.isNaN(0/0), Math.sign(-0)].map(String).join('|')
  )JS");
  CHECK(!boundary.isError());
  CHECK(boundary.toString() == "2147483648|-2147483649|4294967295|0|-2147483648|-Infinity|false|false|true|0");
  CHECK(std::signbit(engine.evaluate("Math.sign(-0)").toNumber()));
  // Exercise immediate/managed transitions in a reused slot and a JS array.
  QJSValue transitions = engine.evaluate(R"JS(
    (function() {
      var a = [{x:17}, -0, NaN, undefined, null, true, 2147483648, 'heap string'];
      for (var i=0; i<1003; ++i) {
        var v = a[0]; a.push(v); a.shift();
      }
      return a.length === 8 && a.some(function(v) { return v && v.x === 17; })
        && a.some(function(v) { return Object.is(v, -0); })
        && a.some(Number.isNaN) && a.indexOf('heap string') !== -1;
    })()
  )JS");
  CHECK(!transitions.isError() && transitions.toBool());

  // No global JS reference: C++ persistent handles must keep the entire
  // graph alive. Allocate enough handles to cross several 4 KB pages.
  QJSValue object = engine.evaluate("({n:73, child:{s:'retained'}, self:null})");
  object.setProperty("self", object);
  QJSValue copied(object), moved(std::move(copied)), assigned, moveAssigned;
  CHECK(copied.isUndefined());
  QJSValue previous = engine.evaluate("({n:-19})");
  assigned = previous;
  assigned = moved;
  moveAssigned = previous;
  moveAssigned = std::move(assigned);
  CHECK(assigned.strictlyEquals(previous)); // Qt's move assignment swaps.
  std::vector<QJSValue> roots;
  for (int i = 0; i < 1500; ++i) {
    QJSValue root = engine.newObject();
    root.setProperty("index", i);
    root.setProperty("graph", object);
    roots.push_back(std::move(root));
  }
  QV4::Value *value = QJSValuePrivate::getValue(&object);
  CHECK(value && value->isObject());
  QV4::PersistentValue persistent(engine.handle(), *value);
  QV4::PersistentValue persistentCopy(persistent), persistentAssigned;
  persistentAssigned = persistentCopy;
  // PersistentValue has no special move overload: rvalues use its copy API.
  QV4::PersistentValue persistentMoved(std::move(persistentCopy));
  persistentAssigned.set(engine.handle(), *QJSValuePrivate::getValue(&previous));
  persistentAssigned = std::move(persistentMoved);
  persistent.clear();
  object = QJSValue();
  for (int round = 0; round < 3; ++round) {
    CHECK(!engine.evaluate("for(var i=0;i<20000;++i) ({i:i,s:'garbage'+i});").isError());
    engine.collectGarbage();
    CHECK(moved.strictlyEquals(moveAssigned));
    CHECK(moved.property("n").toInt() == 73 && assigned.property("n").toInt() == -19);
    CHECK(moved.property("self").strictlyEquals(moved));
    CHECK(moved.property("child").property("s").toString() == "retained");
    CHECK(QJSValue(engine.handle(), persistentAssigned.value()).strictlyEquals(moved));
    CHECK(persistentAssigned.engine() == engine.handle());
    for (int i = 0; i < int(roots.size()); ++i) {
      CHECK(roots[i].property("index").toInt() == i);
      CHECK(roots[i].property("graph").strictlyEquals(moved));
    }
  }
  // Retain Symbols, interned strings and sparse index keys over GC too.
  QJSValue keys = engine.evaluate(R"JS(
    (function() {
      var s = Symbol('key'), t = Symbol('key'), o = {}, a = [];
      o[s]=11; o[t]=22; o.key=33; o['__proto__']=null;
      a[3]=o; a[65537]='middle'; a[4294967294]='last';
      a[4294967295]='not-an-index'; a['01']='leading-zero';
      delete a[65537]; a[1048577]='replacement';
      return function() {
        return o[s]===11 && o[t]===22 && o.key===33 && s!==t
          && Object.getOwnPropertySymbols(o).length===2
          && a.length===4294967295 && a[3]===o && !(65537 in a)
          && a[1048577]==='replacement' && a[4294967294]==='last'
          && a['4294967295']==='not-an-index' && a['01']==='leading-zero'
          && Object.keys(a).join(',')==='3,1048577,4294967294,4294967295,01';
      };
    })()
  )JS");
  CHECK(!keys.isError() && keys.isCallable());
  engine.collectGarbage();
  QJSValue keyResult = keys.call();
  CHECK(!keyResult.isError() && keyResult.toBool());
  fprintf(stderr, "ok QV4 numeric/tags/GC/identity/Symbol/string/sparse/persistent copies and moves\n");
  return 0;
}
#endif

int main(int argc, char **argv) {
  QCoreApplication app(argc, argv);
  CHECK(argc == 2 || argc == 3);
  const QByteArray only = argc == 3 ? argv[2] : "";
  CHECK(only.isEmpty() || only == "raw-data" || only == "metadata" || only == "values");
  if ((only.isEmpty() || only == "raw-data") && rawData()) return 1;
  if ((only.isEmpty() || only == "metadata") && metadata(QString::fromLocal8Bit(argv[1]))) return 1;
#ifdef WITH_QML
  if ((only.isEmpty() || only == "values") && values()) return 1;
#else
  CHECK(only != "values");
#endif
  return 0;
}
