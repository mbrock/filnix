// Qt 5 SVG, QML/JavaScript and Qt Quick under Fil-C. Qt Quick renders
// with its software backend (QT_QUICK_BACKEND=software) on the offscreen
// or xcb platform.
#include <QtCore>
#include <QtGui>
#include <QtQml>
#include <QtQuick>
#include <QtSvg>

#define CHECK(cond)                                                          \
  do {                                                                       \
    if (!(cond)) {                                                           \
      fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);        \
      return 1;                                                              \
    }                                                                        \
  } while (0)

class Backend : public QObject {
  Q_OBJECT
  Q_PROPERTY(QString greeting READ greeting CONSTANT)
public:
  QString greeting() const { return QStringLiteral("hello"); }
  Q_INVOKABLE int twice(int x) const { return 2 * x; }
};

static int svg() {
  QSvgRenderer renderer(QByteArray(
      "<svg xmlns='http://www.w3.org/2000/svg' width='40' height='40'>"
      "<rect width='20' height='40' fill='#00ff00'/>"
      "<circle cx='30' cy='20' r='5' fill='blue'/></svg>"));
  CHECK(renderer.isValid() && renderer.defaultSize() == QSize(40, 40));
  QImage image(40, 40, QImage::Format_ARGB32);
  image.fill(Qt::white);
  QPainter p(&image);
  renderer.render(&p);
  p.end();
  CHECK(image.pixel(5, 5) == qRgb(0, 255, 0));
  CHECK(image.pixel(30, 20) == qRgb(0, 0, 255));
  CHECK(image.pixel(38, 2) == qRgb(255, 255, 255));
  // The SVG image-format plugin.
  QImage viaPlugin;
  CHECK(viaPlugin.loadFromData(
      "<svg xmlns='http://www.w3.org/2000/svg' width='8' height='8'>"
      "<rect width='8' height='8' fill='red'/></svg>",
      "SVG"));
  CHECK(viaPlugin.pixel(4, 4) == qRgb(255, 0, 0));
  return 0;
}

static int js() {
  QJSEngine engine;
  QJSValue r = engine.evaluate(
      "function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }"
      "var objs = [];"
      "for (var i = 0; i < 20000; ++i) objs.push({ i: i, s: 'x' + i });"
      "var sum = objs.reduce(function (a, o) { return a + o.i; }, 0);"
      "JSON.stringify({ fib: fib(20), sum: sum, re: /b+/.exec('abbbc')[0],"
      "  sorted: [3, 1, 2].sort(), date: new Date(0).toISOString() })");
  CHECK(!r.isError());
  CHECK(r.toString() ==
        "{\"fib\":6765,\"sum\":199990000,\"re\":\"bbb\",\"sorted\":[1,2,3],"
        "\"date\":\"1970-01-01T00:00:00.000Z\"}");
  engine.collectGarbage();
  QJSValue thrown = engine.evaluate("null.x");
  CHECK(thrown.isError() && thrown.property("name").toString() == "TypeError");
  Backend backend;
  engine.globalObject().setProperty("backend", engine.newQObject(&backend));
  CHECK(engine.evaluate("backend.greeting + backend.twice(21)").toString() == "hello42");
  QJSValue fn = engine.evaluate("(function (a, b) { return a * b; })");
  CHECK(fn.call({6, 7}).toInt() == 42);
  return 0;
}

static int quick() {
  QQmlEngine engine;
  Backend backend;
  engine.rootContext()->setContextProperty("backend", &backend);
  QQmlComponent component(&engine);
  component.setData(R"(
    import QtQuick 2.15
    Rectangle {
      id: root
      width: 100; height: 60
      color: "#ff0000"
      property int clicks: 0
      property string text: label.text
      signal done(int n)
      Text { id: label; text: backend.greeting + " " + backend.twice(root.clicks) }
      Rectangle { x: 50; width: 50; height: 60; color: "#0000ff" }
      Repeater { model: 5; Item { objectName: "item" + index } }
      Timer { interval: 10; running: true; repeat: true
              onTriggered: { root.clicks++; if (root.clicks == 3) { stop(); root.done(root.clicks) } } }
    }
  )", QUrl("qrc:/test.qml"));
  if (component.isError()) {
    for (const auto &e : component.errors()) fprintf(stderr, "%s\n", qPrintable(e.toString()));
    return 1;
  }
  QScopedPointer<QQuickItem> root(qobject_cast<QQuickItem *>(component.create()));
  CHECK(root);
  QEventLoop loop;
  int done = 0;
  QObject::connect(root.data(), SIGNAL(done(int)), &loop, SLOT(quit()));
  QTimer::singleShot(10000, &loop, &QEventLoop::quit);
  loop.exec();
  done = root->property("clicks").toInt();
  CHECK(done == 3);
  CHECK(root->property("text").toString() == "hello 6");

  QQuickWindow window;
  window.resize(100, 60);
  root->setParentItem(window.contentItem());
  window.show();
  QElapsedTimer timer;
  timer.start();
  while (!window.isExposed() && timer.elapsed() < 10000) QCoreApplication::processEvents();
  // The offscreen platform's backing store has no toImage(), so the
  // software renderer's grab is empty there (as in upstream Qt).
  if (QGuiApplication::platformName() == "offscreen") {
    fprintf(stderr, "(window grab skipped on offscreen)\n");
    return 0;
  }
  QImage shot = window.grabWindow();
  CHECK(shot.width() == 100);
  CHECK(shot.pixel(10, 50) == qRgb(255, 0, 0));
  CHECK(shot.pixel(90, 50) == qRgb(0, 0, 255));
  return 0;
}

static int controls() {
  QQmlEngine engine;
  QQmlComponent component(&engine);
  component.setData(R"(
    import QtQuick 2.15
    import QtQuick.Controls 2.15
    import QtQuick.Layouts 1.15
    ApplicationWindow {
      width: 200; height: 120
      property alias clicked: button.clickCount
      property alias sliderValue: slider.value
      ColumnLayout {
        Button { id: button; property int clickCount: 0; text: "Press"; onClicked: clickCount++ }
        Slider { id: slider; from: 0; to: 10; value: 3 }
        TextField { text: "hello" }
        ComboBox { model: ["a", "b", "c"] }
      }
      Component.onCompleted: { button.clicked(); slider.increase() }
    }
  )", QUrl("qrc:/controls.qml"));
  if (component.isError()) {
    for (const auto &e : component.errors()) fprintf(stderr, "%s\n", qPrintable(e.toString()));
    return 1;
  }
  QScopedPointer<QObject> window(component.create());
  CHECK(window);
  CHECK(window->property("clicked").toInt() == 1);
  CHECK(window->property("sliderValue").toDouble() == 4.0);
  return 0;
}

int main(int argc, char **argv) {
  QGuiApplication app(argc, argv);
  fprintf(stderr, "platform: %s\n", qPrintable(QGuiApplication::platformName()));
  int (*const parts[])() = {svg, js, quick, controls};
  const char *names[] = {"svg", "js", "quick", "controls"};
  for (size_t i = 0; i < sizeof parts / sizeof *parts; ++i) {
    if (parts[i]()) return 1;
    fprintf(stderr, "ok %s\n", names[i]);
  }
  return 0;
}

#include "qt5-quick.moc"
