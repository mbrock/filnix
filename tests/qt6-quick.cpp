// Real QML bindings, Quick software rendering and Controls 2 input under Fil-C.
#include <QtQml>
#include <QtQuick>
#include <QtTest>

#define CHECK(cond) do { if (!(cond)) { \
  fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond); return 1; \
} } while (0)

class Backend : public QObject {
  Q_OBJECT
  Q_PROPERTY(int input READ input WRITE setInput NOTIFY inputChanged)
public:
  int input() const { return m_input; }
  void setInput(int n) { if (n != m_input) { m_input = n; emit inputChanged(); } }
  Q_INVOKABLE int twice(int n) const { return n * 2; }
signals:
  void inputChanged();
private:
  int m_input = 7;
};

static bool ready(QQmlComponent &component) {
  for (const auto &e : component.errors()) fprintf(stderr, "%s\n", qPrintable(e.toString()));
  return component.isReady();
}

static int quick() {
  Backend backend;
  QQmlEngine engine;
  engine.rootContext()->setContextProperty("backend", &backend);
  QQmlComponent component(&engine);
  component.setData(R"QML(
    import QtQuick
    import QtQml.Models
    Rectangle {
      id: root
      width: 120; height: 70; color: "#1256ab"
      property int bias: 4
      property int result: backend.input * 3 + bias
      property int ticks: 0
      property string message: "bound " + backend.twice(result)
      property size dimensions: Qt.size(7, 11)
      property int dimensionSum: dimensions.width + dimensions.height * 2
      Rectangle { x: 83; width: 37; height: 70; color: "#cf4612" }
      Repeater { model: 5; Item { objectName: "item" + index } }
      ObjectModel { id: objects; Item { objectName: "modelItem" } }
      property int objectCount: objects.count
      Text { text: root.message }
      Timer { interval: 5; running: true; repeat: true
        onTriggered: { root.ticks++; if (root.ticks === 3) stop(); }
      }
    }
  )QML", QUrl("qrc:/quick.qml"));
  CHECK(ready(component));
  QScopedPointer<QQuickItem> root(qobject_cast<QQuickItem *>(component.create()));
  CHECK(root && root->property("result").toInt() == 25);
  CHECK(root->property("dimensionSum").toInt() == 29);
  CHECK(root->property("objectCount").toInt() == 1);
  int delegates = 0;
  bool finalDelegate = false;
  for (QQuickItem *child : root->childItems()) {
    if (child->objectName().startsWith("item")) {
      ++delegates;
      finalDelegate |= child->objectName() == "item4";
    }
  }
  CHECK(delegates == 5 && finalDelegate);
  backend.setInput(11);
  root->setProperty("bias", 8);
  CHECK(root->property("result").toInt() == 41);
  CHECK(root->property("message").toString() == "bound 82");
  engine.collectGarbage();
  backend.setInput(2);
  CHECK(root->property("message").toString() == "bound 28");
  QQuickWindow window;
  window.resize(120, 70);
  root->setParentItem(window.contentItem());
  window.show();
  CHECK(QTest::qWaitForWindowExposed(&window, 10000));
  QTest::qWait(100);
  CHECK(root->property("ticks").toInt() == 3);
  if (QGuiApplication::platformName() == "xcb") {
    const QImage shot = window.grabWindow();
    CHECK(shot.size() == QSize(120, 70));
    CHECK(shot.pixel(10, 60) == qRgb(0x12, 0x56, 0xab));
    CHECK(shot.pixel(110, 60) == qRgb(0xcf, 0x46, 0x12));
  }
  fprintf(stderr, "ok Qt6 QML bindings, QObject notifications, ObjectModel, timer and Quick pixels\n");
  return 0;
}

static int controls() {
  QQmlEngine engine;
  QQmlComponent component(&engine);
  component.setData(R"QML(
    import QtQuick
    import QtQuick.Controls
    import QtQuick.Layouts
    ApplicationWindow {
      id: root
      width: 360; height: 340; visible: true; color: "#f0f2f5"
      property int clicks: 0
      ColumnLayout {
        anchors.fill: parent; anchors.margins: 24; spacing: 12
        Label { text: "Qt 6 / Fil-C"; font.pixelSize: 22 }
        Button { objectName: "button"; text: "Press"; onClicked: root.clicks++ }
        Label { text: "Clicks: " + root.clicks }
        Slider { objectName: "slider"; from: 0; to: 10; value: 3; stepSize: 1 }
        TextField { objectName: "field"; text: "hello"; Layout.fillWidth: true }
        ComboBox { objectName: "combo"; model: ["Alpha", "Beta", "Gamma"] }
        Item { Layout.fillHeight: true }
      }
    }
  )QML", QUrl("qrc:/controls.qml"));
  CHECK(ready(component));
  QScopedPointer<QQuickWindow> window(qobject_cast<QQuickWindow *>(component.create()));
  CHECK(window && QTest::qWaitForWindowExposed(window.data(), 10000));
  QTest::qWait(100);
  auto *button = window->findChild<QQuickItem *>("button");
  auto *slider = window->findChild<QQuickItem *>("slider");
  auto *field = window->findChild<QQuickItem *>("field");
  auto *combo = window->findChild<QQuickItem *>("combo");
  CHECK(button && slider && field && combo);
  const QPoint click = button->mapToScene(QPointF(button->width()/2, button->height()/2)).toPoint();
  QTest::mouseClick(window.data(), Qt::LeftButton, Qt::NoModifier, click);
  CHECK(window->property("clicks").toInt() == 1);
  slider->forceActiveFocus();
  QTest::keyClick(window.data(), Qt::Key_Right);
  CHECK(slider->property("value").toDouble() == 4.0);
  field->forceActiveFocus();
  QTest::keyClick(window.data(), Qt::Key_A, Qt::ControlModifier);
  for (char c : QByteArray("typed")) QTest::keyClick(window.data(), c);
  CHECK(field->property("text").toString() == "typed");
  combo->forceActiveFocus();
  QTest::keyClick(window.data(), Qt::Key_Down);
  CHECK(combo->property("currentIndex").toInt() == 1);
  CHECK(combo->property("currentText").toString() == "Beta");
  engine.collectGarbage();
  QTest::mouseClick(window.data(), Qt::LeftButton, Qt::NoModifier, click);
  CHECK(window->property("clicks").toInt() == 2);
  const QString screenshot = qEnvironmentVariable("FILNIX_QT_QUICK_SCREENSHOT");
  if (!screenshot.isEmpty()) {
    QTest::qWait(100);
    const QImage image = window->grabWindow();
    CHECK(image.size() == QSize(360, 340) && image.save(screenshot));
    QObject *popup = combo->property("popup").value<QObject *>();
    CHECK(popup && QMetaObject::invokeMethod(popup, "open"));
    QTest::qWait(100);
    CHECK(popup->property("visible").toBool());
    CHECK(window->grabWindow().save(screenshot + ".popup.png"));
    CHECK(QMetaObject::invokeMethod(popup, "close"));
  }
  fprintf(stderr, "ok Qt6 Controls 2 button, slider, text input, combo and post-GC interaction\n");
  return 0;
}

int main(int argc, char **argv) {
  QGuiApplication app(argc, argv);
  fprintf(stderr, "platform: %s\n", qPrintable(QGuiApplication::platformName()));
  return quick() || controls();
}

#include "qt6-quick.moc"
