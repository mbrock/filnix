// A small Qt 5 program covering the common modules: signals and slots,
// containers, regular expressions, JSON, threads, events, SQLite, XML,
// painting and widgets. Run with QT_QPA_PLATFORM=offscreen or xcb.
#include <QtConcurrent>
#include <QtCore>
#include <QtGui>
#include <QtNetwork>
#include <QtSql>
#include <QtTest>
#include <QtWidgets>
#include <QtXml>

#define CHECK(cond)                                                          \
  do {                                                                       \
    if (!(cond)) {                                                           \
      fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);        \
      return 1;                                                              \
    }                                                                        \
  } while (0)

class Counter : public QObject {
  Q_OBJECT
  Q_PROPERTY(int value READ value WRITE setValue NOTIFY valueChanged)
public:
  int value() const { return m_value; }
  void setValue(int v) {
    if (v != m_value) {
      m_value = v;
      emit valueChanged(v);
    }
  }
signals:
  void valueChanged(int);

private:
  int m_value = 0;
};

static int square(int x) { return x * x; }

static int core() {
  Counter a, b;
  QObject::connect(&a, &Counter::valueChanged, &b, &Counter::setValue);
  int lambdaSeen = 0;
  QObject::connect(&a, &Counter::valueChanged, [&](int v) { lambdaSeen = v; });
  a.setValue(42);
  CHECK(b.value() == 42 && lambdaSeen == 42);
  CHECK(a.setProperty("value", 7) && b.property("value").toInt() == 7);
  CHECK(QString(a.metaObject()->className()) == "Counter");

  QHash<QString, int> hash;
  QMap<int, QString> map;
  QVector<QString> vec;
  for (int i = 0; i < 1000; ++i) {
    hash.insert(QString::number(i), i);
    map.insert(-i, QString::number(i));
    vec.append(QStringLiteral("item %1").arg(i));
  }
  CHECK(hash.value("777") == 777 && map.first() == "999" && vec[5] == "item 5");
  for (int i = 0; i < 1000; i += 2)
    map.remove(-i);
  int sum = 0;
  for (auto it = map.cbegin(); it != map.cend(); ++it)
    sum += it.value().toInt();
  CHECK(map.size() == 500 && sum == 250000);
  QStringList words = QString("the quick brown fox").split(' ');
  std::sort(words.begin(), words.end());
  CHECK(words.join(',') == "brown,fox,quick,the");

  QRegularExpression re("(\\d+)-(\\w+)");
  auto m = re.match("id 123-abc end");
  CHECK(m.hasMatch() && m.captured(1) == "123" && m.captured(2) == "abc");
#if QT_VERSION < QT_VERSION_CHECK(6, 0, 0)
  CHECK(QRegExp("a*b").exactMatch("aaab"));
#endif

  QJsonObject obj{{"name", "fil-c"}, {"n", 3}, {"list", QJsonArray{1, 2, 3}}};
  QByteArray json = QJsonDocument(obj).toJson(QJsonDocument::Compact);
  QJsonDocument back = QJsonDocument::fromJson(json);
  CHECK(back.object()["list"].toArray().size() == 3);
  CHECK(back.object()["name"].toString() == "fil-c");

  QVariant v = QVariant::fromValue(QList<int>{1, 2, 3});
  CHECK(v.value<QList<int>>().size() == 3);
  CHECK(QLocale(QLocale::German).toString(1234.5, 'f', 1) == "1.234,5");
  CHECK(QString::fromUtf8("Grüße").toUpper() == QString::fromUtf8("GRÜSSE"));
  CHECK(QCryptographicHash::hash("abc", QCryptographicHash::Sha256).toHex() ==
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
  CHECK(qUncompress(qCompress(json)) == json);
  QDateTime epoch = QDateTime::fromSecsSinceEpoch(0, Qt::UTC);
  CHECK(epoch.toString(Qt::ISODate) == "1970-01-01T00:00:00Z");

  // Threads, queued connections and the event loop.
  QList<int> in;
  for (int i = 0; i < 200; ++i) in << i;
  QList<int> out = QtConcurrent::blockingMapped(in, square);
  CHECK(out[199] == 199 * 199);
  QThread worker;
  Counter remote;
  remote.moveToThread(&worker);
  worker.start();
  QEventLoop loop;
  int seen = 0;
  QObject::connect(&remote, &Counter::valueChanged, &loop, [&](int x) {
    seen = x;
    loop.quit();
  });
  QMetaObject::invokeMethod(&remote, [&] { remote.setValue(99); });
  QTimer::singleShot(5000, &loop, &QEventLoop::quit);
  loop.exec();
  worker.quit();
  worker.wait();
  CHECK(seen == 99);

  QTemporaryDir dir;
  CHECK(dir.isValid());
  QFile f(dir.filePath("x.txt"));
  CHECK(f.open(QIODevice::WriteOnly));
  QTextStream(&f) << "hello " << 5 << "\n";
  f.close();
  CHECK(f.open(QIODevice::ReadOnly) && f.readAll() == "hello 5\n");
  CHECK(QDir(dir.path()).entryList(QDir::Files) == QStringList{"x.txt"});

  QProcess proc;
  proc.start("sh", {"-c", "echo from-child"});
  CHECK(proc.waitForFinished(10000) && proc.readAllStandardOutput() == "from-child\n");
  return 0;
}

static int network() {
  QTcpServer server;
  CHECK(server.listen(QHostAddress::LocalHost));
  QTcpSocket client;
  client.connectToHost(QHostAddress::LocalHost, server.serverPort());
  CHECK(server.waitForNewConnection(5000));
  QTcpSocket *peer = server.nextPendingConnection();
  CHECK(client.waitForConnected(5000));
  client.write("ping");
  CHECK(client.waitForBytesWritten(5000) && peer->waitForReadyRead(5000));
  CHECK(peer->readAll() == "ping");
  CHECK(QUrl("https://example.org/a?b=c#d").query() == "b=c");
  CHECK(QSslSocket::supportsSsl());
  return 0;
}

static int sql() {
  QSqlDatabase db = QSqlDatabase::addDatabase("QSQLITE");
  db.setDatabaseName(":memory:");
  CHECK(db.open());
  QSqlQuery q;
  CHECK(q.exec("create table t (id integer primary key, name text)"));
  CHECK(q.prepare("insert into t (name) values (?)"));
  for (const char *n : {"a", "b", "c"}) {
    q.addBindValue(n);
    CHECK(q.exec());
  }
  CHECK(q.exec("select group_concat(name) from t") && q.next());
  CHECK(q.value(0).toString() == "a,b,c");
  return 0;
}

static int xml() {
  QDomDocument doc;
  CHECK(doc.setContent(QString("<r><c n='1'/><c n='2'/></r>")));
  CHECK(doc.documentElement().elementsByTagName("c").size() == 2);
  QXmlStreamReader reader("<a><b>text</b></a>");
  QString text;
  while (!reader.atEnd())
    if (reader.readNext() == QXmlStreamReader::Characters) text += reader.text();
  CHECK(text == "text");
  return 0;
}

static int gui() {
  QImage image(64, 64, QImage::Format_ARGB32);
  image.fill(Qt::white);
  QPainter p(&image);
  p.setRenderHint(QPainter::Antialiasing);
  p.fillRect(QRect(0, 0, 32, 64), Qt::red);
  p.setPen(Qt::black);
  p.drawText(QRect(0, 0, 64, 64), Qt::AlignCenter, "Qt");
  p.end();
  CHECK(image.pixel(5, 5) == qRgb(255, 0, 0) && image.pixel(60, 5) == qRgb(255, 255, 255));
  QBuffer png;
  CHECK(image.save(&png, "PNG"));
  QImage loaded;
  CHECK(loaded.loadFromData(png.data(), "PNG") && loaded.pixel(5, 5) == qRgb(255, 0, 0));
#if QT_VERSION >= QT_VERSION_CHECK(6, 0, 0)
  CHECK(!QFontDatabase::families().isEmpty());
#else
  CHECK(!QFontDatabase().families().isEmpty());
#endif

  QWidget window;
  auto *layout = new QVBoxLayout(&window);
  auto *label = new QLabel("Hello from Fil-C");
  auto *edit = new QLineEdit;
  auto *button = new QPushButton("Copy");
  auto *list = new QListWidget;
  layout->addWidget(label);
  layout->addWidget(edit);
  layout->addWidget(button);
  layout->addWidget(list);
  QObject::connect(button, &QPushButton::clicked, [&] {
    label->setText(edit->text());
    list->addItem(edit->text());
  });
  window.resize(320, 240);
  window.show();
  CHECK(QTest::qWaitForWindowExposed(&window));
  edit->setFocus();
  QApplication::processEvents();
  for (QChar c : QString("typed")) {
    QKeyEvent press(QEvent::KeyPress, 0, Qt::NoModifier, QString(c));
    QApplication::sendEvent(edit, &press);
  }
  CHECK(edit->text() == "typed");
  button->click();
  CHECK(label->text() == "typed" && list->count() == 1);
  QPixmap shot = window.grab();
  CHECK(shot.width() == 320 && !shot.toImage().isNull());
  const QString screenshot = qEnvironmentVariable("FILNIX_QT_SCREENSHOT");
  if (!screenshot.isEmpty())
    CHECK(shot.save(screenshot));

  QStandardItemModel tree;
  auto *root = new QStandardItem("root");
  root->appendRow(new QStandardItem("child"));
  tree.appendRow(root);
  QModelIndex child = tree.index(0, 0, tree.index(0, 0));
  CHECK(child.data().toString() == "child" && child.parent().data().toString() == "root");
  QSortFilterProxyModel proxy;
  proxy.setSourceModel(&tree);
  proxy.setRecursiveFilteringEnabled(true);
  proxy.setFilterFixedString("child");
  QModelIndex proxyChild = proxy.index(0, 0, proxy.index(0, 0));
  CHECK(proxyChild.data().toString() == "child");
  QTreeView treeView;
  treeView.setModel(&proxy);
  treeView.expandAll();

  QStandardItemModel model(3, 2);
  QTableView view;
  view.setModel(&model);
  model.setData(model.index(1, 1), "cell");
  CHECK(view.model()->data(view.model()->index(1, 1)).toString() == "cell");
  return 0;
}

int main(int argc, char **argv) {
  QApplication app(argc, argv);
  fprintf(stderr, "platform: %s\n", qPrintable(QGuiApplication::platformName()));
  int (*const parts[])() = {core, network, sql, xml, gui};
  const char *names[] = {"core", "network", "sql", "xml", "gui"};
  for (size_t i = 0; i < sizeof parts / sizeof *parts; ++i) {
    if (parts[i]()) return 1;
    fprintf(stderr, "ok %s\n", names[i]);
  }
  return 0;
}

#include "qt5-smoke.moc"
