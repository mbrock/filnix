// Fil-C ignores the .qtmetadata section attribute. The contracts check
// verifies both metadata discovery and instantiation of this real plugin.
#include <QtCore>

class ContractPlugin : public QObject {
  Q_OBJECT
  Q_PLUGIN_METADATA(IID "org.filnix.Qt5Contracts")
  Q_PROPERTY(QString answer READ answer CONSTANT)
public:
  QString answer() const { return QStringLiteral("sectionless plugin"); }
};

#include "qt5-contract-plugin.moc"
