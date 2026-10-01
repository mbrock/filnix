// QV4 contracts derived from Qt 6's value, key and persistent-handle layouts.
#include <QtQml>
#include <private/qjsvalue_p.h>
#include <private/qv4persistent_p.h>
#include <private/qv4propertykey_p.h>
#include <private/qbipointer_p.h>
#include <cmath>
#include <limits>
#include <vector>

#define CHECK(cond) do { if (!(cond)) { \
  fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond); return 1; \
} } while (0)

static_assert(sizeof(QV4::ReturnedValue) == 8);
static_assert(sizeof(QV4::StaticValue) == 8);
static_assert(sizeof(QV4::Value) == 8);
static_assert(sizeof(QV4::PropertyKey) == 8);
static_assert(sizeof(QJSValue) == 8);
static_assert(alignof(QV4::Value) >= alignof(void *));
static_assert(offsetof(QV4::EngineBase, memoryManager) % alignof(void *) == 0);
static_assert(std::is_trivially_copyable_v<QV4::ReturnedValue>);
static_assert(std::is_trivially_copyable_v<QV4::StaticValue>);
static_assert(std::is_trivially_copyable_v<QV4::Value>);
static_assert(std::is_trivially_copyable_v<QV4::PropertyKey>);

struct alignas(8) First { int n; };
struct alignas(8) Second { int n; };

int main(int argc, char **argv) {
  QCoreApplication app(argc, argv);
  First first{17}; Second second{93};
  QBiPointer<First, Second> ptr(&first);
  ptr.setFlag(); ptr.setFlag(); // Setting a tag must be idempotent.
  CHECK(ptr.isT1() && ptr.flag() && ptr.asT1()->n == 17);
  auto retainedPtr = ptr;
  ptr = &second;
  CHECK(ptr.isT2() && ptr.flag() && ptr.asT2()->n == 93);
  ptr.clearFlag(); ptr.clearFlag();
  CHECK(!ptr.flag() && retainedPtr.asT1()->n == 17);
  ptr = static_cast<Second *>(nullptr);
  CHECK(ptr.isNull() && ptr.isT2());
  ptr = &first;
  CHECK(ptr.isT1() && ptr.asT1()->n == 17);
  QBiPointer<const First, Second> constant(&first);
  constant.setFlag();
  CHECK(constant.asT1()->n == 17 && constant.flag());

  QJSEngine engine;
  QJSValue identity = engine.evaluate("(function(x) { return x; })");
  QJSValue increment = engine.evaluate("(function(x) { return x + 1; })");
  CHECK(identity.isCallable() && increment.isCallable());
  const QJSValue recursion = engine.evaluate("(function f(n) { return n ? f(n-1)+1 : 0; })");
  CHECK(recursion.isCallable());
  CHECK(recursion.call({12}).toInt() == 12);
  const QJSValue overflow = recursion.call({100000});
  CHECK(overflow.isError() && overflow.property("name").toString() == "RangeError");
  const int callLimit = QV4::ExecutionEngine::maxCallDepth();
  CHECK(callLimit > 0);
  QV4::ExecutionEngine::setMaxCallDepth(20);
  CHECK(recursion.call({10}).toInt() == 10);
  CHECK(recursion.call({100}).isError());
  QV4::ExecutionEngine::setMaxCallDepth(callLimit);
  CHECK(engine.evaluate("6*7").toInt() == 42);
  const QString text = QStringLiteral("capability λ") + QChar(0) + QStringLiteral("tail");
  QJSValue string(text), stringCopy(string), stringMoved(std::move(stringCopy));
  CHECK(stringCopy.isUndefined() && stringMoved.isString() && stringMoved.toString() == text);
  CHECK(identity.call({stringMoved}).toString() == text);
  for (bool b : {false, true}) {
    QJSValue result = identity.call({QJSValue(b)});
    CHECK(result.isBool() && result.toBool() == b);
  }
  CHECK(identity.call({QJSValue(QJSValue::NullValue)}).isNull());
  CHECK(identity.call({QJSValue()}).isUndefined());
  CHECK(identity.call({QJSValue(4294967295u)}).toNumber() == 4294967295.0);
  const double numbers[] = {
    -2147483649.0, -2147483648.0, -2147483647.0, 2147483646.0,
    2147483647.0, 2147483648.0, 4294967295.0, 4294967296.0,
    -9007199254740991.0, 9007199254740991.0, -0.0, 0.0, 0.125, -0.125,
    std::numeric_limits<double>::denorm_min(), std::numeric_limits<double>::max(),
    std::numeric_limits<double>::infinity(), -std::numeric_limits<double>::infinity(),
    std::numeric_limits<double>::quiet_NaN(), -std::numeric_limits<double>::quiet_NaN()
  };
  for (double n : numbers) {
    QJSValue input(n), copied(input), moved(std::move(copied));
    CHECK(copied.isUndefined());
    QJSValue result = identity.call({moved});
    CHECK(result.isNumber() && !result.isObject());
    const double actual = result.toNumber();
    CHECK(std::isnan(n) ? std::isnan(actual) : actual == n);
    if (n == 0) CHECK(std::signbit(actual) == std::signbit(n));
    QJSValue sum = increment.call({input});
    CHECK(sum.isNumber());
    CHECK(std::isnan(n) ? std::isnan(sum.toNumber()) : sum.toNumber() == n + 1);
  }
  QJSValue boundaries = engine.evaluate(R"JS(
    [2147483647+1, -2147483648-1, 4294967295>>>0, 4294967296>>>0,
     2147483648|0, 1/-0, Object.is(-0,0), NaN===NaN,
     Number.isNaN(0/0)].map(String).join('|')
  )JS");
  CHECK(!boundaries.isError());
  CHECK(boundaries.toString() == "2147483648|-2147483649|4294967295|0|-2147483648|-Infinity|false|false|true");
  CHECK(std::signbit(engine.evaluate("Math.sign(-0)").toNumber()));
  CHECK(engine.evaluate("Array.from(new Uint32Array([4294967295,4294967296,17])).join(',')")
    .toString() == "4294967295,0,17");
  CHECK(engine.evaluate("new Date(0).toISOString() + '|' + /b+/.exec('abbbc')[0]")
    .toString() == "1970-01-01T00:00:00.000Z|bbb");
  const QJSValue transitions = engine.evaluate(R"JS(
    (function() {
      var a=[{x:17}, -0, NaN, undefined, null, true, 2147483648, 'heap string'];
      for(var i=0;i<1003;++i) { var v=a[0]; a.push(v); a.shift(); }
      return a.length===8 && a.some(v=>v && v.x===17)
        && a.some(v=>Object.is(v,-0)) && a.some(Number.isNaN)
        && a.includes('heap string');
    })()
  )JS");
  CHECK(transitions.isBool() && transitions.toBool());

  QJSValue object = engine.evaluate("({n:73,child:{s:'retained'},self:null})");
  CHECK(!object.isError());
  object.setProperty("self", object);
  QJSManagedValue emptyManaged;
  QJSValue emptyAdopted(std::move(emptyManaged));
  CHECK(emptyAdopted.isUndefined());
  QJSManagedValue managed(object, &engine);
  QJSManagedValue managedMoved(std::move(managed));
  CHECK(managed.isUndefined());
  QJSValue adopted(std::move(managedMoved));
  CHECK(managedMoved.isUndefined() && adopted.strictlyEquals(object));
  QJSValue copied(object), moved(std::move(copied)), assigned, moveAssigned;
  CHECK(copied.isUndefined());
  QJSValue previous = engine.evaluate("({n:-19})");
  assigned = previous;
  assigned = moved;
  moveAssigned = previous;
  moveAssigned = std::move(assigned);
  CHECK(assigned.strictlyEquals(previous)); // QJSValue move assignment swaps.
  const QV4::Value *value = QJSValuePrivate::asManagedType<QV4::Managed>(&object);
  CHECK(value && value->isObject());
  CHECK((quintptr(value) & 7) == 0 && (quintptr(value->m()) & 31) == 0);
  QV4::Value valueCopy = *value;
  auto returned = valueCopy.asReturnedValue();
  QV4::Value valueMoved = QV4::Value::fromReturnedValue(std::move(returned));
  CHECK(valueMoved.m() == value->m() && valueMoved.isObject());
  QV4::PersistentValue persistent(engine.handle(), *value), persistentCopy(persistent);
  QV4::PersistentValue persistentMoved(std::move(persistentCopy)), persistentAssigned;
  CHECK(persistentCopy.isEmpty()); // Unlike Qt 5, Qt 6 has a real move constructor.
  persistentAssigned.set(engine.handle(), *QJSValuePrivate::asManagedType<QV4::Managed>(&previous));
  persistentAssigned = std::move(persistentMoved);
  CHECK(persistentMoved.isEmpty());
  persistent.clear();
  object = QJSValue();
  std::vector<QJSValue> roots;
  for (int i=0; i<1500; ++i) {
    QJSValue root = engine.newObject();
    root.setProperty("index", i);
    root.setProperty("graph", moved);
    roots.push_back(std::move(root));
  }
  QJSValue keys = engine.evaluate(R"JS(
    (function() {
      var s=Symbol('key'), t=Symbol('key'), o={}, a=[];
      o[s]=11; o[t]=22; o.key=33; o.__proto__=null;
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
  for (int round=0; round<3; ++round) {
    CHECK(!engine.evaluate("for(var i=0;i<20000;++i) ({i:i,s:'garbage'+i});").isError());
    engine.collectGarbage();
    CHECK(moved.strictlyEquals(moveAssigned));
    CHECK(adopted.strictlyEquals(moved));
    CHECK(moved.property("n").toInt()==73 && assigned.property("n").toInt()==-19);
    CHECK(moved.property("self").strictlyEquals(moved));
    CHECK(moved.property("child").property("s").toString()=="retained");
    CHECK(QJSValuePrivate::fromReturnedValue(persistentAssigned.value()).strictlyEquals(moved));
    CHECK(persistentAssigned.engine()==engine.handle());
    for (int i=0; i<int(roots.size()); ++i) {
      CHECK(roots[i].property("index").toInt()==i);
      CHECK(roots[i].property("graph").strictlyEquals(moved));
    }
    const QJSValue result = keys.call();
    CHECK(result.isBool() && result.toBool());
  }
  fprintf(stderr, "ok Qt6 JS numbers/NaN/-0, transitions, identity, keys, GC, persistent moves and alignment\n");
}
