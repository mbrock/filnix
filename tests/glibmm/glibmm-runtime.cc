// Exercises glibmm's C++ wrappers over pointer-valued GTypes: a derived
// GObject type with a property and signal, GValue boxing, variants, the
// wrap() type table and a Gio list model, driven by a main loop.
#include <giomm.h>
#include <glibmm.h>
#include <cstdlib>
#include <iostream>

#if GLIBMM_MAJOR_VERSION > 2 || GLIBMM_MINOR_VERSION >= 68
template<typename T> Glib::RefPtr<T> adopt(T* p) { return Glib::make_refptr_for_instance(p); }
using IntSignal = sigc::signal<void(int)>;
#else
template<typename T> Glib::RefPtr<T> adopt(T* p) { return Glib::RefPtr<T>(p); }
using IntSignal = sigc::signal<void, int>;
#endif

#define CHECK(cond)                                                       \
  do {                                                                    \
    if (!(cond)) {                                                        \
      std::cerr << __FILE__ << ":" << __LINE__ << ": " #cond "\n";        \
      std::exit(1);                                                       \
    }                                                                     \
  } while (0)

class Counter : public Glib::Object
{
public:
  Counter() : Glib::ObjectBase("FilnixCounter"), count_(*this, "count", 0) {}

  static Glib::RefPtr<Counter> create() { return adopt(new Counter()); }

  Glib::PropertyProxy<int> property_count() { return count_.get_proxy(); }
  IntSignal& signal_bumped() { return bumped_; }

  void bump()
  {
    count_.set_value(count_.get_value() + 1);
    bumped_.emit(count_.get_value());
  }

private:
  Glib::Property<int> count_;
  IntSignal bumped_;
};

class Item : public Glib::Object
{
public:
  explicit Item(const Glib::ustring& name) : Glib::ObjectBase("FilnixItem"), name(name) {}
  Glib::ustring name;
};

int main()
{
  Glib::init();
  Gio::init();

  auto counter = Counter::create();
  const GType type = G_OBJECT_TYPE(counter->gobj());
  CHECK(g_str_has_suffix(g_type_name(type), "FilnixCounter"));
  CHECK(g_type_is_a(type, G_TYPE_OBJECT));
  CHECK(g_object_class_find_property(G_OBJECT_GET_CLASS(counter->gobj()), "count"));

  int notified = 0, last = 0;
  counter->property_count().signal_changed().connect([&] { ++notified; });
  counter->signal_bumped().connect([&](int n) { last = n; });

  // Drive bumps from the main loop.
  auto loop = Glib::MainLoop::create();
  Glib::signal_timeout().connect(
    [&] {
      counter->bump();
      if (last < 3)
        return true;
      loop->quit();
      return false;
    },
    1);
  loop->run();
  CHECK(last == 3 && notified == 3);

  // Set the property through the C API and read it back through C++.
  g_object_set(counter->gobj(), "count", 41, nullptr);
  CHECK(counter->property_count().get_value() == 41);

  // wrap() looks up the C++ wrapper for an existing C instance by GType.
  Glib::RefPtr<Glib::Object> wrapped = Glib::wrap(G_OBJECT(counter->gobj()), true);
  CHECK(wrapped.get() == counter.get());
  // A C-created Gio object gets its most-derived C++ wrapper class.
  GObject* stream = G_OBJECT(g_memory_input_stream_new());
  Glib::RefPtr<Glib::Object> wrapped_stream = Glib::wrap(stream);
  CHECK(wrapped_stream && wrapped_stream->gobj() == stream);
  CHECK(dynamic_cast<Gio::MemoryInputStream*>(wrapped_stream.get()));

  // GValue boxing for fundamental and wrapped types.
  Glib::Value<Glib::ustring> text;
  text.init(Glib::Value<Glib::ustring>::value_type());
  text.set("memory safety");
  CHECK(G_VALUE_HOLDS_STRING(text.gobj()) && text.get() == "memory safety");
  Glib::Value<double> number;
  number.init(Glib::Value<double>::value_type());
  number.set(2.5);
  CHECK(G_VALUE_TYPE(number.gobj()) == G_TYPE_DOUBLE && number.get() == 2.5);

  // Variants: containers and type-checked casts.
  std::map<Glib::ustring, Glib::VariantBase> dict;
  dict["name"] = Glib::Variant<Glib::ustring>::create("filnix");
  dict["count"] = Glib::Variant<int>::create(42);
  auto variant = Glib::Variant<std::map<Glib::ustring, Glib::VariantBase>>::create(dict);
  CHECK(variant.get_type_string() == "a{sv}");
  auto back = variant.get();
  CHECK(Glib::VariantBase::cast_dynamic<Glib::Variant<int>>(back["count"]).get() == 42);

  // A Gio list model holding custom objects.
  auto store = Gio::ListStore<Item>::create();
  for (auto name : { "alpha", "beta", "gamma" })
    store->append(adopt(new Item(name)));
  CHECK(store->get_n_items() == 3);
  CHECK(store->get_item(1)->name == "beta");
  CHECK(g_type_is_a(store->get_item_type(), G_TYPE_OBJECT));

  std::cout << "glibmm " << GLIBMM_MAJOR_VERSION << "." << GLIBMM_MINOR_VERSION
            << " ok: count=" << counter->property_count().get_value()
            << " variant=" << variant.print() << "\n";
  return 0;
}
