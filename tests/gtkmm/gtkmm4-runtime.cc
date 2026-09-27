// gtkmm 4 on Broadway: Builder lookups, C++ signal handlers, properties,
// a derived widget, a Gio::ListStore-backed list view and a main loop,
// exercising gtkmm over pointer-valued GTypes.
#include <gtkmm.h>
#include <gtkmm/init.h>
#include <cstdlib>
#include <iostream>

#define CHECK(cond)                                                       \
  do {                                                                    \
    if (!(cond)) {                                                        \
      std::cerr << __FILE__ << ":" << __LINE__ << ": " #cond "\n";        \
      std::exit(1);                                                       \
    }                                                                     \
  } while (0)

class CountingButton : public Gtk::Button
{
public:
  CountingButton() : Glib::ObjectBase("FilnixCountingButton"), Gtk::Button("count") {}
  int clicks = 0;

protected:
  void on_clicked() override { ++clicks; }
};

int main()
{
  if (!gtk_init_check())
    return 77;
  Gtk::init_gtkmm_internals();

  auto builder = Gtk::Builder::create_from_string(
    "<interface><object class='GtkWindow' id='window'><child>"
    "<object class='GtkBox' id='box'><property name='orientation'>vertical</property><child>"
    "<object class='GtkButton' id='button'>"
    "<property name='label'>Fil-C</property>"
    "</object></child></object></child></object></interface>");
  auto window = builder->get_widget<Gtk::Window>("window");
  auto box = builder->get_widget<Gtk::Box>("box");
  auto button = builder->get_widget<Gtk::Button>("button");
  CHECK(window && box && button);
  CHECK(g_type_is_a(G_OBJECT_TYPE(button->gobj()), GTK_TYPE_BUTTON));

  int clicked = 0;
  button->signal_clicked().connect([&] { ++clicked; });
  g_signal_emit_by_name(button->gobj(), "clicked");
  CHECK(clicked == 1);
  button->set_label("Memory-safe gtkmm");
  CHECK(button->property_label().get_value() == "Memory-safe gtkmm");

  auto counting = Gtk::make_managed<CountingButton>();
  box->append(*counting);
  g_signal_emit_by_name(counting->gobj(), "clicked");
  CHECK(counting->clicks == 1);
  CHECK(g_str_has_suffix(G_OBJECT_TYPE_NAME(counting->gobj()), "FilnixCountingButton"));

  // A list view over a string list, with a C++ factory binding rows.
  auto strings = Gtk::StringList::create({ "alpha", "beta", "gamma" });
  auto factory = Gtk::SignalListItemFactory::create();
  int bound = 0;
  factory->signal_setup().connect(
    [](const Glib::RefPtr<Gtk::ListItem>& item) { item->set_child(*Gtk::make_managed<Gtk::Label>()); });
  factory->signal_bind().connect([&](const Glib::RefPtr<Gtk::ListItem>& item) {
    auto str = std::dynamic_pointer_cast<Gtk::StringObject>(item->get_item());
    CHECK(str);
    dynamic_cast<Gtk::Label*>(item->get_child())->set_text(str->get_string());
    ++bound;
  });
  auto view = Gtk::make_managed<Gtk::ListView>(Gtk::SingleSelection::create(strings), factory);
  view->set_vexpand(true);
  box->append(*view);
  CHECK(strings->get_n_items() == 3 && strings->get_string(1) == "beta");

  window->set_default_size(200, 200);
  window->present();
  auto loop = Glib::MainLoop::create();
  int ticks = 0;
  Glib::signal_timeout().connect(
    [&] {
      if (++ticks < 10)
        return true;
      loop->quit();
      return false;
    },
    20);
  loop->run();
  CHECK(bound == 3);
  CHECK(view->get_width() > 0 && counting->get_height() > 0);

  std::cout << "gtkmm " << GTKMM_MAJOR_VERSION << "." << GTKMM_MINOR_VERSION
            << " ok: clicks=" << clicked + counting->clicks << " bound=" << bound << "\n";
  delete window;
  return 0;
}
