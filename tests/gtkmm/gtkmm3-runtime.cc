// gtkmm 3 on Broadway: Builder lookups, C++ signal handlers, properties,
// a TreeModel whose column GTypes come from C++ types, a derived widget and
// a main loop, exercising gtkmm over pointer-valued GTypes.
#include <gtkmm.h>
#include <cstdlib>
#include <iostream>

#define CHECK(cond)                                                       \
  do {                                                                    \
    if (!(cond)) {                                                        \
      std::cerr << __FILE__ << ":" << __LINE__ << ": " #cond "\n";        \
      std::exit(1);                                                       \
    }                                                                     \
  } while (0)

class Columns : public Gtk::TreeModel::ColumnRecord
{
public:
  Columns() { add(name); add(size); add(ratio); }
  Gtk::TreeModelColumn<Glib::ustring> name;
  Gtk::TreeModelColumn<int> size;
  Gtk::TreeModelColumn<double> ratio;
};

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
  if (!gtk_init_check(nullptr, nullptr))
    return 77;
  Gtk::Main::init_gtkmm_internals();

  auto builder = Gtk::Builder::create_from_string(
    "<interface><object class='GtkWindow' id='window'><child>"
    "<object class='GtkBox' id='box'><child>"
    "<object class='GtkButton' id='button'>"
    "<property name='label'>Fil-C</property>"
    "</object></child></object></child></object></interface>");
  Gtk::Window* window = nullptr;
  Gtk::Box* box = nullptr;
  Gtk::Button* button = nullptr;
  builder->get_widget("window", window);
  builder->get_widget("box", box);
  builder->get_widget("button", button);
  CHECK(window && box && button);
  CHECK(g_type_is_a(G_OBJECT_TYPE(button->gobj()), GTK_TYPE_BUTTON));

  int clicked = 0;
  button->signal_clicked().connect([&] { ++clicked; });
  button->clicked();
  CHECK(clicked == 1);
  button->set_label("Memory-safe gtkmm");
  CHECK(button->property_label().get_value() == "Memory-safe gtkmm");
  gchar* label = nullptr;
  g_object_get(button->gobj(), "label", &label, nullptr);
  CHECK(Glib::ustring(label) == "Memory-safe gtkmm");
  g_free(label);

  // A derived widget's virtual handler runs from a C signal emission.
  auto counting = Gtk::manage(new CountingButton());
  box->pack_start(*counting);
  g_signal_emit_by_name(counting->gobj(), "clicked");
  CHECK(counting->clicks == 1);
  CHECK(g_str_has_suffix(G_OBJECT_TYPE_NAME(counting->gobj()), "FilnixCountingButton"));

  // Tree model columns get their GTypes from the C++ column types.
  Columns columns;
  auto store = Gtk::ListStore::create(columns);
  CHECK(store->get_column_type(0) == G_TYPE_STRING);
  CHECK(store->get_column_type(1) == G_TYPE_INT);
  CHECK(store->get_column_type(2) == G_TYPE_DOUBLE);
  for (int i = 0; i < 3; ++i)
  {
    auto row = *store->append();
    row[columns.name] = Glib::ustring::compose("row %1", i);
    row[columns.size] = i * 10;
    row[columns.ratio] = i / 2.0;
  }
  Gtk::TreeView view(store);
  view.append_column("Name", columns.name);
  view.append_column("Size", columns.size);
  box->pack_start(view);
  auto second = *std::next(store->children().begin());
  CHECK(Glib::ustring(second[columns.name]) == "row 1");
  CHECK(int(second[columns.size]) == 10);

  // Show the window and let the main loop lay it out and draw a few frames.
  window->show_all();
  // Gtk::Main::run() needs a Gtk::Main instance, which aborts without a
  // display; gtk_init_check above lets the check retry until Broadway is up.
  auto loop = Glib::MainLoop::create();
  int ticks = 0;
  Glib::signal_timeout().connect(
    [&] {
      if (++ticks < 5)
        return true;
      loop->quit();
      return false;
    },
    20);
  loop->run();
  CHECK(view.get_allocated_width() > 0 && counting->get_allocated_height() > 0);

  std::cout << "gtkmm " << GTKMM_MAJOR_VERSION << "." << GTKMM_MINOR_VERSION
            << " ok: clicks=" << clicked + counting->clicks << " rows="
            << store->children().size() << "\n";
  delete window;
  return 0;
}
