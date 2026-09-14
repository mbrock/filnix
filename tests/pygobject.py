import gi

gi.require_version("GObject", "2.0")
gi.require_version("Gio", "2.0")
from gi.repository import Gio, GLib, GObject


class Probe(GObject.Object):
    value = GObject.Property(type=int, default=0)
    __gsignals__ = {"ping": (GObject.SignalFlags.RUN_FIRST, None, (int,))}


probe = Probe(value=17)
assert probe.props.value == 17
seen = []
probe.connect("ping", lambda obj, value: seen.append((obj, value)))
probe.emit("ping", 42)
assert seen == [(probe, 42)]
stream = Gio.MemoryInputStream.new_from_bytes(GLib.Bytes.new(b"Fil-C"))
assert stream.read_bytes(5, None).get_data() == b"Fil-C"
print("PyGObject: types, properties, callbacks and Gio passed")
