__doc__ = '''
evince.py, a simple wrapper around Evince that can detect when a user has
selected an equation, when run as a subprocess, the parent process can then
determine which equation the user has last selected by parsing stdout.
This works for when the document has properly wrapped each equation,
which creates numbers in the form "(N)" on the right hand side of the equation, 
therefore the user can simply double click "(N)" which selects that text.

Notes:
 sudo apt install gir1.2-evince-3.0
 https://lazka.github.io/pgi-docs/EvinceView-3.0/classes/View.html
 https://lazka.github.io/pgi-docs/EvinceView-3.0/classes/DocumentModel.html

'''

import gi
gi.require_version('Gtk', '3.0')
gi.require_version('EvinceDocument', '3.0')
gi.require_version('EvinceView', '3.0')
from gi.repository import Gtk, Gio, GLib
from gi.repository import EvinceDocument
from gi.repository import EvinceView
import os, sys

TEST_PDF = os.path.expanduser('~/Downloads/2510.24491v3.pdf')
if sys.argv[-1].endswith('.pdf'): TEST_PDF = sys.argv[-1]
DEBUG = False

class EvinceApp(Gtk.Application):
    def __init__(self):
        Gtk.Application.__init__(self, application_id="apps.rosetta.evincepy", flags=Gio.ApplicationFlags.FLAGS_NONE)
        self.connect("activate", self.on_activate)
        GLib.timeout_add(1000, self.on_timer)
        self._selected_eq = None

    def on_timer(self):
        if DEBUG:
            print('tick...')
            print('scroll:', self._scroll.get_vadjustment().get_value())
            print('hassel:', self._view.get_has_selection())
        if self._view.get_has_selection():
            sel = self._view.get_selected_text().strip()
            if DEBUG: print('text:', sel)
            if sel != self._selected_eq and sel.startswith('(') and sel.endswith(')'):
                n = sel.split('(')[-1].split(')')[0]
                if n.isdigit():
                    self._selected_eq = sel
                    print('newsel:', sel)
        return True

    def on_activate(self, data=None):
        self._window = window = Gtk.Window(type=Gtk.WindowType.TOPLEVEL)
        window.set_title("Rosetta PDF Viewer")
        window.set_border_width(2)
        window.set_default_size(600, 500)
        self._scroll = scroll = Gtk.ScrolledWindow()
        window.add(scroll)
        EvinceDocument.init()
        self._doc = doc = EvinceDocument.Document.factory_get_document('file://' + TEST_PDF)
        self._view = view = EvinceView.View()
        self._model = model = EvinceView.DocumentModel()
        model.set_document(doc)
        view.set_model(model)
        scroll.add(view)
        window.show_all()
        self.add_window(window)

if __name__ == "__main__":
    app = EvinceApp()
    app.run(None)

