// Installed-extension regression: these roots never enter a Python object.
#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <stdfil.h>

typedef struct {
    volatile long value;
    volatile unsigned char bytes[257];
} Payload;

__attribute__((noinline))
static PyObject *probe_frame(PyObject *callback, int depth, long seed)
{
    Payload *payload = zgc_alloc(sizeof(Payload));
    payload->value = seed + depth * 17;
    for (int i = 0; i < 257; ++i)
        payload->bytes[i] = (seed + depth + i) % 251;
    volatile long guard = seed * 3 + depth;
    // Exercise capabilities pointing both into this C frame and into the heap.
    // Volatile prevents optimizing the post-resume dereferences into constants.
    struct Roots { Payload *heap; volatile long *local; } roots = {payload, &guard};
    volatile struct Roots saved;
    memcpy((void *)&saved, &roots, sizeof(roots));
    PyObject *result = depth
        ? probe_frame(callback, depth - 1, seed)
        : PyObject_CallNoArgs(callback);
    if (!result)
        return NULL;
    long subtotal = PyLong_AsLong(result);
    Py_DECREF(result);
    if (PyErr_Occurred())
        return NULL;
    if (saved.heap->value != seed + depth * 17
        || *saved.local != seed * 3 + depth) {
        PyErr_SetString(PyExc_AssertionError, "suspended C frame/root was corrupted");
        return NULL;
    }
    for (int i = 0; i < 257; ++i) {
        if (saved.heap->bytes[i] != (seed + depth + i) % 251) {
            PyErr_SetString(PyExc_AssertionError, "suspended heap payload was corrupted");
            return NULL;
        }
    }
    return PyLong_FromLong(subtotal + saved.heap->value + *saved.local);
}

static PyObject *probe(PyObject *self, PyObject *args)
{
    PyObject *callback;
    int depth;
    long seed;
    if (!PyArg_ParseTuple(args, "Oil", &callback, &depth, &seed))
        return NULL;
    return probe_frame(callback, depth, seed);
}

static PyObject *collect(PyObject *self, PyObject *args)
{
    zgc_cycle_number before = zgc_completed_cycle();
    for (int i = 0; i < 3; ++i)
        zgc_request_and_wait();
    return PyLong_FromUnsignedLongLong(zgc_completed_cycle() - before);
}

static PyMethodDef methods[] = {
    {"probe", probe, METH_VARARGS, NULL},
    {"collect", collect, METH_NOARGS, NULL},
    {NULL, NULL, 0, NULL}
};
static struct PyModuleDef module = {
    PyModuleDef_HEAD_INIT, "_greenlet_filc_roots", NULL, -1, methods
};
PyMODINIT_FUNC PyInit__greenlet_filc_roots(void)
{
    return PyModule_Create(&module);
}
