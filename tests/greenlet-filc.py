"""Run against the installed Fil-C extension, never the build source tree."""
import contextvars
import gc
import signal
import threading

import greenlet
import _greenlet_filc_roots as roots

assert greenlet.__version__ == "3.3.0"
assert "/nix/store/" in greenlet._greenlet.__file__, greenlet._greenlet.__file__
main = greenlet.getcurrent()
context = contextvars.ContextVar("fiber", default="main")


def expected(depth, seed, resumed):
    # Each frame contributes (seed + 17*d) + (3*seed + d).
    return resumed + 4 * seed * (depth + 1) + 9 * depth * (depth + 1)


def worker(depth, seed):
    context.set(seed)
    local = {"seed": seed, "values": list(range(depth + 1))}
    try:
        raise ValueError(seed)
    except ValueError as error:
        def suspend():
            value = main.switch((depth, seed))
            assert context.get() == seed
            assert error.args == (seed,)
            assert local["values"] == list(range(depth + 1))
            return value
        return roots.probe(suspend, depth, seed)


configs = [(7, 13), (18, 29), (37, 53)]
fibers = [greenlet.greenlet(lambda d=d, s=s: worker(d, s)) for d, s in configs]
for fiber, config in zip(fibers, configs):
    assert fiber.switch() == config
    assert fiber.gr_frame is not None
    assert fiber._stack_saved > 0
assert context.get() == "main"
for _ in range(4):
    gc.collect()
    assert roots.collect() >= 3
for index in (2, 0, 1):
    depth, seed = configs[index]
    resumed = 101 + index * 19
    assert fibers[index].switch(resumed) == expected(depth, seed, resumed)
    assert fibers[index].dead
    assert fibers[index]._stack_saved == 0


def outer():
    def start_inner():
        inner = greenlet.greenlet(lambda: worker(23, 71))
        assert inner.switch() == expected(23, 71, 211)
        return 307
    return roots.probe(start_inner, 11, 89)


parent = greenlet.greenlet(outer)
assert parent.switch() == (23, 71)
inner = main.gr_frame  # Main is running, so it has no suspended frame.
assert inner is None
for _ in range(4):
    assert roots.collect() >= 3
# The inner is owned by its suspended parent's Python frame.
inner = parent.gr_frame.f_locals["inner"]
assert inner.switch(211) == expected(11, 89, 307)
assert parent.dead and inner.dead

# A suspended fiber must still reject another OS thread.
fiber = greenlet.greenlet(lambda: main.switch("thread-owned"))
assert fiber.switch() == "thread-owned"
failures = []


def wrong_thread():
    try:
        fiber.switch()
    except greenlet.error:
        failures.append("ownership enforced")


thread = threading.Thread(target=wrong_thread)
thread.start()
thread.join()
assert failures == ["ownership enforced"]
fiber.throw(greenlet.GreenletExit)
assert fiber.dead

# Native greenlet leaves signal masks attached to the OS thread.
old_mask = signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGUSR1})
try:
    def mask_worker():
        assert signal.SIGUSR1 in signal.pthread_sigmask(signal.SIG_BLOCK, set())
        signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGUSR1})
        main.switch()
        assert signal.SIGUSR1 in signal.pthread_sigmask(signal.SIG_BLOCK, set())
    fiber = greenlet.greenlet(mask_worker)
    fiber.switch()
    assert signal.SIGUSR1 not in signal.pthread_sigmask(signal.SIG_BLOCK, set())
    signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGUSR1})
    fiber.switch()
    assert fiber.dead
finally:
    signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)

print("greenlet installed-extension regression: suspended C roots, nested stacks, "
      "Python exceptions/context, thread ownership and signal masks PASS")
