"""Run the upstream httpbin server natively, but test the client in Fil-C."""

import os
import subprocess
from types import SimpleNamespace

import pytest


@pytest.fixture(scope="session")
def httpbin():
    yield from httpbin_server("Server")


@pytest.fixture(scope="session")
def httpbin_secure():
    yield from httpbin_server("SecureServer")


def httpbin_server(server_class):
    # httpbin's Swagger dependencies include Rust rpds, which cannot load
    # into Fil-C Python. The server is a separate tool, not client code.
    # Use the real app and pytest-httpbin's HTTP/TLS server and certificates.
    code = """
import sys
from httpbin import app
from pytest_httpbin import serve

with getattr(serve, sys.argv[1])(application=app) as server:
    print(server.url, flush=True)
    sys.stdin.read()
"""
    env = dict(os.environ)
    env.pop("PYTHONPATH", None)
    with subprocess.Popen(
        [os.environ["HTTPBIN_PYTHON"], "-I", "-c", code, server_class],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        text=True,
        env=env,
    ) as process:
        try:
            url = process.stdout.readline().strip()
            assert url.startswith(("http://127.0.0.1:", "https://127.0.0.1:")), url
            yield SimpleNamespace(url=url)
        finally:
            process.stdin.close()
            assert process.wait(timeout=10) == 0
