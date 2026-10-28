#!/usr/bin/env python3
import contextlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import importlib.util
from pathlib import Path
import socket
import tempfile
import threading
import unittest

spec = importlib.util.spec_from_file_location("boundary", Path(__file__).with_name("check-storage-boundary.py"))
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)

TOKEN = "7" * 64


@contextlib.contextmanager
def admin_api(require_token=True, token=TOKEN):
    """A stand-in for Garage's admin API; yields its [admin] config section."""
    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            ok = not require_token or self.headers.get("Authorization") == f"Bearer {token}"
            self.send_response(200 if ok else 401)
            self.end_headers()

        def log_message(self, *args):
            pass

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        yield f'[admin]\napi_bind_addr = "127.0.0.1:{server.server_address[1]}"\nmetrics_token = "{token}"\n'
    finally:
        server.shutdown()
        server.server_close()


class StorageBoundary(unittest.TestCase):
    def test_private_socket_and_absent_tcp_are_required(self):
        with tempfile.TemporaryDirectory(prefix="p2-boundary-") as tmp, admin_api() as admin:
            root = Path(tmp)
            config = root / "garage.toml"
            sockets = root / "sock"
            sockets.mkdir(mode=0o700)
            path = sockets / "s3.sock"
            config.write_text(f'[s3_api]\napi_bind_addr = "{path}"\n' + admin)
            config.chmod(0o600)
            with socket.socket(socket.AF_UNIX) as unix, socket.socket() as tcp:
                unix.bind(str(path))
                tcp.bind(("127.0.0.1", 0))
                port = tcp.getsockname()[1]
                boundary.check(config, port)
                tcp.listen()
                with self.assertRaisesRegex(ValueError, "TCP port"):
                    boundary.check(config, port)
            sockets.chmod(0o755)
            with self.assertRaisesRegex(ValueError, "socket parent must be owned by this user and mode 0700"):
                boundary.check(config, port)
            sockets.chmod(0o700)
            config.chmod(0o644)
            with self.assertRaisesRegex(ValueError, "Garage config"):
                boundary.check(config, port)
            config.chmod(0o600)
            config.write_text('[s3_api]\napi_bind_addr = "127.0.0.1:18439"\n')
            with self.assertRaisesRegex(ValueError, "Unix socket"):
                boundary.check(config, port)

    def test_secret_files_must_be_private(self):
        with tempfile.TemporaryDirectory(prefix="p2-boundary-") as tmp, admin_api() as admin:
            root = Path(tmp)
            garage, fdb = root / "garage", root / "fdb"
            garage.mkdir(mode=0o700)
            fdb.mkdir(mode=0o700)
            config, cluster, path = garage / "garage.toml", fdb / "fdb.cluster", garage / "s3.sock"
            config.write_text(f'[s3_api]\napi_bind_addr = "{path}"\n' + admin)
            cluster.write_text("paralean:test-only@127.0.0.1:1\n")
            config.chmod(0o600)
            cluster.chmod(0o600)
            with socket.socket(socket.AF_UNIX) as unix, socket.socket() as tcp:
                unix.bind(str(path))
                tcp.bind(("127.0.0.1", 0))
                port = tcp.getsockname()[1]
                boundary.check(config, port, cluster)
                cluster.chmod(0o644)
                with self.assertRaisesRegex(ValueError, "FDB cluster file"):
                    boundary.check(config, port, cluster)
                cluster.chmod(0o600)
                fdb.chmod(0o755)
                with self.assertRaisesRegex(ValueError, "FDB cluster directory"):
                    boundary.check(config, port, cluster)

    def test_metrics_require_the_config_token(self):
        with tempfile.TemporaryDirectory(prefix="p2-boundary-") as tmp:
            root = Path(tmp)
            sockets = root / "sock"
            sockets.mkdir(mode=0o700)
            config, path = root / "garage.toml", sockets / "s3.sock"
            s3 = f'[s3_api]\napi_bind_addr = "{path}"\n'
            with socket.socket(socket.AF_UNIX) as unix, socket.socket() as tcp:
                unix.bind(str(path))
                tcp.bind(("127.0.0.1", 0))
                port = tcp.getsockname()[1]
                with admin_api() as admin:
                    config.write_text(s3 + admin)
                    config.chmod(0o600)
                    boundary.check(config, port)
                    config.write_text(s3 + "\n".join(l for l in admin.splitlines() if "metrics_token" not in l))
                    with self.assertRaises(ValueError):
                        boundary.check(config, port)
                # A guessable token is refused even though the running API enforces it.
                with admin_api(token="short") as admin:
                    config.write_text(s3 + admin)
                    with self.assertRaisesRegex(ValueError, "metrics_token"):
                        boundary.check(config, port)
                # A running Garage that serves /metrics without the token (started before
                # its config had one) is refused although the config is right.
                with admin_api(require_token=False) as admin:
                    config.write_text(s3 + admin)
                    with self.assertRaisesRegex(ValueError, "answers without its token"):
                        boundary.check(config, port)
                # ...and so is one whose token differs from the config's.
                with admin_api() as admin:
                    config.write_text(s3 + admin.replace(TOKEN, "8" * 64))
                    with self.assertRaisesRegex(ValueError, "refuses this config's token"):
                        boundary.check(config, port)


if __name__ == "__main__":
    unittest.main()
