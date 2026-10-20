#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import socket
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("boundary", Path(__file__).with_name("check-storage-boundary.py"))
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)


class StorageBoundary(unittest.TestCase):
    def test_private_socket_and_absent_tcp_are_required(self):
        with tempfile.TemporaryDirectory(prefix="p2-boundary-") as tmp:
            root = Path(tmp)
            config = root / "garage.toml"
            path = root / "s3.sock"
            config.write_text(f'[s3_api]\napi_bind_addr = "{path}"\n')
            with socket.socket(socket.AF_UNIX) as unix, socket.socket() as tcp:
                unix.bind(str(path))
                tcp.bind(("127.0.0.1", 0))
                port = tcp.getsockname()[1]
                boundary.check(config, port)
                tcp.listen()
                with self.assertRaisesRegex(ValueError, "TCP port"):
                    boundary.check(config, port)
            root.chmod(0o755)
            with self.assertRaisesRegex(ValueError, "0700"):
                boundary.check(config, port)
            root.chmod(0o700)
            config.write_text('[s3_api]\napi_bind_addr = "127.0.0.1:18439"\n')
            with self.assertRaisesRegex(ValueError, "Unix socket"):
                boundary.check(config, port)


if __name__ == "__main__":
    unittest.main()
