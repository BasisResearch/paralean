#!/usr/bin/env python3
"""SSH ProxyCommand: preserve byte order, delay each direction without root."""
import argparse
import asyncio
import sys
import time


async def relay(reader, write, delay):
    queue = asyncio.Queue()

    async def receive():
        while chunk := await reader.read(65536):
            await queue.put((time.monotonic() + delay, chunk))
        await queue.put((time.monotonic() + delay, None))

    task = asyncio.create_task(receive())
    try:
        while True:
            deadline, chunk = await queue.get()
            await asyncio.sleep(max(0, deadline - time.monotonic()))
            if chunk is None:
                return
            await write(chunk)
    finally:
        task.cancel()
        await asyncio.gather(task, return_exceptions=True)


async def main(args):
    remote, writer = await asyncio.open_connection(args.host, args.port)
    local = asyncio.StreamReader()
    await asyncio.get_running_loop().connect_read_pipe(
        lambda: asyncio.StreamReaderProtocol(local), sys.stdin.buffer)

    async def to_remote(chunk):
        writer.write(chunk)
        await writer.drain()

    async def to_local(chunk):
        sys.stdout.buffer.write(chunk)
        sys.stdout.buffer.flush()

    tasks = [asyncio.create_task(relay(local, to_remote, args.delay_ms / 1000)),
             asyncio.create_task(relay(remote, to_local, args.delay_ms / 1000))]
    try:
        await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
    finally:
        for task in tasks:
            task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
        writer.close()
        await writer.wait_closed()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("host")
    parser.add_argument("port", type=int)
    parser.add_argument("--delay-ms", type=float, default=0)
    asyncio.run(main(parser.parse_args()))
