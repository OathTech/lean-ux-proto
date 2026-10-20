"""Debugger framing must survive coalesced and arbitrarily fragmented reads."""
import unittest

from capture_lookup import Remote


class Socket:
    def __init__(self, chunks):
        self.chunks = iter(chunks)
        self.sent = []

    def recv(self, _size):
        return next(self.chunks, b'')

    def sendall(self, data):
        self.sent.append(data)


class RemoteTests(unittest.TestCase):
    def remote(self, chunks):
        remote = Remote.__new__(Remote)
        remote.socket = Socket(chunks)
        remote.buffer, remote.position = b'', 0
        return remote

    def packet(self, payload):
        return b'+$'+payload+b'#'+f'{sum(payload)%256:02x}'.encode()

    def test_packet_boundaries(self):
        wire = self.packet(b'012345')+self.packet(b'89abcd')
        for chunks in ([wire], [wire[i:i+1] for i in range(len(wire))],
                       [wire[:4], wire[4:11], wire[11:]]):
            remote = self.remote(chunks)
            self.assertEqual(remote.read(0x1000, 3), bytes.fromhex('012345'))
            self.assertEqual(remote.read(0x2000, 3), bytes.fromhex('89abcd'))
            self.assertEqual(remote.socket.sent[1::2], [b'+', b'+'])

    def test_bad_checksum_and_truncation(self):
        with self.assertRaisesRegex(ValueError, 'checksum'):
            self.remote([b'+$OK#00']).command('m1000,1')
        with self.assertRaises(EOFError):
            self.remote([b'+$12']).command('m1000,1')

    def test_missing_or_short_memory_fails(self):
        for reply, message in ((b'E14', 'unmapped'), (b'01', 'short')):
            with self.assertRaisesRegex(ValueError, message):
                self.remote([self.packet(reply)]).read(0x1000, 2)


if __name__ == '__main__':
    unittest.main()
