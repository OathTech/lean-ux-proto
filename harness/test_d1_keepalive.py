"""The keepalive's bytes (send.c encrypt_packet) from harness/noise.py, against
the vectors the mirror's `#guard`s pin (Leanux/WG/Data.lean, `dataMessage`).

A keepalive is `le32 4 || le32 key_idx || le64 counter || AEAD(empty)`: the
ChaCha20-Poly1305 tag of the empty plaintext under the sending key, with the
nonce `4 zero bytes || le64 counter` and no associated data. A zero-length
payload at MTU 1420 has no padding.
"""
import struct
import unittest

from . import noise

KEY = bytes(range(32))
REMOTE_INDEX = 0x04030201
# Shared with the Lean #guards in Leanux/WG/Data.lean.
VECTORS = {
    0: "0400000001020304000000000000000010324f800a160bd9a1794255be7ec29d",
    5: "040000000102030405000000000000003e2fdcfe114117a96d0d40c0777d9d17",
    2 ** 40 + 3: "0400000001020304030000000001000082b9adec90da2dfe162521e79d637c95",
}


def keepalive(key, remote_index, counter):
    nonce = bytes(4) + struct.pack("<Q", counter)
    return struct.pack("<IIQ", 4, remote_index, counter) + noise.aead_encrypt(key, nonce, b"", b"")


class KeepaliveTests(unittest.TestCase):
    def test_vectors(self):
        for counter, expected in VECTORS.items():
            message = keepalive(KEY, REMOTE_INDEX, counter)
            self.assertEqual(len(message), 32)
            self.assertEqual(message.hex(), expected)

    def test_nonce_is_noise_counter_nonce(self):
        # the handshake's _nonce helper builds the same 12 bytes
        self.assertEqual(bytes(4) + struct.pack("<Q", 5), noise._nonce(5))


if __name__ == "__main__":
    unittest.main()
