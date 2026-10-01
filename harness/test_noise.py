"""RFC vectors for the harness's Noise primitives, and the initiation layout."""
import unittest

from . import noise


class NoiseTests(unittest.TestCase):
    def test_x25519_rfc7748(self):
        k = bytes.fromhex("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
        u = bytes.fromhex("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c")
        self.assertEqual(noise.x25519(k, u).hex(), "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")

    def test_chacha20_poly1305_rfc8439(self):
        key = bytes(range(0x80, 0xa0))
        nonce = bytes.fromhex("070000004041424344454647")
        aad = bytes.fromhex("50515253c0c1c2c3c4c5c6c7")
        plaintext = (b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, "
                     b"sunscreen would be it.")
        out = noise.aead_encrypt(key, nonce, plaintext, aad)
        self.assertEqual(out[-16:].hex(), "1ae10b594f09e26a7e902ecbd0600691")
        self.assertEqual(out[:16].hex(), "d31a8d34648e60db7b86afbc53ef7ec2")

    def test_initiation_layout(self):
        responder = noise.public_key(b"\x11" * 32)
        message = noise.initiation(responder, b"\x22" * 32, b"\x33" * 32, bytes(12), 7)
        self.assertEqual(len(message), 148)
        self.assertEqual(message[:8].hex(), "0100000007000000")
        self.assertEqual(message[8:40], noise.public_key(b"\x33" * 32))
        self.assertEqual(message[132:], bytes(16))


if __name__ == "__main__":
    unittest.main()
