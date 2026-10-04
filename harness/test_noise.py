"""RFC vectors for the harness's Noise primitives, the initiation layout, and
the D1 handshake: initiation, response, session keys and keepalive."""
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


    # Stage D1: wg0 (the initiator) and a peer whose private key the trace knows.
    WG0, PEER, WG0_E, PEER_E = b"\x11" * 32, b"\x22" * 32, b"\x33" * 32, b"\x44" * 32

    def handshake(self, psk=None, **kw):
        stamp = noise.tai64n(1_700_000_000, 123_456_789)
        init = noise.initiation(noise.public_key(self.PEER), self.WG0, noise.clamp(self.WG0_E), stamp, 0x0a0b0c0d)
        return init, noise.response(init, self.PEER, self.PEER_E, psk, 0x01020304,
                                    initiator_public=noise.public_key(self.WG0), timestamp=stamp, **kw)

    def test_response_keys_agree(self):
        for psk in (None, b"\xaa" * 32):
            init, resp = self.handshake(psk)
            self.assertEqual(len(resp.message), 92)
            self.assertEqual(resp.message[:12].hex(), "02000000" "04030201" "0d0c0b0a")
            self.assertEqual(resp.message[76:], bytes(16))
            index, sending, receiving = noise.consume_response(resp.message, init, self.WG0, self.WG0_E,
                                                               noise.public_key(self.PEER), psk)
            self.assertEqual((index, sending, receiving), (0x01020304, resp.initiator_sending, resp.initiator_receiving))
            self.assertEqual((resp.responder_sending, resp.responder_receiving), (receiving, sending))
            self.assertNotEqual(sending, receiving)

    def test_psk_changes_keys(self):
        self.assertNotEqual(self.handshake()[1].initiator_sending, self.handshake(b"\xaa" * 32)[1].initiator_sending)
        init, resp = self.handshake(b"\xaa" * 32)
        with self.assertRaises(noise.HandshakeError):   # the initiator holds no PSK
            noise.consume_response(resp.message, init, self.WG0, self.WG0_E, noise.public_key(self.PEER), None)

    def test_keepalive_opens_with_responder_key(self):
        _, resp = self.handshake()
        message = noise.keepalive(resp.initiator_sending, resp.responder_index)
        self.assertEqual(len(message), 32)
        self.assertEqual(message[:16].hex(), "04000000" "04030201" + "00" * 8)
        self.assertEqual(noise.open_data(message, resp.responder_receiving), (0x01020304, 0, b""))
        with self.assertRaises(noise.HandshakeError):
            noise.open_data(message, resp.responder_sending)

    def test_tampered_response_rejected(self):
        init, good = self.handshake()
        args = (init, self.WG0, self.WG0_E, noise.public_key(self.PEER), None)
        for tamper in ("nothing", "mac1"):
            _, resp = self.handshake(tamper=tamper)
            with self.assertRaises(noise.HandshakeError):
                noise.consume_response(resp.message, *args)
        # a flipped ephemeral breaks the tag; a wrong receiver index names no initiation
        e = good.message[:12] + bytes([good.message[12] ^ 1]) + good.message[13:60]
        with self.assertRaises(noise.HandshakeError):
            noise.consume_response(e + noise._mac1(e, noise.public_key(self.WG0)) + bytes(16), *args)
        r = good.message[:8] + bytes(4) + good.message[12:60]
        with self.assertRaises(noise.HandshakeError):
            noise.consume_response(r + noise._mac1(r, noise.public_key(self.WG0)) + bytes(16), *args)

    def test_response_verifies_initiation(self):
        stamp = noise.tai64n(5, 0)
        responder = noise.public_key(self.PEER)
        for kw in (dict(tamper="static"), dict(tamper="timestamp"), dict(mac1_key=bytes(32))):
            init = noise.initiation(responder, self.WG0, self.WG0_E, stamp, 7, **kw)
            with self.assertRaises(noise.HandshakeError):
                noise.response(init, self.PEER, self.PEER_E, None, 1)
        init = noise.initiation(responder, self.WG0, self.WG0_E, stamp, 7)
        with self.assertRaises(noise.HandshakeError):   # addressed to another responder
            noise.response(init, b"\x55" * 32, self.PEER_E, None, 1)
        with self.assertRaises(noise.HandshakeError):
            noise.response(init, self.PEER, self.PEER_E, None, 1, initiator_public=noise.public_key(b"\x66" * 32))
        with self.assertRaises(noise.HandshakeError):
            noise.response(init, self.PEER, self.PEER_E, None, 1, timestamp=noise.tai64n(6, 0))

    def test_d1_basic_matches_linux(self):
        """Bytes Linux 6.12.110 sent in d1_basic and d1_preshared_key (steered,
        kernel-net-choice, check of 2026-10-04): the initiation from the
        steered ephemeral, clock and index, and the keepalive after it
        consumed noise.response's message."""
        init = noise.steered_initiation(noise.public_key(self.PEER), self.WG0, bytes(range(0x81, 0xa1)),
                                        1_790_000_000, 987_654_321, 0x0a0b0c0d)
        self.assertEqual(init.hex(), "010000000d0c0b0a883186b800b41d5cf0429695da9b3cc4f328ebcd184a6e482fa578c1"
                         "03f06c7798c791ecddaf39405ad7c4a559c0e5053577b5da8fe24f723026772a077183ede96028d9e4e669a84e"
                         "c1296a2f586567698dc84ee6ee0b2a5878f4f6529543bac7e9f01d2a96038a437ed375224fe9c4a34e74c39330"
                         "08be04a7614e" + "00" * 16)
        for psk, sent in ((None, "95ce77161589ca487381a896172df464"), (b"\xaa" * 32, "1062126346cf9db61e8513c148c03f21")):
            resp = noise.response(init, self.PEER, self.PEER_E, psk, 0x01020304)
            self.assertEqual(noise.keepalive(resp.initiator_sending, resp.responder_index).hex(),
                             "04000000" "04030201" + "00" * 8 + sent)

    def test_tai64n_and_clamp(self):
        # tai64n_now rounds the nanoseconds down to a multiple of 2^24
        self.assertEqual(noise.tai64n(1, (1 << 24) * 3 + 5).hex(), "400000000000000b" "03000000")
        self.assertEqual(noise.tai64n(0, (1 << 24) - 1).hex(), "400000000000000a" "00000000")
        self.assertEqual(noise.timespec64(1, 2).hex(), "0100000000000000" "0200000000000000")
        self.assertEqual(noise.clamp(b"\xff" * 32).hex(), "f8" + "ff" * 30 + "7f")
        # x25519 clamps internally, so a raw secret and its clamp give one public key
        self.assertEqual(noise.public_key(b"\xff" * 32), noise.public_key(noise.clamp(b"\xff" * 32)))


if __name__ == "__main__":
    unittest.main()
