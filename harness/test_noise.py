"""RFC vectors for the harness's Noise primitives, the initiation layout, and
the D1 handshake: initiation, response, session keys and keepalive."""
import struct
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



class D2Tests(unittest.TestCase):
    """Stage D2: sessions from wg0's side, data messages and inner packets."""
    WG0, PEER, WG0_E, PEER_E = b"\x11" * 32, b"\x22" * 32, b"\x33" * 32, b"\x44" * 32

    def test_keepalive_vectors(self):
        # a zero-length data message is the keepalive the mirror's #guards pin
        # (Leanux/WG/Data.lean; harness/test_d1_keepalive.py)
        from .test_d1_keepalive import KEY, REMOTE_INDEX, VECTORS
        for counter, expected in VECTORS.items():
            self.assertEqual(noise.data_message(KEY, REMOTE_INDEX, counter, b"").hex(), expected)
            self.assertEqual(noise.keepalive(KEY, REMOTE_INDEX, counter).hex(), expected)

    def test_initiator_session_matches_linux(self):
        """wg0's keepalive in d1_basic (Linux 6.12.110, see test_d1_basic_matches_linux)
        is the zero-length message under initiator_session."""
        init = noise.steered_initiation(noise.public_key(self.PEER), self.WG0, bytes(range(0x81, 0xa1)),
                                        1_790_000_000, 987_654_321, 0x0a0b0c0d)
        session = noise.initiator_session(noise.response(init, self.PEER, self.PEER_E, None, 0x01020304))
        self.assertEqual((session.local_index, session.remote_index, session.initiator), (0x0a0b0c0d, 0x01020304, True))
        self.assertEqual(session.from_wg0(0, b"").hex(),
                         "04000000" "04030201" + "00" * 8 + "95ce77161589ca487381a896172df464")

    def test_initiator_session_agrees_with_consume_response(self):
        init = noise.initiation(noise.public_key(self.PEER), self.WG0, self.WG0_E, noise.tai64n(5, 0), 77)
        resp = noise.response(init, self.PEER, self.PEER_E, b"\xaa" * 32, 88)
        index, sending, receiving = noise.consume_response(resp.message, init, self.WG0, self.WG0_E,
                                                           noise.public_key(self.PEER), b"\xaa" * 32)
        session = noise.initiator_session(resp)
        self.assertEqual((session.sending, session.receiving, session.remote_index, session.local_index),
                         (sending, receiving, index, 77))
        # what the peer sends, wg0 opens with its receiving key
        message = session.to_wg0(3, b"hello")
        self.assertEqual(noise.open_data(message, receiving)[:2], (77, 3))
        self.assertEqual(session.open_from_wg0(session.from_wg0(9, b"x")), (9, b"x" + bytes(15)))

    def test_responder_session(self):
        """respond-then-data: the peer initiates, wg0 responds with its steered
        response ephemeral and index; the peer's consume_response derives
        the keys the peer sends with, which wg0 receives with."""
        peer_e = b"\x45" * 32
        theirs = noise.initiation(noise.public_key(self.WG0), self.PEER, peer_e, noise.tai64n(1, 0), 0x0badcafe)
        raw = bytes(range(1, 33))
        ours = noise.wg0_response(theirs, self.WG0, raw, None, 0x11223344)
        self.assertEqual(ours.message[12:44], noise.public_key(raw))     # x25519 clamps the raw draw
        index, peer_sending, peer_receiving = noise.consume_response(ours.message, theirs, self.PEER, peer_e,
                                                                     noise.public_key(self.WG0), None)
        session = noise.responder_session(ours)
        self.assertEqual(index, 0x11223344)
        self.assertEqual((session.receiving, session.sending), (peer_sending, peer_receiving))
        self.assertEqual((session.local_index, session.remote_index, session.initiator), (0x11223344, 0x0badcafe, False))
        message = session.to_wg0(0, b"")
        self.assertEqual(message, noise.keepalive(peer_sending, 0x11223344))

    def test_wg0_response_matches_linux(self):
        """wg0's response in d2_respond_then_data (Linux 6.12.110,
        kernel-net-choice, check of 2026-10-04, steered resp_ephemeral and
        index_draw); Linux then delivered the inner datagram of the peer's
        first data message, built under responder_session's keys."""
        device, peer = b"\x11" * 32, b"\x22" * 32
        theirs = noise.initiation(noise.public_key(device), peer, b"\x46" * 32, noise.tai64n(1, 0), 0x0badcafe)
        ours = noise.wg0_response(theirs, device, bytes(range(1, 33)), None, 0x11223344)
        self.assertEqual(ours.message.hex(),
                         "0200000044332211fecaad0b07a37cbc142093c8b755dc1b10e86cb426374ad16aa853ed0bdfc0b2b86d1c7c8d24"
                         "98c35ac35eea33f009987f9b4b2d2967079c36ea7bdfa130f51d74c2261d" + "00" * 16)

    def test_padding(self):
        # ALIGN(len, 16), clamped by the MTU (1420) only in (1404, 1420]
        for length, pad in ((0, 0), (1, 15), (15, 1), (16, 0), (17, 15), (1404, 4), (1405, 3), (1408, 0),
                            (1409, 11), (1419, 1), (1420, 0), (1421, 15)):
            self.assertEqual(noise.padding(length), pad, length)
        self.assertEqual(noise.padding(1419, 0), 5)   # no MTU: ALIGN alone
        for length in (1, 15, 16, 17, 1404, 1405, 1419, 1420):
            message = noise.data_message(bytes(32), 1, 2, bytes(length))
            self.assertEqual(len(message), 16 + length + noise.padding(length) + 16)
        self.assertEqual(noise.message_data_len(0), 32)

    def test_tampered_tag(self):
        good = noise.data_message(bytes(32), 1, 2, b"abc")
        bad = noise.data_message(bytes(32), 1, 2, b"abc", tamper=True)
        self.assertEqual(good[:-1], bad[:-1])
        self.assertNotEqual(good[-1], bad[-1])
        with self.assertRaises(noise.HandshakeError):
            noise.open_data(bad, bytes(32))

    def test_counter_constants(self):
        self.assertEqual(noise.COUNTER_WINDOW_SIZE, 8128)
        self.assertEqual(noise.REJECT_AFTER_MESSAGES, 2**64 - 8130)

    @staticmethod
    def udp_sum_ok(pseudo, udp):
        return noise._sum16(pseudo + udp) == 0xffff

    def test_ipv4_udp(self):
        src, dst = bytes([10, 0, 0, 2]), noise.WG0_ADDR4
        packet = noise.ipv4_udp(src, dst, 12345, 51998, b"payload")
        self.assertEqual(len(packet), 20 + 8 + 7)
        self.assertEqual(packet[:12].hex(), "45000023" "0000" "4000" "40" "11" + packet[10:12].hex())
        self.assertEqual(noise.inet_checksum(packet[:20]), 0)
        self.assertEqual(packet[12:20], src + dst)
        self.assertEqual(packet[20:26].hex(), "3039" "cb1e" "000f")
        pseudo = src + dst + bytes([0, 17, 0, 15])
        self.assertTrue(self.udp_sum_ok(pseudo, packet[20:]))
        self.assertEqual(noise.ipv4_udp(src, dst, 1, 2, b"x", checksum="zero")[26:28], bytes(2))
        wrong = noise.ipv4_udp(src, dst, 1, 2, b"x", checksum="wrong")
        self.assertFalse(self.udp_sum_ok(src + dst + bytes([0, 17, 0, 9]), wrong[20:]))
        self.assertNotEqual(wrong[26:28], bytes(2))

    def test_csum_mangled_0(self):
        # a payload whose checksum is 0 is sent as 0xffff (dev.c:3425, udp_send_skb)
        src, dst = noise.WG0_ADDR4, bytes([10, 0, 0, 1])
        base = noise._sum16(src + dst + bytes([0, 17, 0, 10]) + bytes.fromhex("cb1e9c40000a0000"))
        payload = struct.pack(">H", 0xffff - base)
        packet = noise.xmit_packet(4, dst, payload)
        self.assertEqual(packet[26:28], b"\xff\xff")
        self.assertTrue(self.udp_sum_ok(src + dst + bytes([0, 17, 0, 10]), packet[20:]))

    def test_dishonest_ipv4(self):
        src = bytes([10, 0, 0, 2])
        for tot_len in (19, 0, 100):
            packet = noise.to_wg0(4, src, b"abc", tot_len=tot_len)
            self.assertEqual(struct.unpack(">H", packet[2:4])[0], tot_len)
            self.assertEqual(noise.inet_checksum(packet[:20]), 0)   # the header checksum stays correct
        packet = noise.to_wg0(4, src, b"abc", version=5)
        self.assertEqual(packet[0], 0x55)
        self.assertEqual(noise.inet_checksum(packet[:20]), 0)

    def test_ipv6_udp(self):
        src = bytes.fromhex("20010db8000000000000000000000002")
        packet = noise.to_wg0(6, src, b"hi", sport=7)
        self.assertEqual(packet[:8].hex(), "60000000" "000a" "11" "40")
        self.assertEqual(packet[8:40], src + noise.WG0_ADDR6)
        self.assertEqual(packet[40:46].hex(), "0007" "cb1e" "000a")
        pseudo = src + noise.WG0_ADDR6 + bytes([0, 0, 0, 10, 0, 0, 0, 17])
        self.assertTrue(self.udp_sum_ok(pseudo, packet[40:]))
        self.assertEqual(noise.to_wg0(6, src, b"hi", payload_len=200)[4:6].hex(), "00c8")
        self.assertEqual(noise.to_wg0(6, src, b"hi", version=4)[0] >> 4, 4)
        self.assertNotEqual(noise.to_wg0(6, src, b"hi", checksum="wrong")[46:48], bytes(2))

    def test_gso_segments_are_equal_checksummed_and_numbered(self):
        # W4: one UDP_SEGMENT datagram as wg_xmit receives it (design 2.1):
        # equal segments, ids 0..n-1, DF, a complete UDP checksum per segment
        payload = bytes(range(256)) * 11   # 2816 = 2 x 1408? no: 4 x 704
        segments = noise.gso_segments(bytes([10, 0, 0, 1]), payload, 704)
        self.assertEqual(len(segments), 4)
        for i, seg in enumerate(segments):
            self.assertEqual(len(seg), 20 + 8 + 704)
            self.assertEqual(seg[4:6], i.to_bytes(2, "big"))          # id
            self.assertEqual(seg[6:8], b"\x40\x00")                   # DF
            self.assertEqual(noise.inet_checksum(seg[:20]), 0)         # header checksum verifies
            pseudo = seg[12:16] + seg[16:20] + bytes([0, 17]) + len(seg[20:]).to_bytes(2, "big")
            self.assertEqual(noise.inet_checksum(pseudo + seg[20:]), 0)   # UDP checksum verifies
            self.assertEqual(seg[28:], payload[i * 704:(i + 1) * 704])
        with self.assertRaises(ValueError):
            noise.gso_segments(bytes([10, 0, 0, 1]), payload, 1000)   # a short last segment

    def test_xmit_packet(self):
        packet = noise.xmit_packet(4, bytes([10, 0, 0, 1]), b"leux")
        self.assertEqual(packet[:20].hex()[:20], "45000020" "0000" "4000" "4011")
        self.assertEqual(packet[12:16], noise.WG0_ADDR4)
        self.assertEqual(packet[20:24].hex(), "cb1e9c40")
        dst6 = bytes.fromhex("20010db8000000000000000000000001")
        packet = noise.xmit_packet(6, dst6, b"leux")
        self.assertEqual(packet[:8].hex(), "60000000" "000c" "1140")
        self.assertEqual(packet[8:24], noise.WG0_ADDR6)
        with self.assertRaises(ValueError):
            noise.xmit_packet(6, bytes.fromhex("fe800000000000000000000000000001"), b"x")
        with self.assertRaises(ValueError):
            noise.xmit_packet(6, bytes.fromhex("febf0000000000000000000000000001"), b"x")
        noise.xmit_packet(6, bytes.fromhex("fec00000000000000000000000000001"), b"x")
        # the largest IPv4 payload fills the MTU, without padding
        self.assertEqual(len(noise.xmit_packet(4, bytes([10, 0, 0, 1]), bytes(1392))), noise.DEVICE_MTU)
        session = noise.Session(bytes(32), bytes(32), 1, 2, True)
        message = noise.wg0_data(session, 4, 4, bytes([10, 0, 0, 1]), bytes(1392))
        self.assertEqual(len(message), 32 + 1420)
        self.assertEqual(session.open_from_wg0(message)[1], noise.xmit_packet(4, bytes([10, 0, 0, 1]), bytes(1392)))


    # Stage E (section 6.A): XChaCha20-Poly1305 and the cookie reply.
    def test_hchacha20_draft_vector(self):
        # draft-irtf-cfrg-xchacha-03, section 2.2.1 (also libsodium's crypto_core_hchacha20)
        nonce = bytes.fromhex("000000090000004a0000000031415927")
        self.assertEqual(noise.hchacha20(bytes(range(32)), nonce).hex(),
                         "82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc")

    def test_xchacha20poly1305_draft_vector(self):
        # draft-irtf-cfrg-xchacha-03, appendix A.3.1 (checked against libsodium)
        key, nonce = bytes(range(0x80, 0xa0)), bytes(range(0x40, 0x58))
        aad = bytes.fromhex("50515253c0c1c2c3c4c5c6c7")
        plaintext = (b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, "
                     b"sunscreen would be it.")
        out = noise.xchacha20poly1305_encrypt(key, nonce, plaintext, aad)
        self.assertEqual(out[:16].hex(), "bd6d179d3e83d43b9576579493c0e939")
        self.assertEqual(out[-16:].hex(), "c0875924c1c7987947deafd8780acf49")
        self.assertEqual(noise.xchacha20poly1305_decrypt(key, nonce, out, aad), plaintext)
        with self.assertRaises(noise.HandshakeError):
            noise.xchacha20poly1305_decrypt(key, nonce, out, aad[:-1] + b"\x00")
        # the cookie-sized vector the Lean mirror's #guard uses (libsodium agrees)
        self.assertEqual(noise.xchacha20poly1305_encrypt(bytes(range(32)), bytes(range(0x40, 0x58)),
                                                         bytes([7] * 16), bytes([1] * 16)).hex(),
                         "d33e0277d7e77e1188f380b9a89b6295f5e04a578ccbd2023f1c0eeeb9ea6e52")

    def test_cookie_message(self):
        peer = b"\x22" * 32
        init = noise.initiation(noise.public_key(peer), b"\x11" * 32, noise.clamp(b"\x33" * 32),
                                noise.tai64n(1_700_000_000, 0), 0x0a0b0c0d)
        peer_public = noise.public_key(peer)
        nonce, cookie = bytes(range(24)), bytes(range(100, 116))
        mac1 = noise.last_mac1(init)
        reply = noise.cookie_message(0x0a0b0c0d, cookie, nonce, mac1, peer_public)
        self.assertEqual(len(reply), 64)
        self.assertEqual(reply[:8].hex(), "030000000d0c0b0a")
        self.assertEqual(reply[8:32], nonce)
        self.assertEqual(noise.consume_cookie_message(reply, mac1, peer_public), cookie)
        # the key is BLAKE2s("cookie--" || the sender's public key)
        self.assertEqual(noise.cookie_key(peer_public), noise._hash(b"cookie--" + peer_public))
        with self.assertRaises(noise.HandshakeError):
            noise.consume_cookie_message(reply, bytes(16), peer_public)
        bad = noise.cookie_message(0x0a0b0c0d, cookie, nonce, mac1, peer_public, aad=bytes(16))
        with self.assertRaises(noise.HandshakeError):
            noise.consume_cookie_message(bad, mac1, peer_public)
        # MAC2 covers the message up to mac2 and leaves mac1 in place
        with_mac2 = noise.with_mac2(init, cookie)
        self.assertEqual(with_mac2[:-16], init[:-16])
        self.assertEqual(with_mac2[-16:], noise.hashlib.blake2s(init[:-16], key=cookie, digest_size=16).digest())

if __name__ == "__main__":
    unittest.main()
