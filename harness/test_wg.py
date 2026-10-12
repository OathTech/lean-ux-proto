"""WireGuard configuration encoding and dump decoding; no guest."""
import struct
import unittest

from . import wg


def attr(kind, data, nested=False):
    return wg._attr(kind, data, nested)


class InnerPacketTests(unittest.TestCase):
    """W5+W6 (docs/2026-10-06-w5-w6-receive.md): the TCP segment builder and
    the IPv4 RST Linux answers it with (2.4.1)."""

    def test_tcp_segment_and_its_rst(self):
        from . import noise
        src, dst = bytes([10, 0, 0, 2]), bytes.fromhex("0afffe01")
        syn = noise.ipv4_tcp(src, dst, 40001, 80, 0x11223344, 0, 2, tos=0xb9)
        self.assertEqual(len(syn), 40)
        self.assertEqual(noise.inet_checksum(syn[:20]), 0)                    # the header checksum verifies
        pseudo = src + dst + struct.pack(">BBH", 0, 6, 20)
        self.assertEqual(noise.inet_checksum(pseudo + syn[20:]), 0)          # and the TCP checksum
        rst = noise.rst4(syn)
        self.assertEqual((rst[0], rst[1], rst[2:4], rst[4:6], rst[6:8], rst[8], rst[9]),
                         (0x45, 0xb8, b"\x00\x28", b"\x00\x00", b"\x40\x00", 64, 6))   # tos & ~ECN, id 0, DF, TTL 64
        self.assertEqual((rst[12:16], rst[16:20]), (dst, src))
        th = rst[20:]
        self.assertEqual(struct.unpack(">HHIIBBHHH", th), (80, 40001, 0, 0x11223345, 5 << 4, 4 | 16, 0, th[16] << 8 | th[17], 0))
        self.assertEqual(noise.inet_checksum(dst + src + struct.pack(">BBH", 0, 6, 20) + th), 0)
        # with ACK: seq = the segment's ack_seq, no ACK flag; a RST is not answered
        ack = noise.ipv4_tcp(src, dst, 40001, 80, 5, 0x55667788, 16, b"data")
        self.assertEqual(struct.unpack(">HHIIBB", noise.rst4(ack)[20:34]), (80, 40001, 0x55667788, 0, 5 << 4, 4))
        self.assertIsNone(noise.rst4(noise.ipv4_tcp(src, dst, 1, 2, 0, 0, 4)))
        # FIN and payload count into ack_seq
        fin = noise.ipv4_tcp(src, dst, 1, 2, 100, 0, 1, b"xyz")
        self.assertEqual(struct.unpack_from(">I", noise.rst4(fin), 28)[0], 104)


class WireGuardTests(unittest.TestCase):
    def test_rejects_non_hex_addresses_and_bad_lengths(self):
        peer = {"public_key": "22" * 32, "allowed_ips": [{"family": 4, "addr": "10.0.0.0", "cidr": 8}]}
        with self.assertRaises(wg.InvalidConfig):
            wg.validate_config({"peers": [peer]})
        peer["allowed_ips"][0]["addr"] = "0A000000"            # not lowercase
        with self.assertRaises(wg.InvalidConfig):
            wg.validate_config({"peers": [peer]})
        # W1: lengths the policy table rejects stay out (P8): below 4 bytes,
        # above 20; a wrong length for the family is the kernel's observable
        # -EINVAL (set_allowedip's fallthrough) and is accepted
        peer["allowed_ips"][0]["addr"] = "0a0000"
        with self.assertRaises(wg.InvalidConfig):
            wg.validate_config({"peers": [peer]})
        peer["allowed_ips"][0]["addr"] = "0a" * 21
        with self.assertRaises(wg.InvalidConfig):
            wg.validate_config({"peers": [peer]})
        peer["allowed_ips"][0]["addr"] = "0a00000000"          # five bytes for IPv4: accepted, -EINVAL in the kernel
        wg.validate_config({"peers": [peer]})
        peer["allowed_ips"][0].update(family=6, addr="0a000000")
        wg.validate_config({"peers": [peer]})
        with self.assertRaises(wg.InvalidConfig):               # an endpoint shorter than the policy minimum
            wg.validate_config({"peers": [{"public_key": "22" * 32,
                                           "endpoint": {"family": 4, "addr": "0a000001", "port": 1, "len": 15}}]})
        with self.assertRaises(wg.InvalidConfig):               # flowinfo is IPv6 only
            wg.validate_config({"peers": [{"public_key": "22" * 32,
                                           "endpoint": {"family": 4, "addr": "0a000001", "port": 1, "flowinfo": 1}}]})
        with self.assertRaises(wg.InvalidConfig):               # raw flags are exclusive with the booleans
            wg.validate_config({"peers": [{"public_key": "22" * 32, "flags": 1, "remove": True}]})
        with self.assertRaises(wg.InvalidConfig):               # ifname above IFNAMSIZ - 1 (P8)
            wg.validate_device({"ifname": "a" * 16})

    def test_w1_encodes_selectors_malformations_and_endpoint_fields(self):
        # the device selector: by name (the default), by index, both, neither
        self.assertEqual(wg.encode_get(), attr(wg.DEV_IFNAME, b"wg0\0"))
        self.assertEqual(wg.encode_get({"ifindex": 3}), attr(wg.DEV_IFINDEX, struct.pack("=I", 3)))
        self.assertEqual(wg.encode_get({"ifname": "lo", "ifindex": 1}),
                         attr(wg.DEV_IFNAME, b"lo\0") + attr(wg.DEV_IFINDEX, struct.pack("=I", 1)))
        self.assertEqual(wg.encode_get({}), b"")
        # a malformed peer entry lacks NLA_F_NESTED; a parsed one has it
        config = {"peers": [{"public_key": "22" * 32, "malformed": "not_nested"}]}
        payload = wg.encode_set(config)
        entry = attr(0, attr(wg.PEER_PUBLIC_KEY, b"\x22" * 32), nested=False)
        self.assertIn(attr(wg.DEV_PEERS, entry, nested=True), payload)
        self.assertNotIn(attr(0, attr(wg.PEER_PUBLIC_KEY, b"\x22" * 32), nested=True), payload)
        # flags raw (even 0 is sent), protocol version, a peer without a key
        payload = wg.encode_set({"flags": 2, "peers": [{"flags": 0, "protocol_version": 2}]})
        self.assertIn(attr(wg.DEV_FLAGS, struct.pack("=I", 2)), payload)
        self.assertIn(attr(wg.PEER_FLAGS, struct.pack("=I", 0)), payload)
        self.assertIn(attr(wg.PEER_PROTOCOL_VERSION, struct.pack("=I", 2)), payload)
        self.assertNotIn(struct.pack("=HH", 36, wg.PEER_PUBLIC_KEY), payload)
        # the endpoint's flowinfo (network order), scope_id, af and len
        endpoint = {"family": 6, "addr": "00" * 15 + "01", "port": 51820, "flowinfo": 0x12345, "scope_id": 1}
        sockaddr = wg._sockaddr(endpoint)
        self.assertEqual(len(sockaddr), 28)
        self.assertEqual(sockaddr[4:8], struct.pack("!I", 0x12345))
        self.assertEqual(sockaddr[24:28], struct.pack("=I", 1))
        self.assertEqual(len(wg._sockaddr(dict(endpoint, len=20))), 20)
        self.assertEqual(wg._sockaddr(dict(endpoint, len=40))[28:], b"\0" * 12)
        self.assertEqual(wg._sockaddr({"family": 4, "addr": "0a000001", "port": 1, "af": 0})[:2], b"\0\0")
        # an allowed IP with a subset of its attributes, and af overriding the family
        ips = wg.encode_set({"peers": [{"public_key": "22" * 32, "allowed_ips": [{"family": 4, "addr": "0a000000"},
                                                                                {"family": 4, "addr": "0a000000", "cidr": 8, "af": 0}]}]})
        self.assertIn(attr(0, attr(wg.AIP_FAMILY, struct.pack("=H", wg.AF_INET)) + attr(wg.AIP_IPADDR, bytes.fromhex("0a000000")), nested=True), ips)
        self.assertIn(attr(wg.AIP_FAMILY, struct.pack("=H", 0)), ips)

    def test_w1_decodes_ipv6_endpoint_fields_and_rejects_sin_zero(self):
        v6 = struct.pack("=H", wg.AF_INET6) + struct.pack("!HI", 51820, 0x12345) + b"\0" * 15 + b"\1" + struct.pack("=I", 7)
        self.assertEqual(wg._decode_endpoint(v6), {"family": 6, "addr": "00" * 15 + "01", "port": 51820,
                                                   "flowinfo": 0x12345, "scope_id": 7})
        v4 = struct.pack("=H", wg.AF_INET) + struct.pack("!H", 1) + bytes.fromhex("0a000001") + b"\0" * 8
        self.assertEqual(wg._decode_endpoint(v4), {"family": 4, "addr": "0a000001", "port": 1})
        with self.assertRaises(wg.InvalidConfig):
            wg._decode_endpoint(v4[:15] + b"\1")

    def test_encodes_addresses_in_network_order(self):
        config = {"peers": [{"public_key": "22" * 32,
                             "endpoint": {"family": 4, "addr": "0a000001", "port": 51820},
                             "allowed_ips": [{"family": 6, "addr": "fd" + "00" * 14 + "01", "cidr": 64}]}]}
        payload = wg.encode_set(config)
        self.assertIn(struct.pack("=H", wg.AF_INET) + struct.pack("!H", 51820) + bytes.fromhex("0a000001"), payload)
        self.assertIn(attr(wg.AIP_IPADDR, bytes.fromhex("fd" + "00" * 14 + "01")), payload)

    def test_decodes_dump_addresses_as_hex_and_coalesces_peers(self):
        ip = attr(0, attr(wg.AIP_CIDR, b"\x08") + attr(wg.AIP_FAMILY, struct.pack("=H", wg.AF_INET)) +
                  attr(wg.AIP_IPADDR, bytes.fromhex("0a000000")), nested=True)
        endpoint = struct.pack("=H", wg.AF_INET) + struct.pack("!H", 7) + bytes.fromhex("c0a80001") + b"\0" * 8
        peer = attr(wg.PEER_PUBLIC_KEY, b"\x22" * 32) + attr(wg.PEER_ENDPOINT, endpoint) + \
            attr(wg.PEER_ALLOWEDIPS, ip, nested=True)
        first = attr(wg.DEV_IFINDEX, struct.pack("=I", 3)) + attr(wg.DEV_PEERS, attr(0, peer, nested=True), nested=True)
        continued = attr(wg.DEV_PEERS, attr(0, attr(wg.PEER_PUBLIC_KEY, b"\x22" * 32) +
                                            attr(wg.PEER_ALLOWEDIPS, ip, nested=True), nested=True), nested=True)
        device = wg.decode_dump([first.hex(), continued.hex()])
        self.assertEqual(device["ifindex"], 3)
        self.assertEqual(len(device["peers"]), 1)
        self.assertEqual(device["peers"][0]["endpoint"], {"family": 4, "addr": "c0a80001", "port": 7})
        self.assertEqual(device["peers"][0]["allowed_ips"], [{"family": 4, "addr": "0a000000", "cidr": 8}] * 2)

    def test_decode_rejects_anomalies(self):
        ip = lambda family, addr: attr(0, attr(wg.AIP_CIDR, b"\x08") + attr(wg.AIP_FAMILY, struct.pack("=H", family)) +
                                       attr(wg.AIP_IPADDR, addr), nested=True)
        peer = lambda body: attr(wg.DEV_PEERS, attr(0, attr(wg.PEER_PUBLIC_KEY, b"\x22" * 32) + body, nested=True),
                                 nested=True)
        index = attr(wg.DEV_IFINDEX, struct.pack("=I", 3))
        bad = [
            [],                                                                     # no message
            [(index + index).hex()],                                                # duplicate device attribute
            [attr(wg.DEV_IFINDEX, b"\x03").hex()],                                 # truncated u32
            [peer(attr(wg.PEER_ALLOWEDIPS, ip(7, b"\0" * 4), nested=True)).hex()],  # unknown family
            [peer(attr(wg.PEER_ALLOWEDIPS, ip(wg.AF_INET, b"\0" * 16), nested=True)).hex()],  # length vs family
            [peer(b"").hex(), peer(attr(wg.PEER_KEEPALIVE, struct.pack("=H", 1))).hex()],       # continued peer extras
            ["0G"],                                                                 # not hex
        ]
        for payloads in bad:
            with self.assertRaises(wg.InvalidConfig, msg=payloads):
                wg.decode_dump(payloads)


if __name__ == "__main__":
    unittest.main()
