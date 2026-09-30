"""WireGuard configuration encoding and dump decoding; no guest."""
import struct
import unittest

from . import wg


def attr(kind, data, nested=False):
    return wg._attr(kind, data, nested)


class WireGuardTests(unittest.TestCase):
    def test_rejects_non_hex_addresses_and_bad_lengths(self):
        peer = {"public_key": "22" * 32, "allowed_ips": [{"family": 4, "addr": "10.0.0.0", "cidr": 8}]}
        with self.assertRaises(wg.InvalidConfig):
            wg.validate_config({"peers": [peer]})
        peer["allowed_ips"][0]["addr"] = "0a00000000"          # five bytes for IPv4
        with self.assertRaises(wg.InvalidConfig):
            wg.validate_config({"peers": [peer]})
        peer["allowed_ips"][0]["addr"] = "0A000000"            # not lowercase
        with self.assertRaises(wg.InvalidConfig):
            wg.validate_config({"peers": [peer]})
        peer["allowed_ips"][0].update(family=6, addr="0a000000")
        with self.assertRaises(wg.InvalidConfig):
            wg.validate_config({"peers": [peer]})

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
