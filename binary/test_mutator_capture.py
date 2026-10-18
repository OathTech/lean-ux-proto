"""Argument roots retain delisted allocations without weakening lookup defaults."""
import unittest

from capture_lookup import capture


class Memory:
    def __init__(self):
        self.cells = {}

    def region(self, address, size):
        self.cells.update((address+i, 0) for i in range(size))

    def put(self, address, value, width=8):
        self.cells.update(enumerate(value.to_bytes(width, 'little'), address))

    def read(self, address, size):
        try:
            return bytes(self.cells[address+i] for i in range(size))
        except KeyError as error:
            raise ValueError('unmapped fake memory') from error

    def word(self, address, size=8):
        return int.from_bytes(self.read(address, size), 'little')


class CaptureTests(unittest.TestCase):
    def setUp(self):
        self.memory = m = Memory()
        for address, size in [(0x10000, 65536), (0x30000, 64), (0x40000, 256),
                              (0x50000, 64), (0x7f800, 2064), (0x90000, 0x708),
                              (0xa0000, 1024), (0xb0000, 8), (0xc0000, 64)]:
            m.region(address, size)
        self.offsets = dict(tableSize=65536, hash=8, peer=0, kind=24, next=0,
                            entrySize=32, peerHandshake=64, handshakeEntry=0, keypairEntry=0)
        self.layout = {
            'wg_peer': dict(size=256, members=dict(device=0, peer_list=8, keypairs=192)),
            'wg_device': dict(size=64, members=dict(index_hashtable=0, peer_list=8)),
            'noise_handshake': dict(members=dict(remote_static=32)),
            'noise_keypairs': dict(members=dict(current_keypair=0, previous_keypair=8, next_keypair=16)),
            'noise_keypair': dict(size=64),
            'pcpu_hot': dict(size=64, members=dict(preempt_count=8, current_task=0)),
        }
        self.probe = dict(offsets=self.offsets, preempt=0xc0008)
        self.regs = dict(rdi=0x10000, rsp=0x80000, rcx=0xb0000)
        m.put(0x10000, 0x40048)  # Linked handshake; keypair is only an argument root.
        m.put(0x40040, 0x40000)
        m.put(0x40058, 1, 4)
        m.put(0x50000, 0x40000)
        m.put(0x50018, 2, 4)
        m.put(0x40000, 0x30000)
        m.put(0x30000, 0x10000)
        m.put(0x30008, 0x40008)
        m.put(0x40008, 0x30008)
        m.put(0xc0000, 0x90000)
        m.put(0x906e0, 2, 4)
        m.put(0x906e4, 128, 4)
        m.put(0x906e8, 0xa0000)
        m.put(0xa0000, 1)

    def test_lookup_defaults_and_full_mutator_closure(self):
        normal = capture(self.memory, self.regs, self.probe, self.layout, 3)
        self.assertEqual(normal['coverageCapturedWords'], 5)
        self.assertEqual(normal['capacity'], 128)
        self.assertEqual(normal['keypairs'], [])
        self.memory.put(0x30008, 0x30008)  # Peer has left the device list.
        with self.assertRaisesRegex(ValueError, 'outside device membership'):
            capture(self.memory, self.regs, self.probe, self.layout, 3)
        result = capture(self.memory, {**self.regs, 'rcx': 0}, self.probe, self.layout, 3,
                         root_entries=[0x50000], read_output=False,
                         include_retired=True, full_coverage=True)
        self.assertEqual(result['retainedPeers'], [0x40000])
        self.assertEqual(result['deviceMembers'], [])
        self.assertEqual(result['keypairs'], [0x50000])
        self.assertEqual(result['capacity'], result['coverageCapturedWords'])

    def test_unknown_argument_kind_fails(self):
        self.memory.put(0x50018, 9, 4)
        with self.assertRaisesRegex(ValueError, 'unknown argument entry kind'):
            capture(self.memory, self.regs, self.probe, self.layout, 3, root_entries=[0x50000])


if __name__ == '__main__':
    unittest.main()
