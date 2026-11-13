"""An entry's contents must not select the native source-alignment witness."""
import unittest
from capture_index_mutator import select_invocation, recording_position


class NoReads:
    def word(self, _address):
        raise AssertionError('ordinal selection read entry memory')


class SelectionTests(unittest.TestCase):
    def test_every_replacement_entry_counts_without_reading_linkage(self):
        for anchor in ('replace', 'insert'):
            self.assertEqual([select_invocation(anchor, 2, i, NoReads(), {}, {})
                              for i in range(4)], [False, False, True, False])

    def test_unknown_selector_fails(self):
        with self.assertRaisesRegex(ValueError, 'unknown'):
            select_invocation('unknown', 0, 0, NoReads(), {}, {})

    def test_recording_frontier_uses_stopped_bytes_and_rejects_drops(self):
        class Memory:
            dropped = 0
            def read(self, address, size):
                if (address, size) == (0x1000, 8):
                    return (37).to_bytes(8, 'little')
                if (address, size) == (0x2020, 4):
                    return self.dropped.to_bytes(4, 'little')
                raise AssertionError('unexpected read')
        memory = Memory()
        layout = dict(sequenceAddress=0x1000, taskDropped=0x20)
        position, blocks = recording_position(memory, 0x2000, layout)
        self.assertEqual(position['sequence'], 37)
        self.assertEqual(blocks[0]['bytes'], [37, 0, 0, 0, 0, 0, 0, 0])
        memory.dropped = 1
        with self.assertRaisesRegex(ValueError, 'dropped'):
            recording_position(memory, 0x2000, layout)


if __name__ == '__main__':
    unittest.main()
