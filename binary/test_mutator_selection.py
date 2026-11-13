"""An entry's contents must not select the native source-alignment witness."""
import unittest
from capture_index_mutator import select_invocation


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


if __name__ == '__main__':
    unittest.main()
