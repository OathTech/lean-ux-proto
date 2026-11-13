"""Keep the actual PC trial distinct from the later comparison-mode trial."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from remediation.replacement_prefix_diagnostic import CompletedPrefixLog


class PrefixLogTests(unittest.TestCase):
    def test_full_guest_modes_do_not_mix(self):
        with TemporaryDirectory() as directory:
            path = Path(directory) / 'boot.log'
            rows = ['LEANUX_HIDDEN ' + json.dumps(dict(id='sample', mode=mode, index=index, records=[]))
                    for mode, index in [('pc', 0), ('pc', 1), ('cmp', 0), ('cmp', 1)]]
            path.write_text('\n'.join(rows) + '\n')
            self.assertEqual(CompletedPrefixLog(path, 'sample', 1).read_text(), rows[0])

    def test_unknown_mode_is_not_ignored(self):
        with TemporaryDirectory() as directory:
            path = Path(directory) / 'boot.log'
            path.write_text('LEANUX_HIDDEN ' + json.dumps(dict(id='sample', mode='unknown', index=0, records=[])))
            with self.assertRaisesRegex(ValueError, 'unexpected record trace or mode'):
                CompletedPrefixLog(path, 'sample', 1)


if __name__ == '__main__':
    unittest.main()
