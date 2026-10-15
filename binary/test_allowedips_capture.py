"""The local lookup symbol must be resolved by source, never first match."""
import unittest
from unittest.mock import patch

from harness.linux import binary_coverage_ranges


class AllowedipsCaptureTests(unittest.TestCase):
    def test_source_disambiguates_local_lookup(self):
        def output(command, **_):
            if command[0] == 'nm':
                return '1000 20 t lookup\n2000 30 t lookup\n'
            return ('/linux/drivers/net/wireguard/allowedips.c:129\n'
                    if command[-1] == '0x2000' else '/linux/lib/other.c:8\n')
        with patch('harness.linux.subprocess.check_output', side_effect=output):
            self.assertEqual(binary_coverage_ranges(symbols=('lookup',),
                sources={'lookup': 'drivers/net/wireguard/allowedips.c'}),
                [dict(symbol='lookup', lo=0x2000, hi=0x2030)])

    def test_missing_source_and_remaining_ambiguity_fail(self):
        for location in ('??:0\n', '/linux/drivers/net/wireguard/allowedips.c:129\n'):
            with self.subTest(location=location), patch('harness.linux.subprocess.check_output',
                side_effect=['1000 20 t lookup\n2000 30 t lookup\n', location, location]):
                with self.assertRaises(ValueError):
                    binary_coverage_ranges(symbols=('lookup',),
                        sources={'lookup': 'drivers/net/wireguard/allowedips.c'})


if __name__ == '__main__':
    unittest.main()
