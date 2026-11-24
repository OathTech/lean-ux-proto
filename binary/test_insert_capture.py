"""Replay refuses stale or incomplete capture identities before execution."""
import unittest

from binary.pair_insert_capture import validate_identity


class IdentityTests(unittest.TestCase):
    def test_identity(self):
        kernel = dict(checked=True, expected='kernel', actual='kernel')
        identity = dict(kernel=kernel, kraken='semantics')
        validate_identity(identity, kernel, 'semantics')
        for field in identity:
            with self.subTest(field=field, variant='missing'):
                candidate = dict(identity)
                del candidate[field]
                with self.assertRaisesRegex(ValueError, field):
                    validate_identity(candidate, kernel, 'semantics')
            with self.subTest(field=field, variant='mismatched'):
                with self.assertRaisesRegex(ValueError, field):
                    validate_identity({**identity, field: 'wrong'}, kernel, 'semantics')
        for field, bad in [('checked', False), ('actual', 'wrong'), ('expected', 'wrong')]:
            with self.subTest(kernel_field=field):
                with self.assertRaisesRegex(ValueError, 'kernel'):
                    validate_identity({**identity, 'kernel': {**kernel, field: bad}},
                                      kernel, 'semantics')


if __name__ == '__main__':
    unittest.main()
