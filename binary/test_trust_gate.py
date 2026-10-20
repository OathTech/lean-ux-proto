"""Small rejection tests for the binary dependency/specification gate."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from binary.pin import verify_pin
from binary.surface import diff_surface


class TrustGateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='binary-pin-', dir=Path(__file__).resolve().parents[1] / '.tmp')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / '.deps/kraken'
        self.repo.mkdir(parents=True)
        (self.root / 'binary').mkdir()
        (self.root / 'dependencies').mkdir()
        self.git('init', '-q', '--initial-branch=probe')
        (self.repo / 'Source.lean').write_text('def source := 1\n')
        (self.repo / '.gitignore').write_text('.lake/\n')
        self.git('add', '.')
        self.git('-c', 'user.name=Gate test', '-c', 'user.email=gate@example.invalid', 'commit', '-qm', 'fixture')
        pin = self.git('rev-parse', 'HEAD')
        (self.root / 'binary/TrustBase.lean').write_text(f'def krakenCommit : String := "{pin}"\n')
        (self.root / 'binary/lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        (self.root / 'dependencies/sources.lock.json').write_text(json.dumps([
            dict(name='kraken', commit=pin, toolchain='leanprover/lean4:v4.35.0')]))
        (self.root / 'binary/lake-manifest.json').write_text(json.dumps(dict(packages=[
            dict(name='Kraken', type='path', dir='../.deps/kraken')])))

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args], text=True).strip()

    def test_clean_with_ignored_build(self):
        (self.repo / '.lake').mkdir()
        (self.repo / '.lake/output').write_text('ephemeral')
        self.assertEqual(verify_pin(self.root), self.git('rev-parse', 'HEAD'))

    def test_tracked_source_change(self):
        (self.repo / 'Source.lean').write_text('def source := 2\n')
        with self.assertRaisesRegex(ValueError, 'not clean'):
            verify_pin(self.root)

    def test_untracked_source(self):
        (self.repo / 'Extra.lean').write_text('def extra := 1\n')
        with self.assertRaisesRegex(ValueError, 'not clean'):
            verify_pin(self.root)

    def test_wrong_head(self):
        (self.repo / 'Source.lean').write_text('def source := 2\n')
        self.git('add', '.')
        self.git('-c', 'user.name=Gate test', '-c', 'user.email=gate@example.invalid', 'commit', '-qm', 'changed')
        with self.assertRaisesRegex(ValueError, 'differs from pinned'):
            verify_pin(self.root)

    def test_trust_lock_disagreement(self):
        (self.root / 'binary/TrustBase.lean').write_text('def krakenCommit : String := "' + '0'*40 + '"\n')
        with self.assertRaisesRegex(ValueError, 'disagree'):
            verify_pin(self.root)

    def test_changed_premise_visible(self):
        expected = 'headline : SerializedEnvironment cpus actions → Conclusion\n'
        actual = 'headline : StrongerEnvironment cpus actions → Conclusion\n'
        delta = diff_surface(actual, expected)
        self.assertIn('-' + expected.rstrip(), delta)
        self.assertIn('+' + actual.rstrip(), delta)
        self.assertEqual(diff_surface(expected, expected), '')


if __name__ == '__main__':
    unittest.main()
