"""Fresh-worktree regression for the exact private Kraken reconstruction.

Requires the repository's staged upstream Kraken checkout and Lake, as the
binary package itself does. Run through capped on the shared devbox.
"""
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'binary'))
from run import bootstrap
from pin import verify_pin


class BootstrapTests(unittest.TestCase):
    def test_fresh_manifest_and_exact_patch_commit(self):
        with tempfile.TemporaryDirectory(prefix='binary-bootstrap-', dir=ROOT / '.tmp') as tmp:
            root = Path(tmp)
            for relative in ('dependencies/sources.lock.json', 'lakefile.toml', 'lean-toolchain',
                             'binary/TrustBase.lean', 'binary/lakefile.toml', 'binary/lean-toolchain'):
                dest = root / relative
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, dest)
            shutil.copytree(ROOT / 'binary/kraken-patches', root / 'binary/kraken-patches')
            self.assertFalse((root / 'binary/lake-manifest.json').exists())
            bootstrap(root)
            self.assertTrue((root / 'binary/lake-manifest.json').is_file())
            pin = verify_pin(root)
            bootstrap(root)
            self.assertEqual(verify_pin(root), pin)
            source = root / '.deps/kraken/Kraken.lean'
            source.write_text(source.read_text() + '\n-- dirty checkout control\n')
            with self.assertRaisesRegex(ValueError, 'not clean'):
                bootstrap(root)


if __name__ == '__main__':
    unittest.main()
