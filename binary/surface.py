"""Print and diff the binary trust specification. Baseline updates are explicit."""
import argparse
import difflib
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
HEADLINES = [
    'Binary.LookupRelation.lookup_simulation',
    'Binary.LookupRelation.lookup_transport',
    'Binary.LookupRelation.LookupPost.frame',
    'Binary.LookupRelation.LookupPost.frame_cuts',
    'Binary.LookupRelation.lookup_framed_transport',
    'Binary.LookupRelation.lookup_snapshot_transport',
    'Binary.LookupSourceFrame.lookup_receivingSnapshot',
    'Binary.LookupWitness.witness_pre',
    'Binary.LookupHitWitness.dead_pre',
    'Binary.LookupHitWitness.live_pre',
    'Binary.AllowedipsWitness.pre4',
    'Binary.AllowedipsWitness.pre6',
    'Binary.Pair.Remove.remove_checked',
    'Binary.Pair.Remove.remove_simulation',
    'Binary.Pair.Replace.replace_checked',
    'Binary.Pair.Replace.replace_simulation',
    'Binary.Pair.IndexLookup.lookup_checked',
    'Binary.Pair.IndexLookup.lookup_simulation',
    'Binary.Pair.Sequence.sequence_checked',
    'Binary.Pair.Remove.Witness.check_linked',
    'Binary.Pair.Remove.Witness.check_unhashed',
    'Binary.Pair.Remove.Witness.executes',
    'Binary.Pair.Replace.Witness.check_linked',
    'Binary.Pair.Replace.Witness.check_unhashed',
    'Binary.Pair.Replace.Witness.executes',
    'Binary.Pair.Insert.insert_checked',
    'Binary.Pair.Insert.insert_simulation',
    'Binary.Pair.InsertSequence.sequence_checked',
    'Binary.Pair.Insert.Witness.check',
    'Binary.Pair.Insert.Witness.source_success',
    'Binary.Pair.Insert.Witness.executes',
    'Binary.RandomService.return_recorded',
]
IMPORTS = ['LookupSnapshotTransport', 'LookupWitness', 'LookupHitWitness', 'AllowedipsWitnessPre',
           'PairInsertionSurface']
# These definitions determine the meaning of the headline and its environment
# premises outside TrustBase. The expected text is a specification, not a log.
DEFINITIONS = [
    'Binary.LookupRelation.R', 'Binary.LookupRelation.LookupPost',
    'Binary.EffectSuccessor', 'Binary.InstructionSuccessor', 'Binary.ActualHistory',
    'Binary.NoEarlyReturn', 'Binary.EndsAtReturn',
    'Binary.Pair.Corresponds', 'Binary.Pair.Remove.ownership', 'Binary.Pair.Remove.targetOwnership',
    'Binary.Pair.Remove.Pre', 'Binary.Pair.Remove.callBoundary', 'Binary.Pair.Remove.Post',
    'Binary.Pair.Replace.Pre', 'Binary.Pair.Replace.callBoundary', 'Binary.Pair.Replace.Post',
    'Binary.Pair.IndexLookup.Pre', 'Binary.Pair.IndexLookup.callBoundary', 'Binary.Pair.IndexLookup.Post',
    'Binary.Pair.Sequence.initialCheck', 'Binary.Pair.Sequence.Admissible',
    'Binary.Pair.Sequence.AdmissibleSequence', 'Binary.Pair.Sequence.program',
    'Binary.Pair.Sequence.install', 'Binary.Pair.Sequence.prepare', 'Binary.Pair.Sequence.Ready',
    'Binary.Pair.Sequence.Execute', 'Binary.Pair.Sequence.SequencePost',
    'Binary.Pair.Sequence.EntryDomain', 'Binary.Pair.Sequence.Observed',
    'Binary.Pair.Insert.Pre', 'Binary.Pair.Insert.callBoundary', 'Binary.Pair.Insert.providerCheck',
    'Binary.Pair.Insert.Post', 'Binary.Pair.Insert.ProviderState',
    'Binary.Pair.InsertSequence.initialCheck', 'Binary.Pair.InsertSequence.Admissible',
    'Binary.Pair.InsertSequence.AdmissibleSequence', 'Binary.Pair.InsertSequence.program',
    'Binary.Pair.InsertSequence.prepare', 'Binary.Pair.InsertSequence.Ready',
    'Binary.Pair.InsertSequence.SourceBoundaries', 'Binary.Pair.InsertSequence.Boundary',
    'Binary.Pair.InsertSequence.Execute', 'Binary.Pair.InsertSequence.SequencePost',
    'Binary.Pair.InsertSequence.EntryDomain', 'Binary.Pair.InsertSequence.Observed',
    'Binary.RandomProvider.Config', 'Binary.RandomProvider.snapshot',
    'Binary.RandomProvider.initialized', 'Binary.RandomProvider.recording',
    'Binary.RandomProvider.steer', 'Binary.RandomProvider.remote', 'Binary.RandomProvider.check',
]
EXPECTED = ROOT / 'binary/TrustSurface.expected.txt'


def render_surface(root=ROOT):
    root = Path(root)
    temp = root / '.tmp'
    temp.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='binary-surface-', dir=temp) as directory:
        source = Path(directory) / 'Surface.lean'
        source.write_text(''.join(f'import {name}\n' for name in IMPORTS)
                          + 'set_option format.width 110\nset_option pp.universes true\n'
                          + ''.join(f'#check @{name}\n' for name in HEADLINES)
                          + ''.join(f'#print {name}\n' for name in DEFINITIONS))
        result = subprocess.run(['lake', 'env', 'lean', str(source)], cwd=root / 'binary',
                                capture_output=True, text=True)
        if result.returncode:
            raise ValueError(f'trust-surface printing failed:\n{result.stdout}{result.stderr}')
        if result.stderr:
            raise ValueError(f'unexpected trust-surface diagnostics: {result.stderr}')
    return ('HEADLINE STATEMENTS AND INTERPRETATION DEFINITIONS\n' + result.stdout.rstrip()
            + '\n\nTRUST DECLARATIONS: binary/TrustBase.lean (verbatim)\n'
            + (root / 'binary/TrustBase.lean').read_text())


def diff_surface(actual, expected):
    return ''.join(difflib.unified_diff(expected.splitlines(keepends=True),
                                      actual.splitlines(keepends=True),
                                      fromfile='expected trust surface', tofile='current trust surface'))


def check_surface():
    actual = render_surface()
    print(actual, end='' if actual.endswith('\n') else '\n', flush=True)
    delta = diff_surface(actual, EXPECTED.read_text())
    if delta:
        print(delta, end='', flush=True)
        raise ValueError('binary trust surface changed; inspect the diff and explicitly update its specification')
    print('binary trust-surface diff: PASS', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-expected', action='store_true',
                        help='intentionally replace the reviewed specification; commit and review its diff')
    args = parser.parse_args()
    if args.write_expected:
        EXPECTED.write_text(render_surface())
        print(f'Updated {EXPECTED}; review its Git diff')
    else:
        check_surface()


if __name__ == '__main__':
    main()
