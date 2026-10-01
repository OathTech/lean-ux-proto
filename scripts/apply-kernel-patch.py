#!/usr/bin/env python3
"""Apply a unified diff strictly: every hunk's context and removed lines must
match exactly at the stated line, with no fuzz or offset, and the patched file
must keep its line count (instrumentation patches here preserve every line
number, so the decision table's spans stay valid). Fails on any mismatch.

    apply-kernel-patch.py PATCH SOURCE_TREE SHA256
"""
import hashlib
import re
import sys
from pathlib import Path


def hunks(text):
    files, current = [], None
    lines = text.split('\n')
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('--- '):
            target = lines[i + 1]
            if not target.startswith('+++ b/'):
                raise SystemExit(f'malformed header at line {i + 2}')
            current = (target[len('+++ b/'):], [])
            files.append(current)
            i += 2
            continue
        match = re.match(r'@@ -(\d+),(\d+) \+(\d+),(\d+) @@', line)
        if match:
            old_start, old_len, new_start, new_len = map(int, match.groups())
            body, old_seen, new_seen = [], 0, 0
            i += 1
            # The header's counts delimit the body exactly.
            while old_seen < old_len or new_seen < new_len:
                if i >= len(lines) or lines[i][:1] not in (' ', '-', '+'):
                    raise SystemExit(f'truncated hunk before line {i + 1}')
                body.append(lines[i])
                old_seen += lines[i][0] in ' -'
                new_seen += lines[i][0] in ' +'
                i += 1
            current[1].append((old_start, old_len, new_start, new_len, body))
            continue
        if line:
            raise SystemExit(f'unexpected patch line {i + 1}: {line!r}')
        i += 1
    return files


def main():
    patch, tree, expected = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
    text = patch.read_text()
    if hashlib.sha256(text.encode()).hexdigest() != expected:
        raise SystemExit('patch hash differs from the recorded one')
    for name, file_hunks in hunks(text):
        path = tree / name
        source = path.read_text().split('\n')
        before = len(source)
        for old_start, old_len, new_start, new_len, body in reversed(file_hunks):
            old = [l[1:] for l in body if l[0] in ' -']
            new = [l[1:] for l in body if l[0] in ' +']
            if old_start != new_start or old_len != len(old) or new_len != len(new) or len(old) != len(new):
                raise SystemExit(f'{name}: hunk at {old_start} changes line numbers')
            if source[old_start - 1:old_start - 1 + len(old)] != old:
                raise SystemExit(f'{name}: hunk at {old_start} does not match the source')
            source[old_start - 1:old_start - 1 + len(old)] = new
        if len(source) != before:
            raise SystemExit(f'{name}: line count changed')
        path.write_text('\n'.join(source))
        print(f'patched {name}')


if __name__ == '__main__':
    main()
