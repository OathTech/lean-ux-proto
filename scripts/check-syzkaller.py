#!/usr/bin/env python3
"""Generate and compile a syzkaller program without executing its syscalls."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.artifacts/nono-validation'
OUT.mkdir(parents=True, exist_ok=True)
BIN = ROOT / '.deps/syzkaller/bin'
program = subprocess.check_output([
    str(BIN / 'syz-mutate'), '-seed=42', '-len=8', '-enable=eventfd2,dup,close',
], text=True)
assert 'eventfd2' in program, program
(OUT / 'syzkaller-generated.prog').write_text(program)
result = subprocess.run([
    str(BIN / 'syz-prog2c'), '-prog', str(OUT / 'syzkaller-generated.prog'),
], text=True, capture_output=True, check=True)
assert 'failed to format' not in result.stderr, result.stderr
(OUT / 'syzkaller-generated.c').write_text(result.stdout)
subprocess.run(['gcc', '-static', '-O2', str(OUT / 'syzkaller-generated.c'),
                '-o', str(OUT / 'syzkaller-generated')], check=True)
print('PASS: seeded syzkaller generation, formatted C conversion and static compilation.')
print('Generated syscalls were not executed on the host.')
