"""Bind reported KCOV PCs to DWARF locations in the accepted Linux image."""
from collections import Counter
import hashlib
import re
from pathlib import Path
import subprocess


def symbolize(rows, kernel):
    kernel = Path(kernel)
    addresses = sorted({pc for row in rows for pc in row['pcs']})
    if not addresses or any(int(pc, 16) == 0 for pc in addresses):
        raise ValueError('missing or invalid coverage addresses')
    # KCOV records the instruction following the instrumentation call.
    query = ''.join(hex(int(pc, 16) - 1) + '\n' for pc in addresses).encode()
    process = subprocess.run(['addr2line', '-e', kernel, '-a', '-f', '-i'], input=query,
                             capture_output=True, timeout=60, check=True)
    records, current = {}, None
    lines = process.stdout.decode().splitlines()
    index = 0
    while index < len(lines):
        if lines[index].startswith('0x'):
            current = f'0x{int(lines[index], 16) + 1:016x}'
            records[current] = []
            index += 1
        elif current is not None and index + 1 < len(lines):
            records[current].append(dict(function=lines[index], source=lines[index + 1]))
            index += 2
        else:
            raise ValueError('malformed coverage symbolization output')
    if set(records) != set(addresses) or any(not stack or all(frame['source'].startswith('??') for frame in stack)
                                            for stack in records.values()):
        raise ValueError('coverage address does not resolve in accepted kernel')
    return dict(kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
                convention='KCOV return PC minus one; DWARF inline frames',
                unique_pcs=len(addresses), locations=records)


def _disassemble(kernel, function):
    """Instruction lines of each symbol named exactly `function`, one list per
    symbol (the same name can label several local symbols)."""
    listing = subprocess.run(['objdump', '-d', '--no-show-raw-insn', f'--disassemble={function}', kernel],
                             capture_output=True, text=True, timeout=120, check=True).stdout
    bodies, current = [], None
    for line in listing.splitlines():
        if re.match(r'^[0-9a-f]+ <.+>:$', line):
            current = []
            bodies.append(current)
        elif current is not None and re.match(r'^ *[0-9a-f]+:\t', line):
            current.append(line)
    return bodies


COVERAGE_HOOK = '<__sanitizer_cov_trace_pc>'


def attributable(frames):
    """Whether a point's DWARF attribution is usable. Header code enters a
    function only through inline frames; a point whose outermost frame (the
    symbol's own) names a header line lies outside every inline range, where
    the line table gives a merged block (a join after an inlined `if`) the
    header's last line. Such points witness nothing."""
    return not frames[-1]['source'].split(':')[0].endswith('.h')


def instrumented_lines(kernel, functions, files):
    """`instrumented_points` without its per-symbol map."""
    lines, names, chains, _ = instrumented_points(kernel, functions, files)
    return lines, names, chains


def instrumented_points(kernel, functions, files):
    """Source lines that own a KCOV instrumentation point in the given functions,
    the (inlined) function names those points belong to, and how many points
    have each frame chain (`file:line` per DWARF frame, innermost first; the
    check's shared-exit declarations must each name exactly one), and per
    listed symbol the (inlined function, `file:line`) pairs that own a point
    in that symbol's body: a helper inlined into several callers is
    instrumented differently in each copy, so whether a line owns a point is
    a fact about one copy (the check's unreached-line rule reads it).

    KCOV records the return address of the call to `__sanitizer_cov_trace_pc`.
    When a callee ends by jumping to the hook (directly, conditionally, or
    through a chain of such tail jumps), the recorded address is the callee's
    return address in the caller, so those call sites count too. Compiler
    split bodies (`name.cold`, `name.part.N`, ...) are included. Uses the
    return-PC-minus-one convention of `symbolize`. Fails if a listed function
    or a called symbol is missing, or if a function contributes no line.
    """
    kernel = Path(kernel)
    symbols = set(subprocess.run(['nm', kernel], capture_output=True, text=True, timeout=120,
                                 check=True).stdout.split())
    tail_jumps = {}

    def ends_in_coverage(callee, depth=0):
        if callee not in tail_jumps:
            bodies = _disassemble(kernel, callee)
            if not bodies:
                raise ValueError(f'called symbol {callee} not found in kernel image')
            tail_jumps[callee] = False
            for line in (l for body in bodies for l in body):
                jump = re.search(r'\tj[a-z]+ +[0-9a-f]+ <([A-Za-z0-9_.]+)>$', line)
                if jump and (jump.group(1) == '__sanitizer_cov_trace_pc'
                             or (depth < 3 and jump.group(1) != callee and ends_in_coverage(jump.group(1), depth + 1))):
                    tail_jumps[callee] = True
                    break
        return tail_jumps[callee]

    per_function = {}
    for function in functions:
        names = [function] + sorted(n for n in symbols if n.startswith(function + '.'))
        bodies = [body for name in names for body in _disassemble(kernel, name)]
        if not bodies:
            raise ValueError(f'function {function} not found in kernel image')
        pcs = []
        for body in bodies:
            for current, following in zip(body, body[1:]):
                if '\tcall' not in current:
                    continue
                target = re.search(r'<([A-Za-z0-9_.]+)>$', current.strip())
                if target and (target.group(0) == COVERAGE_HOOK or ends_in_coverage(target.group(1))):
                    pcs.append(int(following.split(':')[0], 16))
        per_function[function] = pcs
    lines, names, chains, by_symbol = set(), set(), Counter(), {}
    for function, pcs in per_function.items():
        query = ''.join(hex(pc - 1) + '\n' for pc in pcs).encode()
        output = subprocess.run(['addr2line', '-e', kernel, '-a', '-i', '-f'], input=query,
                                capture_output=True, timeout=60, check=True).stdout.decode().splitlines()
        stacks, index = [], 0
        while index < len(output):
            if output[index].startswith('0x'):
                stacks.append([])
                index += 1
            elif stacks and index + 1 < len(output):
                stacks[-1].append(dict(function=output[index], source=output[index + 1]))
                index += 2
            else:
                raise ValueError('malformed addr2line output')
        found = 0
        for frames in stacks:
            if not attributable(frames):
                continue
            chains[tuple(frame['source'].split('/.deps/linux/')[-1].split(' ')[0] for frame in frames)] += 1
            for frame in frames:
                source = frame['source'].split('/.deps/linux/')[-1].split(' ')[0]
                if source.split(':')[0] in files:
                    lines.add(source)
                    names.add(frame['function'])
                    by_symbol.setdefault(function, set()).add((frame['function'].split('.')[0], source))
                    found += 1
        if not found:
            raise ValueError(f'function {function} has no instrumentation point in the anchored files')
    return lines, names, chains, by_symbol
