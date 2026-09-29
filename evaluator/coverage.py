"""Bind reported KCOV PCs to DWARF locations in the accepted Linux image."""
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


def instrumented_lines(kernel, functions, files):
    """Source lines that own a KCOV instrumentation point in the given functions,
    and the (inlined) function names those points belong to.

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
    lines, names = set(), set()
    for function, pcs in per_function.items():
        query = ''.join(hex(pc - 1) + '\n' for pc in pcs).encode()
        output = subprocess.run(['addr2line', '-e', kernel, '-i', '-f'], input=query,
                                capture_output=True, timeout=60, check=True).stdout.decode().splitlines()
        found = 0
        for name, source in zip(output[0::2], output[1::2]):
            source = source.split('/.deps/linux/')[-1].split(' ')[0]
            if source.split(':')[0] in files:
                lines.add(source)
                names.add(name)
                found += 1
        if not found:
            raise ValueError(f'function {function} has no instrumentation point in the anchored files')
    return lines, names
