#!/usr/bin/env python3
"""D3 stream K boot probe (docs/2026-10-05-d3-timers.md, questions Q1 and Q5).

Boots a kernel build with the harness's boot parameters and records, before
and after an optional guest batch (a trace file, as harness/linux.py runs
it): /proc/timer_list (the tick device's mode and event handler, hres_active),
the current and available clocksources, and the kernel log's clocksource and
TSC lines (the watchdog's demotion of the TSC is a pr_warn, hidden from the
console by loglevel=3). Evidence only; never an oracle run.

    scripts/in-bundle python3 scripts/d3-boot-probe.py --out DIR [--traces FILE.jsonl] [--arm-records]
"""
import argparse
import fcntl
import gzip
import json
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from harness import linux  # noqa: E402
from harness.trace import loads_trace, serialize_wire, uses_wireguard  # noqa: E402

STATE = """\
echo LEANUX_PROBE_BEGIN $1
/bin/busybox cat /sys/devices/system/clocksource/clocksource0/current_clocksource
/bin/busybox cat /sys/devices/system/clocksource/clocksource0/available_clocksource
/bin/busybox cat /proc/timer_list
/bin/busybox dmesg | /bin/busybox grep -i -E 'clocksource|tsc|watchdog|unstable'
echo LEANUX_PROBE_END $1
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--traces', type=Path)
    parser.add_argument('--arm-records', action='store_true')
    parser.add_argument('--timeout', type=float, default=600)
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    guest = ''
    files = []
    if args.traces:
        traces = [loads_trace(line) for line in args.traces.read_text().splitlines()]
        dispatch = linux.dispatch_addresses() if any(uses_wireguard(t) for t in traces) else []
        (out / 'wire.txt').write_text(serialize_wire(traces, None, dispatch, args.arm_records))
        subprocess.run(['gcc', '-static', '-O2', '-Wall', '-Wextra', '-Werror', '-std=c11',
                        str(linux.ROOT / 'harness/guest.c'), '-o', str(out / 'guest-runner')], check=True)
        guest = '/guest-runner /wire.txt\necho LEANUX_GUEST_EXIT=$?\n'
        files = [('/guest-runner', out / 'guest-runner', '755'), ('/wire.txt', out / 'wire.txt', '444')]
    (out / 'init').write_text(
        '#!/bin/sh\n'
        '/bin/busybox mount -t devtmpfs devtmpfs /dev\n'
        '/bin/busybox mount -t proc proc /proc\n'
        '/bin/busybox mount -t sysfs sysfs /sys\n'
        '/bin/busybox mount -t debugfs debugfs /sys/kernel/debug\n'
        'state() {\n' + STATE + '}\n'
        'state before\n' + guest + 'state after\n'
        '/bin/busybox reboot -f\n'
        'while :; do /bin/busybox sleep 1; done\n')
    spec = ['dir /bin 755 0 0', 'dir /dev 755 0 0', 'dir /proc 755 0 0', 'dir /sys 755 0 0', 'dir /tmp 1777 0 0',
            'nod /dev/console 600 0 0 c 5 1', 'nod /dev/null 666 0 0 c 1 3', 'slink /bin/sh busybox 777 0 0']
    for target, source, mode in [('/init', out / 'init', '755'),
                                 ('/bin/busybox', linux.SHARED / '.tools/sysroot/usr/bin/busybox', '755')] + files:
        spec.append(f'file {target} {source} {mode} 0 0')
    (out / 'initramfs.list').write_text('\n'.join(spec) + '\n')
    cpio = subprocess.check_output([str(linux.KERNEL / 'usr/gen_init_cpio'), '-t', '0', str(out / 'initramfs.list')])
    (out / 'initramfs.cpio.gz').write_bytes(gzip.compress(cpio, mtime=0))
    command = ['qemu-system-x86_64', '-accel', 'tcg,thread=single', '-machine', 'pc-i440fx-8.2', '-cpu', 'qemu64',
               '-smp', '1', '-m', '256', '-display', 'none', '-monitor', 'none', '-serial', 'stdio', '-nic', 'none',
               '-no-reboot', '-kernel', str(linux.KERNEL / 'arch/x86/boot/bzImage'),
               '-initrd', str(out / 'initramfs.cpio.gz'), '-append', linux.BOOT_PARAMETERS]
    (out / 'qemu-command.json').write_text(json.dumps(command, indent=2) + '\n')
    lockpath = linux.SHARED / '.artifacts/runs/qemu.lock'
    with lockpath.open('a+') as lock:
        deadline = time.monotonic() + linux.QEMU_LOCK_WAIT
        while True:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    raise SystemExit('QEMU slot busy')
                time.sleep(2)
        code = linux._bounded_process(command, out / 'boot.log', args.timeout, linux.OUTPUT_LIMIT)
    print(f'qemu exit {code}; {out / "boot.log"}')


if __name__ == '__main__':
    main()
