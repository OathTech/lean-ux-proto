#!/usr/bin/env python3
"""Build and boot the dependency smoke guest; run via scripts/in-bundle."""
import gzip
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".artifacts/guest"
KERNEL = Path(os.environ.get("LEANUX_KERNEL_BUILD", ROOT / ".artifacts/kernel"))
OUT.mkdir(parents=True, exist_ok=True)
subprocess.run(["gcc", "-static", "-O2", "-Wall", "-Wextra", "-Werror",
                str(ROOT / "harness/probes/kcov-smoke.c"),
                "-o", str(OUT / "kcov-smoke")], check=True)
(OUT / "init").write_text(
    "#!/bin/sh\n"
    "/bin/busybox mount -t devtmpfs devtmpfs /dev\n"
    "/bin/busybox mount -t proc proc /proc\n"
    "/bin/busybox mount -t sysfs sysfs /sys\n"
    "/bin/busybox mount -t debugfs debugfs /sys/kernel/debug\n"
    "/kcov-smoke\n"
    "result=$?\n"
    "echo LEANUX_GUEST_EXIT=$result\n"
    "/bin/busybox reboot -f\n"
    "while :; do /bin/busybox sleep 1; done\n"
)
spec = ["dir /bin 755 0 0", "dir /dev 755 0 0", "dir /proc 755 0 0",
        "dir /sys 755 0 0", "dir /tmp 1777 0 0", "nod /dev/console 600 0 0 c 5 1",
        "nod /dev/null 666 0 0 c 1 3", "slink /bin/sh busybox 777 0 0",
        f"file /init {OUT / 'init'} 755 0 0",
        f"file /kcov-smoke {OUT / 'kcov-smoke'} 755 0 0",
        f"file /bin/busybox {ROOT / '.tools/sysroot/usr/bin/busybox'} 755 0 0"]
(OUT / "initramfs.list").write_text("\n".join(spec) + "\n")
cpio = subprocess.check_output([str(KERNEL / "usr/gen_init_cpio"),
                                "-t", "0", str(OUT / "initramfs.list")])
(OUT / "initramfs.cpio.gz").write_bytes(gzip.compress(cpio, mtime=0))
command = ["qemu-system-x86_64", "-accel", "tcg,thread=single",
           "-machine", "pc-i440fx-8.2", "-cpu", "qemu64", "-smp", "1", "-m", "256",
           "-display", "none", "-monitor", "none", "-serial", "stdio",
           "-nic", "none", "-no-reboot",
           "-kernel", str(KERNEL / "arch/x86/boot/bzImage"),
           "-initrd", str(OUT / "initramfs.cpio.gz"),
           "-append", "console=ttyS0 panic=1"]
(OUT / "qemu-command.json").write_text(json.dumps(command, indent=2) + "\n")
try:
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, errors="replace", timeout=60)
except subprocess.TimeoutExpired as exc:
    (OUT / "boot.log").write_bytes(exc.stdout or b"")
    raise SystemExit("Guest timed out; inspect .artifacts/guest/boot.log") from exc
(OUT / "boot.log").write_text(result.stdout)
if (result.returncode != 0 or "LEANUX_KCOV_SMOKE_PASS" not in result.stdout
        or "LEANUX_GUEST_EXIT=0" not in result.stdout):
    raise SystemExit("Guest smoke failed; inspect .artifacts/guest/boot.log")
addresses = re.findall(r"KCOV_PC=(0x[0-9a-f]+)", result.stdout)
(OUT / "coverage-pcs.txt").write_text("\n".join(addresses) + "\n")
symbols = subprocess.check_output([
    "addr2line", "-f", "-e", str(KERNEL / "vmlinux"),
], input="\n".join(sorted(set(addresses))) + "\n", text=True)
(OUT / "coverage-symbols.txt").write_text(symbols)
if "fs/eventfd.c" not in symbols or "fs/file.c" not in symbols:
    raise SystemExit("KCOV did not symbolize to the expected modeled source files")
print(next(line for line in result.stdout.splitlines() if "LEANUX_KCOV_SMOKE_PASS" in line))
print("PASS: TCG guest, FD aliasing, KCOV, and source symbolization; network disabled.")
