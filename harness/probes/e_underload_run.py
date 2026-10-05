#!/usr/bin/env python3
"""THROWAWAY PROBE runner for workstream E (docs/2026-10-05-e-dos.md).

Not the oracle. Compiles harness/probes/e_underload_probe.c (baking in a fixed
private key and a valid-MAC1 initiation), builds an initramfs, takes one of the
shared QEMU slots, and boots the pinned kernel. Prints the serial log's
LEANUX_PROBE rows: whether a cookie reply (type 3) came back under each burst
mechanism, i.e. whether `under_load` was crossed.

Run: scripts/in-bundle python3 harness/probes/e_underload_run.py
"""
import fcntl
import gzip
import hashlib
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SHARED = Path(os.environ.get("LEANUX_SHARED_ROOT", ROOT)).resolve()
ARTIFACTS = Path(os.environ.get("LEANUX_ARTIFACTS", ROOT / ".artifacts")).resolve()
KERNEL = Path(os.environ.get("LEANUX_KERNEL_DIR", SHARED / ".artifacts/kernel-net-choice")).resolve()
BUSYBOX = SHARED / ".tools/sysroot/usr/bin/busybox"
QEMU_SLOTS = int(os.environ.get("LEANUX_QEMU_SLOTS", "3"))
QEMU_LOCK_WAIT = 3600


def x25519(k, u):
    P = 2**255 - 19
    a24 = 121665
    k = bytearray(k); k[0] &= 248; k[31] &= 127; k[31] |= 64
    k = int.from_bytes(k, "little"); x1 = int.from_bytes(u, "little")
    x2, z2, x3, z3, sw = 1, 0, x1, 1, 0
    for t in range(254, -1, -1):
        kt = (k >> t) & 1; sw ^= kt
        if sw: x2, x3 = x3, x2; z2, z3 = z3, z2
        sw = kt
        A = (x2 + z2) % P; AA = A * A % P; B = (x2 - z2) % P; BB = B * B % P; E = (AA - BB) % P
        C = (x3 + z3) % P; D = (x3 - z3) % P; DA = D * A % P; CB = C * B % P
        x3 = pow(DA + CB, 2, P); z3 = x1 * pow(DA - CB, 2, P) % P
        x2 = AA * BB % P; z2 = E * (AA + a24 * E) % P
    if sw: x2, x3 = x3, x2; z2, z3 = z3, z2
    return ((x2 * pow(z2, P - 2, P)) % P).to_bytes(32, "little")


def baked():
    priv = bytearray((i * 7 + 3) & 0xFF for i in range(32))
    priv[0] &= 248; priv[31] &= 127; priv[31] |= 64
    priv = bytes(priv)
    pub = x25519(priv, (9).to_bytes(32, "little"))
    mac1_key = hashlib.blake2s(b"mac1----" + pub, digest_size=32).digest()
    body = (1).to_bytes(4, "little") + (0xDEADBEEF).to_bytes(4, "little") + bytes(32) + bytes(48) + bytes(28)
    mac1 = hashlib.blake2s(body, digest_size=16, key=mac1_key).digest()
    init = body + mac1 + bytes(16)
    assert len(init) == 148
    carr = lambda b: ",".join(str(x) for x in b)
    return carr(priv), carr(init), pub.hex()


def main():
    out = ARTIFACTS / "e-underload-probe"
    out.mkdir(parents=True, exist_ok=True)
    priv_c, init_c, pub_hex = baked()
    src = (ROOT / "harness/probes/e_underload_probe.c").read_text()
    src = src.replace("PRIV_BYTES", priv_c).replace("INIT_BYTES", init_c)
    (out / "probe.c").write_text(src)
    print(f"wg0 public key (for reference): {pub_hex}", file=sys.stderr)

    binary = out / "probe-bin"
    build = ["gcc", "-static", "-O2", "-std=c11", "-Wall", str(out / "probe.c"), "-o", str(binary)]
    r = subprocess.run(build, capture_output=True, text=True)
    if r.returncode:
        sys.stderr.write(r.stdout + r.stderr)
        raise SystemExit("probe build failed")

    (out / "init").write_text(
        "#!/bin/sh\n"
        "/bin/busybox mount -t devtmpfs devtmpfs /dev\n"
        "/bin/busybox mount -t proc proc /proc\n"
        "/bin/busybox mount -t sysfs sysfs /sys\n"
        "/probe-bin\n"
        "echo LEANUX_PROBE_EXIT=$?\n"
        "/bin/busybox reboot -f\n"
        "while :; do /bin/busybox sleep 1; done\n"
    )
    spec = ["dir /bin 755 0 0", "dir /dev 755 0 0", "dir /proc 755 0 0", "dir /sys 755 0 0",
            "nod /dev/console 600 0 0 c 5 1", "nod /dev/null 666 0 0 c 1 3", "slink /bin/sh busybox 777 0 0"]
    for target, source, mode in (("/init", out / "init", "755"), ("/probe-bin", binary, "755"),
                                 ("/bin/busybox", BUSYBOX, "755")):
        spec.append(f"file {target} {source} {mode} 0 0")
    (out / "initramfs.list").write_text("\n".join(spec) + "\n")
    cpio = subprocess.check_output([str(KERNEL / "usr/gen_init_cpio"), "-t", "0", str(out / "initramfs.list")], timeout=30)
    (out / "initramfs.cpio.gz").write_bytes(gzip.compress(cpio, mtime=0))

    command = ["qemu-system-x86_64", "-accel", "tcg,thread=single", "-machine", "pc-i440fx-8.2",
               "-cpu", "qemu64", "-smp", "1", "-m", "256", "-display", "none", "-monitor", "none",
               "-serial", "stdio", "-nic", "none", "-no-reboot",
               "-kernel", str(KERNEL / "arch/x86/boot/bzImage"),
               "-initrd", str(out / "initramfs.cpio.gz"),
               "-append", "console=ttyS0 panic=1 nokaslr loglevel=4"]

    runs = SHARED / ".artifacts/runs"
    runs.mkdir(parents=True, exist_ok=True)
    paths = [runs / ("qemu.lock" if i == 0 else f"qemu.lock.{i}") for i in range(QEMU_SLOTS)]
    deadline = time.monotonic() + QEMU_LOCK_WAIT
    log = None
    while log is None:
        for path in paths:
            lock = path.open("a+")
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                lock.close()
                continue
            with lock:
                print(f"booting probe on {KERNEL.name} (slot {path.name})", file=sys.stderr, flush=True)
                proc = subprocess.run(command, capture_output=True, text=True, timeout=240)
                log = proc.stdout + proc.stderr
            break
        if log is None:
            if time.monotonic() >= deadline:
                raise SystemExit("no QEMU slot")
            time.sleep(2)

    (out / "boot.log").write_text(log)
    print("".join(line + "\n" for line in log.splitlines() if "LEANUX_PROBE" in line or "PROBE_FAIL" in line))
    print(f"(full serial log: {out / 'boot.log'})", file=sys.stderr)


if __name__ == "__main__":
    main()
