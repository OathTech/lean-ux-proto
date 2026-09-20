#!/usr/bin/env python3
"""Build small Lean/Std and static C executables without project dependencies.

This is a toolchain probe, not an offline-readiness or Linux-semantics test.
All generated files stay under the repository's ignored .artifacts directory.
"""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    shared = Path(os.environ.get('LEANUX_SHARED_ROOT', repo))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, default=shared / ".tools/lean/bin")
    parser.add_argument("--cc", default="gcc", help="C compiler executable")
    args = parser.parse_args()
    lean_bin = args.lean_bin.resolve()
    for name in ("lean", "lake"):
        if not os.access(lean_bin / name, os.X_OK):
            parser.error(f"missing executable {lean_bin / name}; stage Lean or use --lean-bin")
    cc = shutil.which(args.cc)
    if cc is None:
        parser.error(f"C compiler not found: {args.cc}")
    clang = shutil.which('clang')
    cxx = shutil.which('g++')
    if clang is None or cxx is None:
        parser.error('Clang and G++ must be available in the bundle')

    output_root = Path(os.environ.get('LEANUX_ARTIFACTS', repo / '.artifacts')) / 'probes'
    output_root.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="toolchains-", dir=output_root))
    for name in ("tmp", "cache", "elan"):
        (work / name).mkdir()
    (work / "lake-config.toml").write_text("")
    (work / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
    (work / "lakefile.toml").write_text(
        'name = "leanux_probe"\nversion = "0.1.0"\n'
        'defaultTargets = ["leanux_probe"]\n\n'
        '[[lean_exe]]\nname = "leanux_probe"\nroot = "Main"\n'
    )
    (work / "Main.lean").write_text(
        'import Std\n\nexample (n : Nat) : n + 0 = n := by simp\n\n'
        'def main : IO Unit := IO.println "leanux-toolchain-ok"\n'
    )
    (work / "probe.c").write_text(
        '#include <stdio.h>\n#include <stdint.h>\n#include <sys/eventfd.h>\n'
        'int main(void) {\n'
        '  _Static_assert(sizeof(uint64_t) == 8, "expected eight-byte uint64_t");\n'
        '  printf("c-toolchain-ok u64=%zu nonblock=%d\\n",\n'
        '         sizeof(uint64_t), EFD_NONBLOCK);\n'
        '  return 0;\n}\n'
    )
    (work / "probe.cc").write_text(
        '#include <iostream>\n#include <vector>\n'
        'int main() { std::vector<int> v{1, 2, 3}; '
        'std::cout << "cxx-toolchain-ok size=" << v.size() << "\\n"; }\n'
    )
    env = os.environ.copy()
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN", "LAKE",
                 "LAKE_HOME", "LAKE_OVERRIDE_LEAN", "ELAN_TOOLCHAIN"):
        env.pop(name, None)
    env.update({
        "PATH": str(lean_bin) + os.pathsep + env.get("PATH", os.defpath),
        "TMPDIR": str(work / "tmp"),
        "XDG_CACHE_HOME": str(work / "cache"),
        "ELAN_HOME": str(work / "elan"),
        "LAKE_CACHE_DIR": str(work / "cache/lake"),
        "LAKE_CONFIG": str(work / "lake-config.toml"),
        "LAKE_NO_CACHE": "true",
    })
    commands = [
        [str(lean_bin / "lean"), "--version"],
        [str(lean_bin / "lake"), "--keep-toolchain", "--no-cache", "build"],
        [str(work / ".lake/build/bin/leanux_probe")],
        [cc, "-Wall", "-Wextra", "-Werror", "-static", "probe.c", "-o", "c-probe"],
        [str(work / "c-probe")],
        [clang, '-Wall', '-Wextra', '-Werror', '-static', 'probe.c', '-o', 'clang-probe'],
        [str(work / 'clang-probe')],
        [cxx, '-Wall', '-Wextra', '-Werror', '-static', 'probe.cc', '-o', 'cxx-probe'],
        [str(work / 'cxx-probe')],
    ]
    print(f"Probe directory: {work}", flush=True)
    try:
        for command in commands:
            subprocess.run(command, cwd=work, env=env, check=True, timeout=60)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError) as exc:
        print(f"Toolchain probe failed: {exc}")
        return 1
    print("PASS: Lean/Std native build and GCC/Clang C and GCC C++ static builds executed.")
    print("Guest execution and sandbox isolation have separate checks.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
