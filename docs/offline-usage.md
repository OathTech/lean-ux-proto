# Working offline after setup

[Setup and first run](../REPRODUCING.md) needs the network once, to install
Lean through elan and to stage the locked tools and the Linux source. After
that the builds and checks need no network access.

Run commands through `scripts/in-bundle`, using the portable `cap` helper
from the setup guide for heavy work:

```sh
scripts/in-bundle lean --version
cap scripts/in-bundle lake build leanux-model
cap scripts/in-bundle python3 -m evaluator.check --suite handwritten --trace alias_close
```

The check requires `LEANUX_KERNEL_DIR` to name a build matching this revision's
kernel identity (`kernel/identity-x86_64-net-choice.txt`). The proof tree
needs no guest: `cap scripts/in-bundle lake build LeanuxProofs` and
`cap scripts/in-bundle scripts/proof-gate` work offline once Lean is installed.
`scripts/in-bundle` configures tool paths, compiler libraries, QEMU firmware
and local caches. It neither downloads tools nor provides sandboxing.

## What each input is identified by

Every input a build or a check consumes is pinned by something anyone can
reproduce from a public source. Nothing is identified by a file that exists
on one machine only.

| Input | Pin | Checked |
| --- | --- | --- |
| Tool packages (compiler, QEMU, kernel build tools) | URL and SHA-256 in `dependencies/packages.lock.json` | when staged, and by `scripts/verify-dependencies.py` |
| Linux source | URL and SHA-256 in `dependencies/sources.lock.json` | when staged, and again by `scripts/build-kernel` |
| Lean | version and commit in `dependencies/toolchains.lock.json`, for the toolchain `lean-toolchain` names | by `scripts/in-bundle` at every launch, from the toolchain's own `lean --version` |
| Kernel build | path-independent identity (`scripts/kernel-identity.py`) in `kernel/identity-*.txt` | at every guest boot |
| Kraken (binary package) | upstream commit plus committed patches giving one exact commit | by `binary/pin.py` |

`scripts/verify-dependencies.py` reports the first three without network
access. A build in another directory or on another machine has the same
kernel identity; the SHA-256 of its `vmlinux` file differs, because the build
directory enters the debug information, and is not a pin.

## Moving a setup to a machine without network access

Install elan and the toolchain on the destination, or copy an existing elan
home. Then copy these beside a checkout of the same revision, preserving
symlinks:

| Path | Purpose |
| --- | --- |
| `.tools/sysroot` | The packaged compiler, Python, QEMU and build tools |
| `.deps/linux`, `.deps/downloads` | The locked Linux source and the archives needed to rebuild the kernel |
| A matching build under `.artifacts/` (optional) | Saves a kernel rebuild; the check recomputes its identity on the destination |

Do not copy `.cache`: its generated links contain absolute paths, and
`scripts/in-bundle` recreates it. Model builds in `.lake` and test reports
are disposable too.

Worktrees share the main checkout's `.tools/`, `.deps/` and selected kernel
build. Their `.cache/`, `.lake/` and test output are private; see
[worktree practices](worktree-practices.md).

The optional [binary experiment](../binary/README.md) needs its own private
patched Kraken dependency, fetched once by its bootstrap. Its proof builds
then run offline, and its image tests use the same kernel build.
