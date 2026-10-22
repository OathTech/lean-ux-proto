# Using a staged environment offline

The shared development machines use a staged Lean snapshot for offline work.
This is an alternative to the elan setup in
[setup and first run](../REPRODUCING.md). A Git clone contains the code and
dependency locks, but not the snapshots, downloaded tools, Linux sources or
kernel build. Once the dependencies are present, the normal build and check
commands need no network access.

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
`cap scripts/in-bundle scripts/proof-gate` work offline once Lean is staged. The
host requirements still apply offline. `scripts/in-bundle` configures tool
paths, compiler libraries, QEMU firmware and local caches. It neither
downloads tools nor provides sandboxing.

## What to copy to an offline machine

| Path | Purpose |
| --- | --- |
| `.tools/lean-<version>` (or the matching legacy `.tools/lean`), `.tools/sysroot` | Lean and the packaged compiler, Python, QEMU and build tools |
| `.deps/linux`, `.deps/downloads` | Locked Linux source and archives needed to rebuild the patched kernel |
| A matching build under `.artifacts/` (optional) | Saves a kernel rebuild; the check recomputes its identity on the destination |

Copy these alongside a checkout of the same revision, preserving symlinks.
The Lean stage must match `lean-toolchain`; copying only an older
`.tools/lean` stage is insufficient.
Keep the checked-in `dependencies/*.lock.json` files. Do not copy `.cache`:
its generated links contain absolute paths, and `scripts/in-bundle` recreates
it. Model builds in `.lake` and test reports are disposable too.

## Restore the devboxes' Lean snapshots

Run this in the original clone, where the shared `.tools/` and `.deps/` live:

```sh
python3 scripts/restore-toolchains.py --only lean
```

The restore script checks the snapshots against
[`dependencies/toolchains.lock.json`](../dependencies/toolchains.lock.json)
and restores missing installations. It leaves existing directories untouched.
The lock's Lean 4.35.0 row has only a local snapshot archive, which is not in
Git, and no upstream source. This command is therefore not a fresh-clone
installer: without that snapshot it fails. It also visits the legacy 4.33.1
row and downloads that release if neither its installation nor archive is
present. For a fully offline restore, both rows need an existing installation
or their cached archives. Copying the matching extracted 4.35.0 stage instead
does not require the legacy stage.

The two compressed Lean snapshots total about 1.5 GB; extracted, their two
toolchains occupy roughly 6 GiB. An offline bundle that only needs the current
pin can omit the older extracted stage.

The staged snapshot is the devboxes' offline mechanism for Lean, and
`scripts/in-bundle` uses it first when it is present and reports the pinned
version. On a connected machine the ordinary route is elan: install the
toolchain `lean-toolchain` names (`elan toolchain install "$(cat
lean-toolchain)"`, see [REPRODUCING.md](../REPRODUCING.md)), and the launcher
locates it through elan (`elan toolchain list`, then `elan run <name> lean
--print-prefix`) and checks its version; it never installs or downloads, and
never uses an unversioned `lean` from `PATH`. `LEANUX_LEAN_SOURCE=staged` or
`=elan` forces one route; the default `auto` tries the snapshot, then elan.

## Optional tools

Some older bundles also contain Go, syzkaller, Firecracker source, reference
manuals or `.tools/lean-lsp`. These are not required for the differential check.
Go and the Lean MCP helper have no upstream download fallback in the restore
script; offline use requires their cached snapshots or staged directories.
Keep `.deps/go-mod` if you use the staged syzkaller build.

If the Lean MCP helper is staged, `scripts/lean-lsp /absolute/path/to/project`
starts it without a global registration. For ordinary Lean editor support,
`scripts/in-bundle lake serve` is available with the core bundle.

Worktrees share the main checkout's `.tools/`, `.deps/` and selected kernel
build. Their `.cache/`, `.lake/` and test output are private; see
[worktree practices](worktree-practices.md).

The optional [binary experiment](../binary/README.md) needs its own private
patched Kraken dependency. Its proof builds can run offline after bootstrap;
its image tests additionally require the exact saved s5 ELF, which this
mirror bundle does not reproduce.
