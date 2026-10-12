# Using a staged environment offline

Follow [setup and first run](../REPRODUCING.md) to obtain the required bundle.
A Git clone contains the code and dependency locks, but not the downloaded
tools, Linux sources or kernel build. Once staged, the normal build and check
commands need no network access.

Run commands through `scripts/in-bundle`:

```sh
scripts/in-bundle lean --version
scripts/in-bundle lake build leanux-model
scripts/in-bundle python3 -m evaluator.check --suite handwritten --trace alias_close
```

The check requires `LEANUX_KERNEL_DIR` to name a build matching this revision's
kernel identity. The host requirements still apply offline. `scripts/in-bundle` configures tool paths,
compiler libraries, QEMU firmware and local caches. It neither downloads tools
nor provides sandboxing.

## What to copy to an offline machine

| Path | Purpose |
| --- | --- |
| `.tools/lean`, `.tools/sysroot` | Lean and the packaged compiler, Python, QEMU and build tools |
| `.deps/linux`, `.deps/downloads` | Locked Linux source and archives needed to rebuild the patched kernel |
| A matching build under `.artifacts/` (optional) | Saves a kernel rebuild; recheck its identity on the destination |

Copy these alongside a checkout of the same revision, preserving symlinks.
Keep the checked-in `dependencies/*.lock.json` files. Do not copy `.cache`:
its generated links contain absolute paths, and `scripts/in-bundle` recreates
it. Model builds in `.lake` and test reports are disposable too.

The staging scripts reuse hash-checked cached downloads. With the appropriate
snapshot archive in `.deps/downloads`, `scripts/restore-toolchains.py --only
lean` restores a missing Lean installation without a download. It leaves an
existing installation untouched.

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
