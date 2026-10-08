# New-machine setup guide (2026-10-08) [AGENT]

This guide takes a fresh machine to a verified copy of the project:
- the approved D3 oracle kernel, identity `8744fcc4…`;
- the unit tests;
- a full check at 1611/1611.

It was written from the scripts and the state of the old machine on 2026-10-08. Nothing in it was
executed for this guide: no builds, no VM runs, no downloads. Steps that could not be confirmed by
reading are marked **unverified**.

Where the older docs disagree with the scripts, this guide follows the scripts. Section 12 lists
the stale docs.

Read [the pause state](2026-10-08-pause-state.md) first. It says what is on `main`, what is on
branches, and the order in which to resume work.

Conventions:
- `$REPO` is the absolute path of the main checkout on the new machine.
- `$REPO/.worktrees/<id>` is a task worktree.
- Every project command runs through `scripts/in-bundle`. It puts the staged tools on `PATH`,
  sends caches to `.cache`, and sets `LEANUX_*` (`scripts/in-bundle`).
- Provenance: an [AGENT] mark is a recommendation of the agent that wrote this guide. A [USER]
  mark is a decision the user has already recorded.

## 1. Host requirements

### 1.1 Operating system

The recommended OS is **Ubuntu 24.04 LTS, x86-64**. The old host ran Ubuntu 24.04.4 with
glibc 2.39 and Python 3.12.3.

The reasons:
- The staged sysroot is 222 Ubuntu 24.04 amd64 packages (`dependencies/packages.lock.json`).
- `scripts/in-bundle` keeps the host's loader and glibc, and links every other library from the
  sysroot. The host glibc must therefore be 2.39 or newer (README.md, docs/offline-usage.md).
- The QEMU guest is x86-64 under TCG. KVM is not used.

### 1.2 What you install system-wide

The project rule forbids machine-global changes unless the user approves them (`~/.claude/CLAUDE.md`).
The agent installs none of the following. **You install them.**

| Prerequisite | Needed by | Note |
|---|---|---|
| `/usr/bin/python3`, version **3.12 or newer** | `scripts/in-bundle` (its shebang is `#!/usr/bin/python3`); `stage-resources.py`, `restore-toolchains.py`, `verify-dependencies.py` | The docs say "Python 3.9+". That is **stale**. The scripts use `hashlib.file_digest` (3.11+) and `tarfile.extractall(filter="data")` (3.12, or a 3.11.4+ backport). Ubuntu 24.04 ships 3.12. |
| `/bin/sh` | `scripts/build-kernel`, `bundle-tool`, `check-nono`, `lean-lsp` | |
| `git` | `in-bundle` (`git rev-parse` in worktrees), the mutant scripts, the workflow | |
| `curl` | `stage-resources.py`, `restore-toolchains.py` | |
| `tar` with zstd support, and `zstd` | `restore-toolchains.py` (`tar --zstd`) | |
| `dpkg-deb` | `stage-resources.py packages` (`dpkg-deb --extract`) | Missing from REPRODUCING.md's host list. It is part of base Ubuntu (`dpkg`). |
| `sha256sum`, `coreutils` | manual verification below | |
| SSH key with access to `git@github.com:OathTech/lean-ux-proto.git` | clone | User-level |
| Network access to `snapshot.ubuntu.com`, `www.kernel.org` and `github.com` | one-time staging | Not needed after staging |
| `nono` (optional) | confinement for agent sessions; `scripts/check-nono` | The old host had nono 0.79.0 at `~/.cargo/bin/nono`. How it was installed is **unverified**. |
| Claude Code and its MCP registration (optional) | agent work; see section 10 | User-level |

The following are **not** needed on the host, because they come from the project-local bundle:
- a compiler, make, flex, bison, binutils or LLVM;
- QEMU, BusyBox, Lean or elan, Go;
- any development packages, root access or global configuration.

The project's Lean does not use elan. `in-bundle` puts `$REPO/.tools/lean/bin` on `PATH` and
points `ELAN_HOME` at `.cache/elan`.

Set the git identity per repository (`git -C $REPO config user.name …`), not with `--global`.

### 1.3 CPU, memory and disk [AGENT recommendation]

These are estimates. They were not measured on a clean machine.

**CPU.** x86-64 is required.
- Use **8 or more dedicated cores**. 16 is comfortable.
- Each QEMU guest is single-threaded TCG (`-accel tcg,thread=single -smp 1`, `harness/linux.py`).
  Up to `LEANUX_QEMU_SLOTS` guests run at once. The default is 3, and it was set by [USER 2026-10-05].
- The kernel build uses `-j${LEANUX_JOBS:-4}` (`scripts/build-kernel`).
- The Lean build is single-threaded (`moreLeanArgs = ["-j1"]` in `lakefile.toml`, and
  `LEAN_NUM_THREADS=1` in `evaluator/check.py`).
- Timing matters. Each WireGuard trace must finish within 4.5 s of guest time (section 11.1).
  On the old host, with load 50-80 on 32 cores, the worst trace came within 1.6 % of that bound.
  An uncontended machine is worth more than many cores.

**Memory.** Use 16 GB at minimum and 32 GB to be comfortable.
- Each guest has 256 MiB (`-m 256`) plus QEMU's own overhead.
- The kernel build at `-j4` and the Lean build add a few GB. This is **unverified**.
- The old host had 125 GB.

**Disk.** Use **at least 200 GB free** for the project, on a local filesystem. Sizes measured on
the old host:

| Item | Size |
|---|---|
| `.tools`: Lean 2.9G, sysroot 1.0G, Go 0.27G, lean-lsp 0.05G | 4.2 GB |
| `.deps`: Linux source 1.6G, downloads 1.2G, go-mod 1.4G, syzkaller 0.44G, docs 0.12G | 4.8 GB |
| One kernel build directory (`.artifacts/kernel-net-choice*`) | 0.9 GB |
| One extracted, patched kernel source (`.artifacts/src/linux-6.12.110-*`) | 1.6 GB |
| `.artifacts/runs/evidence` (main checkout) | 0.23 GB |
| A worktree after several full checks and its own kernel (`.worktrees/d3-int`): `.artifacts/check` 3.3G, `.artifacts/src` 1.6G, kernel 0.9G, `.lake` 0.23G | 6 GB |
| All 31 worktrees on the old host | 73 GB |

The minimal path in sections 4-6 needs about 12 GB:
- the sysroot and its `.deb` downloads;
- Lean and its release archive;
- the Linux source and archive;
- one patched source and one kernel build.

Each full check writes several hundred MB to `.artifacts/check/<timestamp>/` (**unverified**
per-run figure). The old disk once reached 99 % full (2026-10-06).

## 2. Clone and fetch

Sources: `git remote -v`, `docs/2026-10-08-pause-state.md` section 5.

```sh
git clone git@github.com:OathTech/lean-ux-proto.git $REPO
```

**A clone from GitHub is not enough today.** On 2026-10-08 the remote was behind:
- `origin/main` is `6581932` (P, pipes stage 1).
- Local `main` on the old machine is `84a56fd` (D3, user-approved 2026-10-07).
- **No `task/*` branch is on the remote.** That includes `task/pause`, which holds this guide and
  the pause-state note.

The pause-state note (section 5) gives two ways to bring the work across:
- a **push** to `origin`. This needs the user's explicit approval at the moment of the push.
- a **git bundle**, which the user copies across. No remote is involved.

If you use a bundle, these are the commands. They are an [AGENT] suggestion, **unverified**, and
were not run.

```sh
# On the old machine (read-only for the repository; writes one file outside it):
git -C /home/dev/projects/lean-ux-proto bundle create /tmp/lean-ux-proto.bundle --branches
git bundle verify /tmp/lean-ux-proto.bundle

# On the new machine, after cloning from GitHub:
git -C $REPO fetch /path/to/lean-ux-proto.bundle \
    'refs/heads/task/*:refs/heads/task/*' 'refs/heads/main:refs/remotes/bundle/main'
git -C $REPO rev-parse bundle/main          # must print 84a56fd9c82ee1dca6ca9314e46a5b06357ad98f
git -C $REPO merge --ff-only bundle/main    # on main: restores the already-approved D3 main
```

The fast-forward restores the `main` the user approved on 2026-10-07. It integrates nothing new.
If the hash differs, stop and ask.

Untracked state is not in any bundle:
- `.artifacts/runs/evidence/`, about 233 MB in the main checkout;
- `.worktrees/*/.artifacts/runs/evidence/`.

Copy these by hand if the integration records are to be kept (pause-state section 5). Do not copy
`.cache`, because its links hold absolute paths (docs/offline-usage.md).

## 3. Lean toolchain and the model build

Sources: `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `scripts/restore-toolchains.py`,
`dependencies/toolchains.lock.json`, `evaluator/check.py`.

- `lean-toolchain` is `leanprover/lean4:v4.33.1`.
- `lake-manifest.json` has no packages: no Mathlib, no dependencies.
- The project's Lean is **`.tools/lean`**, from the official release. elan is not used.

```sh
cd $REPO
python3 scripts/restore-toolchains.py --only lean
```

What this does:
- With no snapshot present, it downloads
  `https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst` to
  `.deps/downloads/`.
- It checks `upstream_sha256` `890afd18…af235`.
- It extracts the release to `.tools/lean`. The release is identical, file by file, to the old
  machine's snapshot (lock note, checked 2026-09-30).
- An existing `.tools/lean` is left untouched.

`in-bundle` refuses to start without the sysroot. Do section 4 first, then:

```sh
scripts/in-bundle lean --version    # Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2…, Release)
scripts/in-bundle lake --version    # Lake version 5.0.0-src+819816b (Lean version 4.33.1)
```

### Building the model

Build in a **worktree**, not the main checkout (AGENTS.md; section 9):

```sh
cd $REPO/.worktrees/<id>
scripts/in-bundle lake build                # default target: the Leanux library
scripts/in-bundle lake build leanux-model   # the executable .lake/build/bin/leanux-model
```

`lakefile.toml` has `defaultTargets = ["Leanux"]`, so a **plain `lake build` does not relink the
`leanux-model` binary**.
- `evaluator.check` runs `lake build leanux-model` itself, unless you pass `--no-build`. With
  `--no-build` it runs `lake build leanux-model --no-build`, which fails if the binary is out of
  date.
- `evaluator.test_model_replay` runs whatever binary is at `.lake/build/bin/leanux-model`. A missing
  binary fails the tests. A **stale** binary is not detected.
- `harness.test_d1_keys` runs `lake env lean` and needs the library build (`lake build`).

Run both commands before the unit tests.

## 4. Project-local tools (`.tools`)

Sources: `scripts/stage-resources.py`, `scripts/restore-toolchains.py`, `scripts/cache-toolchains.py`,
`dependencies/packages.lock.json`, `dependencies/toolchains.lock.json`, docs/offline-usage.md.

| Directory | Contents | Produced by | Network source |
|---|---|---|---|
| `.tools/sysroot` | 222 Ubuntu 24.04 packages: GCC/G++ 13.3, binutils, LLVM/Clang/LLD 19, Python 3.12, make/flex/bison/perl, **QEMU 8.2.2** (+ SeaBIOS, iPXE), BusyBox, git, ripgrep, strace | `python3 scripts/stage-resources.py packages`: each `.deb` is downloaded, checked against the lock, and extracted with `dpkg-deb --extract`. There are no maintainer scripts and no dpkg database. A usrmerge layout and compiler aliases are completed inside the sysroot. | `https://snapshot.ubuntu.com/ubuntu/20260920T000000Z/` (the lock's `archive.ubuntu.com` URLs are rewritten to the dated snapshot) |
| `.tools/lean` | Lean 4.33.1 | `python3 scripts/restore-toolchains.py --only lean` | GitHub release (section 3) |
| `.tools/go` | Go 1.26.5 (syzkaller only) | `restore-toolchains.py`, **from the snapshot only** | none: the lock row has no `upstream_url` |
| `.tools/lean-lsp` | Lean LSP MCP 0.29.0 and 41 Python distributions | `restore-toolchains.py`, **from the snapshot only** | none |

Stage the minimum the check needs. Run it from the main checkout, which is where shared inputs
live (docs/worktree-practices.md):

```sh
cd $REPO
python3 scripts/stage-resources.py packages     # .deps/downloads/debs (233 MB), then .tools/sysroot
python3 scripts/restore-toolchains.py --only lean
```

`stage-resources.py packages` is safe to rerun:
- downloads already present are hash-checked;
- the marker `.tools/sysroot/.leanux-packages-sha256` must equal the sha256 of
  `packages.lock.json` (`dd9d4d59…ed98b`);
- it refuses to overwrite a sysroot that is partial or unrecognized.

### Go and lean-lsp

`.tools/go` and `.tools/lean-lsp` have **no fetch path** on a fresh machine.
- `cache-toolchains.py` snapshotted them from the old host's `/usr/local/go` and
  `~/.local/share/uv/tools/lean-lsp-mcp`.
- `restore-toolchains.py` restores them only from the snapshot archives in `.deps/downloads/`.

If you want them, copy two files from the old machine into `$REPO/.deps/downloads/`:
- `go-1.26.5-local-snapshot.tar.zst`, 64 MB, sha256 `7fefdddf…244e`;
- `lean-lsp-0.29.0-local-snapshot.tar.zst`, 13 MB, sha256 `06aeac88…d65ad8`.

Then run:

```sh
python3 scripts/restore-toolchains.py --only go,lean-lsp
```

`restore-toolchains.py` checks each snapshot's sha256 against the lock. Go is needed only for
syzkaller, and lean-lsp only for the MCP (section 10). Neither is needed for the check.
`dependencies/lean-lsp-requirements.txt` pins the 41 MCP distributions, but no script installs
from it.

### Verification

```sh
scripts/in-bundle python3 scripts/probe-toolchains.py     # compiler/Lean/QEMU probes (README.md)
scripts/in-bundle qemu-system-x86_64 --version           # QEMU emulator version 8.2.2 (Debian 1:8.2.2+ds-0ubuntu1.18)
scripts/in-bundle gcc --version                          # gcc-13 (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0
scripts/in-bundle python3 --version                      # Python 3.12.3
```

`scripts/verify-dependencies.py` and `scripts/check-offline.py` are **all-or-nothing**.

`verify-dependencies.py` checks every row of every lock:
- all 222 `.deb` files;
- the Linux, Firecracker and syzkaller archives;
- the **three toolchain snapshots** `*-local-snapshot.tar.zst`;
- `documentation.lock.json` and `lean-manual.lock.json`;
- the source samples in `docs/resource-proposal.json`.

After the minimal staging above it **will fail** with a missing-file error:
- Lean was restored from the release archive, not the snapshot;
- syzkaller, Firecracker and the docs are not staged.

That failure says nothing about the files that are present. To make it pass, you also need:
- `python3 scripts/stage-resources.py sources`, all three sources. The two GitHub archives are not
  guaranteed byte-stable (REPRODUCING.md).
- The three snapshot archives, copied from the old machine.
- `.deps/docs`, copied. `stage-resources.py docs` re-downloads it, **and rewrites
  `dependencies/documentation.lock.json`**, a tracked file. The Lean manual comes from
  `scripts/mirror-lean-manual.py` (**unverified**).

The command:

```sh
scripts/in-bundle python3 scripts/verify-dependencies.py    # PASS: N staged archives ... verified.
```

`check-offline.py` runs seven checks in order and stops at the first failure:
toolchains, kernel, guest, syzkaller, syzkaller-program, lean-lsp, integrity.
- Launch it through `scripts/check-nono`, which needs nono, or directly with
  `scripts/in-bundle python3 scripts/check-offline.py --only <check>`.
- Its `kernel` check runs `scripts/build-kernel` with the **base** profile into `.artifacts/kernel`,
  unless `--kernel-build` is given. That build copies its config over `kernel/config-x86_64`.
- The `syzkaller` check needs `.deps/go-mod` and refuses to run outside the main checkout.
- `.deps/go-mod` has **no script that produces it**. It is only checked. Copy it from the old
  machine if you want the syzkaller checks.

[AGENT] For the check, the useful subsets are:

```sh
scripts/in-bundle python3 scripts/check-offline.py --only toolchains
scripts/in-bundle python3 scripts/check-offline.py --only lean-lsp     # only after lean-lsp is restored
```

## 5. Kernel source (`.deps/linux` and the locked archive)

Sources: `scripts/stage-resources.py` (`sources`), `dependencies/sources.lock.json`,
REPRODUCING.md section 1.

```sh
cd $REPO
python3 scripts/stage-resources.py sources --sources linux
```

The command does three things:
- It downloads `https://www.kernel.org/pub/linux/kernel/v6.x/linux-6.12.110.tar.xz` to
  `.deps/downloads/linux-6.12.110.tar.xz`, and checks sha256
  `8cee19e1839bb6ff4d5254d761933ae6ab670492d5ed030e09a80538320d5c4c`. The lock records commit
  `fa5b0686…`.
- It extracts the archive to `.deps/linux`, writing the marker `.deps/linux/.leanux-archive-sha256`.
- It checks the Linux source samples listed in `docs/resource-proposal.json`.

How the pieces are used:
- `scripts/build-kernel` extracts the **archive** again for every patched profile, and re-checks
  its hash against the lock.
- `.deps/linux` is the pristine reference. It is read by:
  - `evaluator/check.py` (`SOURCE`);
  - `kernel/patches/gen-choice-stream.py`;
  - debug-info paths, because the build maps the patched tree onto `.deps/linux` with
    `-fdebug-prefix-map`.
- `.deps` is never modified.

Check by hand:

```sh
sha256sum .deps/downloads/linux-6.12.110.tar.xz
cat .deps/linux/.leanux-archive-sha256
```

Both must print `8cee19e1…5c4c`.

## 6. The oracle kernel

Sources: `scripts/build-kernel`, `scripts/apply-kernel-patch.py`, `scripts/kernel-identity.py`,
`kernel/identity-x86_64-net-choice.txt`, `harness/linux.py`,
`.artifacts/runs/evidence/d3/integration.json` (old machine).

### 6.1 What is approved on `main`

The D3 oracle was approved by [USER 2026-10-07], "yes approved on both":
- **profile `net-choice`**: `kernel/config-x86_64-net` unchanged, plus
  `kernel/patches/choice-stream.patch` applied **alone** to the locked source;
- **patch sha256** `3b0f2026265c7ccfe3bd8951ab7afd3ccdf5b56d6ffea70f5c715a57f7f217ab`, hard-coded as
  `CHOICE_SHA` in `scripts/build-kernel`;
- **path-independent identity** `8744fcc402b0efd49200e317c02f0e4a352441bbe38c2b11c79533b041ad399e`, the
  first hash in `kernel/identity-x86_64-net-choice.txt`;
- **boot parameters** (`harness/linux.py` `BOOT_PARAMETERS`):
  `console=ttyS0 panic=1 nokaslr loglevel=3 clocksource=refined-jiffies`.

`clocksource=refined-jiffies` is part of the oracle. D3's virtual time advance
(`KCOV_LEANUX_TIME_ADVANCE`) is refused unless the timekeeper is refined-jiffies. Every batch checks
the clocksource at its start and end (`EXPECTED_CLOCKSOURCE`). The harness passes the parameter
itself. Do not change it.

The vmlinux sha256 `883e1f60…6c51` in the identity file depends on the build path. It **will
differ** on the new machine, and that is expected. Only the identity counts.

### 6.2 Profiles that exist on `main`

`scripts/build-kernel` accepts `base`, `net`, `net-rcov`, `net-hidden`, `net-probe` and
`net-choice`.
- Only **`net-choice`** is the current oracle.
- The others belong to earlier stages. `net-probe` is a throwaway measurement kernel.

**`net-choice-actl` (the A allocation-steering control kernel) is not on `main`.**
- It exists on `task/a-k` and `task/int-da`, where `scripts/build-kernel` and the patches differ.
- `task/int-da`'s `net-choice` is a different kernel: patch `4274afa3…`, identity `c79e3e0c…`. Its
  control kernel is identity `044b46e5…`.
- Both need new signoff (pause-state section 2, resume step 3).
- Build them only from that branch's worktree, into a separate directory, never over the D3 oracle.

### 6.3 Build

`build-kernel` requires the build directory to be **inside `$LEANUX_ARTIFACTS`**. `harness/linux.py`
refuses a `LEANUX_KERNEL_DIR` outside `<main checkout>/.artifacts` or the worktree's own `.artifacts`.

The harness's default kernel is `<main checkout>/.artifacts/kernel-net-choice` (`harness/linux.py`
`KERNEL`). Every worktree reads it as a shared input (docs/worktree-practices.md).

[AGENT recommendation] Build the D3 oracle once, at that default path, from the main checkout, as
a shared-input step:

```sh
cd $REPO
LEANUX_KERNEL_PROFILE=net-choice LEANUX_KERNEL_BUILD=.artifacts/kernel-net-choice \
    scripts/in-bundle scripts/build-kernel
```

This is the form in REPRODUCING.md section 2. `LEANUX_JOBS` sets the make parallelism; the default
is 4. The steps:
1. It verifies the archive against `sources.lock.json`.
2. It extracts the archive to `.artifacts/src/linux-6.12.110-choice-stream-d3`. REPRODUCING.md
   says `-d1`, which is **stale**.
3. It applies the patch with `scripts/apply-kernel-patch.py`, strictly and by hash: no fuzz, and
   line numbers are preserved in anchored files.
4. It records the patch hash in `.leanux-patch-sha256`. An existing source tree with a different
   hash is refused.
5. It configures, with fixed `KBUILD_BUILD_*` and timestamp, and builds `bzImage` and `vmlinux`.

**Caveats:**
- **It copies the build's `.config` over the tracked `kernel/config-x86_64-net-choice`.** For the
  D3 build the two are byte-identical; this was checked on the old machine. Afterwards
  `git -C $REPO status --porcelain` must be empty. If it is not, the build differs from the oracle:
  stop, do not commit, and ask.
- AGENTS.md permits the main checkout only for "read-only inspection, shared inputs, worktree
  administration". Treat this build as a one-time shared-input step, and confirm it with the user if
  in doubt.
- The alternative used on the old machine kept D3 kernels inside worktrees, for example
  `.worktrees/d3-int/.artifacts/kernel-net-choice-d3`, and always set `LEANUX_KERNEL_DIR`. That works
  too, but the kernel disappears with the worktree.

### 6.4 Verify the identity

```sh
cd $REPO
scripts/in-bundle python3 scripts/kernel-identity.py .artifacts/kernel-net-choice
grep -v '^#' kernel/identity-x86_64-net-choice.txt | head -1
```

The first command prints `<identity>  (N build-ID notes zeroed)`. The identity must equal
`8744fcc402b0efd49200e317c02f0e4a352441bbe38c2b11c79533b041ad399e`.

The identity hashes three things, with GNU build-ID notes zeroed:
- `.config`;
- `System.map`;
- every loaded section of `vmlinux`.

So it is independent of the build path. It was confirmed equal across build directories on the
old host. **That it reproduces on a different host from the same locked toolchain is expected but
unverified.**

If it differs, stop: "the check's decision table was verified against the accepted build"
(REPRODUCING.md). Nothing in `evaluator.check` verifies the identity automatically. The report
records only the path-dependent `vmlinux_sha256`. Checking the identity is a manual step.

Optional: confirm that the patch is reproducible from the locked source (the generator script is in
`kernel/patches/`). It writes `.artifacts/choice-patch/` and overwrites the tracked patch, so run it
**in a worktree**:

```sh
cd $REPO/.worktrees/<id>
scripts/in-bundle python3 kernel/patches/gen-choice-stream.py   # prints ok
sha256sum kernel/patches/choice-stream.patch                    # 3b0f2026…f217ab
git diff --exit-code kernel/patches/choice-stream.patch
```

Whether it regenerates byte-identically is **unverified**.

## 7. Guest and provisioning (`.artifacts/guest`, `.artifacts/provisioning`)

Neither directory is an input to the check.

- **The check's guest** is built for every chunk, from `harness/guest.c`, by `harness/linux.py`:
  - it compiles with `gcc -static -O2 -Wall -Wextra -Werror -std=c11`;
  - it builds an initramfs with the kernel build's `usr/gen_init_cpio` and the sysroot's BusyBox;
  - it boots `qemu-system-x86_64 -accel tcg,thread=single -machine pc-i440fx-8.2 -cpu qemu64 -smp 1
    -m 256 -display none -monitor none -serial stdio -nic none -no-reboot -kernel … -initrd …
    -append "<BOOT_PARAMETERS>"`.

  Each chunk's directory holds `provenance.json` and `qemu-command.json`. Nothing needs staging.
- **`.artifacts/guest`** is the output of the dependency smoke test `scripts/check-guest.py`. It
  holds the `kcov-smoke` probe, the initramfs and `boot.log`. It boots with only
  `console=ttyS0 panic=1`. Its default kernel is `.artifacts/kernel`, the **base** profile, which
  the oracle procedure does not build. To smoke-test with the oracle build:

  ```sh
  cd $REPO
  LEANUX_KERNEL_BUILD=$REPO/.artifacts/kernel-net-choice scripts/in-bundle python3 scripts/check-guest.py
  ```

  Expected: `PASS: TCG guest, FD aliasing, KCOV, and source symbolization; network disabled.`
  Whether this probe passes on the net-choice kernel is **unverified**: on the old host it ran
  against the base kernel.
- **`.artifacts/provisioning`** holds logs of the original 2026-09-20 provisioning run, plus
  `lean-lsp-check.json`, which `scripts/check-lean-lsp.py` writes. Nothing reads it. It need not be
  recreated.
- `dependencies/validation.json` records that 2026-09-20 run. It is historical. Its "bootstrap
  requirements" (bwrap, user namespaces) were retired with the Bubblewrap launcher
  (docs/offline-usage.md).

## 8. Smoke tests

Run all of these **in a worktree** on `main`'s commit, after sections 3-6. For example:

```sh
cd $REPO && git worktree add .worktrees/setup -b task/setup main && cd .worktrees/setup
export LEANUX_KERNEL_DIR=$REPO/.artifacts/kernel-net-choice    # explicit; see 11.6
```

`in-bundle` passes `LEANUX_KERNEL_DIR` through to the commands it runs.

### 8.1 Unit tests (no guest)

```sh
scripts/in-bundle lake build && scripts/in-bundle lake build leanux-model
scripts/in-bundle python3 -B -m unittest \
    evaluator.test_evaluation evaluator.test_model_replay \
    harness.test_trace harness.test_wg harness.test_noise harness.test_linux \
    harness.test_d1_keepalive harness.test_d1_keys
```

Expected: **99 tests, OK** (`.artifacts/runs/evidence/d3/integration.json`: "unit_tests": "99/99").
The module list is the 8 modules of `docs/2026-10-05-d3-timers.md` section 17.3. Their `def test`
counts on `main` sum to 99: 35 + 10 + 13 + 4 + 26 + 4 + 2 + 5.

The commands in README.md and REPRODUCING.md list fewer modules. They are **stale**.

### 8.2 Quick check

```sh
scripts/in-bundle python3 -m evaluator.check --suite handwritten,pipes
```

Expected: `pass`, 64/64. This is the D3 "quick suites" run, recorded at `f17fa7c`, before the
final pre-signoff commits; it is **unverified** that it gives exactly 64 at `84a56fd`.

The check writes `report.json` to `.artifacts/check/<timestamp>/` (or `--out DIR`, which must be a
new directory inside the worktree's `.artifacts`). It exits nonzero unless everything passes.

Other selectors (`evaluator/check.py`):
- `--suite` takes a comma-separated subset of `handwritten`, `critic`, `wireguard`, `generated`,
  `wireguard-generated`, `pipes`, `pipes-generated`, plus the control suites `steering-controls`
  and `timer-controls`;
- `--trace ID` replays one trace;
- `--no-build` reuses an up-to-date model.

### 8.3 Full check

```sh
scripts/in-bundle python3 -m evaluator.check
```

Expected on `main` (`84a56fd`), from the `merge-full2` run on the old machine: `status` `pass`,
`traces` **1611**, `counts` `{"agreement": 1611}` across all **7 suites** (1388 + 223 pipes),
`operations` 44967, `operand_pairs_matched` 424476. The seed defaults to `20260920`, and the counts
are `--generated-count 1000`, `--wireguard-count 200`, `--pipes-count 200`.

On the old contended host it took **about 45 minutes**, model build included. README.md says
"~1.5 hours".

Chunks of 100 traces run one after another within a check. `LEANUX_QEMU_SLOTS` limits concurrent
guests **across all checks** in all worktrees.

Afterwards, check the timing margin (section 11.1).

REPRODUCING.md's table (1288 traces, 38652 operations, 324964 operand pairs) is from stage A and is
**stale**.

### 8.4 Controls

```sh
scripts/in-bundle python3 scripts/steering-controls.py   # expected 3/3 rejected
scripts/in-bundle python3 scripts/wg-d3-controls.py      # expected tc_advance_wait0 rejected
```

Both need `LEANUX_KERNEL_DIR` exported, per the `wg-d3-controls.py` docstring.

### 8.5 Mutants: scope them

```sh
scripts/in-bundle python3 scripts/wg-mutants.py [NAME ...]      # WireGuard: 70 entries
scripts/in-bundle python3 scripts/pipes-mutants.py [NAME ...]   # pipes: 18 + baseline
```

How the scripts work:
- Each mutant is written **into the working tree**, then a check runs: `--suite wireguard` for
  WireGuard, `pipes` for pipes. The file is then restored with `git checkout -- <file>`.
- The tree must be clean, which the script asserts. Run mutants only in a dedicated worktree, and
  never in the main checkout.
- `wg-mutants.py` writes `.artifacts/check/mutant-<NAME>/` and `.artifacts/check/mutants-summary.json`.
- It exits 1 on any `no_verdict`: an infrastructure failure is never counted as a rejection.

**A full WireGuard set takes 18 hours or more.** On the old contended host:
- one mutant took about 16 minutes;
- all 70 took 18.5 hours (`docs/2026-10-05-d3-timers.md` section 16.4).

[USER] decision: mutant runs are scoped to the touched files, on reduced corpora. The full set
runs once, at milestones (pause-state section 3). Always pass names. For example, the D3 set
(8/8 rejected on `main`):

```sh
scripts/in-bundle python3 scripts/wg-mutants.py D3-M1-attempts-not-incremented D3-M2-need-another-ignored \
    D3-M3-firing-keeps-timer D3-M4-clear-keeps-handshake D3-M5-send-fresh-at-reject \
    D3-M6-no-lastminute-flag D3-M7-send-ignores-reject-after-time D3-M8-new-handshake-delay
```

Expected on `main`:
- WireGuard: 68 rejected, 1 survivor (`B2-M3-length-before-type`, an instrument limit), and
  1 equivalent (`H-M8-response-unclamped`, listed and not run). 0 without a verdict.
- Pipes: baseline pass 23/23, **18/18 rejected**.

REPRODUCING.md's "about 20 minutes" for `wg-mutants.py` is **stale**.

Run long jobs as tracked background tasks (section 11.5).

## 9. Worktree workflow and evidence

Sources: AGENTS.md, docs/worktree-practices.md, `scripts/in-bundle`.

```sh
cd $REPO
git worktree add .worktrees/<id> -b task/<id> main
cd .worktrees/<id>
scripts/in-bundle python3 -m evaluator.check     # or any other bundled command
```

How `in-bundle` treats a worktree:
- It finds the main checkout through `git rev-parse --git-common-dir`. It fails unless the main
  checkout has `.tools`.
- **Shared, read-only:** `.tools`, `.deps`, the oracle kernel and `.artifacts/runs/` in the main
  checkout. That includes the QEMU slot locks `qemu.lock`, `qemu.lock.1` and `qemu.lock.2`.
- **Private to the worktree, Git-ignored:** `.cache`, `.artifacts` and `.lake`.

The rules:
- All development happens in worktrees on `task/*` branches.
- `main` moves only with the user's explicit signoff on the concrete diff. This covers
  fast-forward, cherry-pick, reset and push alike.
- Record the approval in `integration.json`, next to the evidence.

**Evidence.**
- Copy a report worth keeping (one presented for signoff, or a reproduced failure) to
  `$REPO/.artifacts/runs/evidence/<id>/` before you remove the worktree.
- It is untracked. Back it up by hand.

**Remove a worktree:**

```sh
git -C .worktrees/<id> status --porcelain     # must be empty
git worktree remove .worktrees/<id>
git branch -d task/<id>
```

Never use `git clean -fdx`, and never delete recursively over `.worktrees/`.

## 10. Agent environment

### 10.1 Lean LSP MCP

Sources: `scripts/lean-lsp`, `scripts/lean-lsp-python`, `scripts/check-lean-lsp.py`.

The project-local MCP server:

```sh
scripts/lean-lsp /absolute/path/to/a/Lean/project/inside/this/repository
```

- It needs `.tools/lean-lsp` (section 4, from the snapshot only).
- It runs through `in-bundle`, with the staged Python 3.12 and site-packages.
- It disables the remote search tools: `lean_leansearch`, `lean_loogle`, `lean_leanfinder`,
  `lean_state_search` and `lean_hammer_premise`.
- It refuses a project path outside the repository.

To check it:

```sh
scripts/in-bundle scripts/lean-lsp-python scripts/check-lean-lsp.py
# PASS: offline Lean MCP diagnostics accept valid code and detect a type error.
```

On the old machine, Claude Code did **not** use this server. It used a user-global registration in
`~/.claude.json`, `"lean-lsp": {"type": "stdio", "command": "lean-lsp-mcp"}`, with
`~/.local/bin/lean-lsp-mcp` and `~/.elan`. Those are user-level installs.

On the new machine, either:
- recreate them yourself, as a user-level change; or
- register `scripts/lean-lsp` for this project only. A checked-in `.mcp.json` would be a tracked
  change, which needs its own branch and signoff. `claude mcp add --scope local` writes to
  `~/.claude.json`.

[AGENT] Neither option has been tested.

### 10.2 nono

Sources: `scripts/check-nono`, `scripts/nono-check-profile.json`, docs/nono-profile-proposal.md.

- Agent sessions on the old host ran under nono. Its profiles were
  `~/.config/nono/profiles/claude-local.json` and `codex-local.json`. These are user files, and are
  **not in the repository**: copy or recreate them yourself.
- `scripts/in-bundle` provides no confinement of its own.
- `scripts/check-nono` runs `check-offline.py` under `nono wrap` with the repository's profile
  fixture. That fixture extends `default`, grants the workdir read-write, reads `/usr`, `/proc`,
  `/etc/localtime` and `/etc/python3.12`, and **blocks the network**. It is passed by filename and
  never installed.
- Inherits the all-or-nothing caveats of section 4. Use `--only`:

  ```sh
  scripts/check-nono --only toolchains
  scripts/check-nono --only lean-lsp
  ```

### 10.3 Agent memory

The agent's project memory lives in
`~/.claude/projects/-home-dev-projects-lean-ux-proto/memory/`.
- The directory name is derived from the checkout's absolute path.
- If `$REPO` is not `/home/dev/projects/lean-ux-proto`, a copied memory directory must be renamed
  to match.
- The [USER] decisions in it are also recorded in the pause-state note (section 3).
- `~/.claude/CLAUDE.md` holds the global rules. Copy it as well.

## 11. Known pitfalls

### 11.1 The 4.5 s trace bound on a contended host

Each WireGuard trace must finish within **4.5 s of guest time**, measured from just before `wg_up`,
net of virtual advances:
- `REKEY_BOUND_NS` in `harness/guest.c`;
- `JIFFIES_BOUND = 1125` at HZ 250 in `evaluator/check.py`.

A trace over the bound fails `environment_failure trace_exceeds_rekey_bound`, and that fails its
whole chunk.

On the old host, at load 50-80, the give-up class came within **1.6 %** of the bound:
`generated-wg-20260920-00194` at 4.43 s, and `d3_retransmit_gives_up` at 4.38 s
(`docs/2026-10-05-d3-timers.md` section 17.5).

The bound is fixed by design (`docs/2026-10-06-contended-host.md` section 4). Do not raise it to
make a run pass. After the first full check, re-measure the margin (pause-state, resume step 1):

```sh
python3 -c "import json,glob,sys; r=[json.loads(l) for f in glob.glob(sys.argv[1]+'/chunk-*/linux/timing.jsonl') for l in open(f)]; m=max(r,key=lambda x:x['since_up_ns']); print(m['id'],m['mode'],m['since_up_ns']/1e9,'s of 4.5')" .artifacts/check/<timestamp>
```

The layout `chunk-*/linux/timing.jsonl` is read from `evaluator/check.py` and `harness/linux.py`,
and `since_up_ns` is net of advances. **This one-liner is unverified.**

### 11.2 `LEANUX_QEMU_SLOTS`

The default is **3** ([USER 2026-10-05]; `harness/linux.py`).
- The locks are `$REPO/.artifacts/runs/qemu.lock{,.1,.2}`, shared by every worktree.
- A run waits up to 3600 s for a free slot, then fails `resource_busy`. That outcome is retried
  once, and the retry is recorded in `chunk_retries`.
- More slots add load and erode the 4.5 s margin.
- docs/worktree-practices.md still says "only one QEMU guest runs at a time". That is **stale**.

### 11.3 Disk

Each worktree's `.artifacts/check` grows with every check and mutant run: 3.3 GB in one worktree on
the old host. A worktree that builds its own kernel adds 2.5 GB (source plus build). The old disk
reached 99 % once.

Before you remove a worktree:
- copy the evidence you need;
- check free space before kernel builds and full mutant runs.

### 11.4 Stale model binaries

- A plain `lake build` does not relink `leanux-model` (section 3).
- `evaluator.test_model_replay` runs whatever binary is present.
- `evaluator.check --no-build` refuses an out-of-date binary.
- After switching branches or editing Lean, run `scripts/in-bundle lake build leanux-model` before
  the replay tests.
- Each worktree has its own `.lake`. A fresh worktree has no binary until it is built.

### 11.5 Long jobs as tracked background tasks

Full checks (about 45 minutes), mutant sets and kernel builds are long.
- Start them as **tracked background tasks**, so completion is reported.
- Do not detach them with `&` and poll with `pgrep -f <pattern>`. The poller's own command line
  matches the pattern, so it never exits. On 2026-09-30 this hung for about 1 h 40 m after the run
  had finished.
- Before you report progress, check actual completion.

### 11.6 Set `LEANUX_KERNEL_DIR` explicitly for mutant and control runs

`harness/linux.py` falls back to `<main checkout>/.artifacts/kernel-net-choice`. Whatever kernel sits
there is used, and the identity is never checked.

On the old machine that path held a **pre-D3** kernel. A mutant run started without
`LEANUX_KERNEL_DIR` ran on it, and the D3 traces failed with `environment_failure` (the advance
ioctl returned `ENOTTY`) next to spurious `hidden_mismatch`es (d3 evidence summary, S2).

For every mutant, control and evidence run:
1. Export `LEANUX_KERNEL_DIR` as an **absolute path**.
2. Make sure the path lies inside an artifact root.
3. Verify that kernel's identity first (section 6.4).

`wg-mutants.py` now scores such a run `no_verdict`. The kernel mismatch itself is still not
detected.

### 11.7 Further failure points on a fresh machine

- **The remote lacks the D3 `main` and every `task/*` branch** (section 2). A clone from GitHub
  alone gives the pre-D3 tree, and its full-check counts differ.
- **`verify-dependencies.py`, `check-offline.py` and `check-nono` fail** after the minimal staging
  (section 4). This is a missing file, not corruption.
- **Go, lean-lsp, `.deps/go-mod` and `.deps/docs`** have no fetch path. Copy them from the old
  machine, or do without them.
- **`build-kernel` writes tracked config files**: `kernel/config-x86_64*`, one per profile. Check
  `git status` after every kernel build.
- **`.cache` must not be copied** between machines: its links hold absolute paths. It is
  disposable.
- **Ubuntu snapshot availability.** The packages come from `snapshot.ubuntu.com` at
  `20260920T000000Z`. If that service is unreachable there is no other path, because 8 of the
  locked packages had already left `archive.ubuntu.com` by 2026-09-30 (`stage-resources.py`).
- **Kernel identity on new hardware.** It is expected to match (same locked toolchain, fixed build
  metadata), but this is **unverified across hosts** (section 6.4).

## 12. Stale statements in other documents

Where these disagree with the scripts, follow the scripts. None of these documents has been edited.

| Document | Statement | Actual (script or evidence) |
|---|---|---|
| README.md, REPRODUCING.md, docs/offline-usage.md | Python 3.9+ | 3.12 (`tarfile` `filter="data"`; `hashlib.file_digest` 3.11+) |
| REPRODUCING.md | Host tools list | Also needs `dpkg-deb` |
| REPRODUCING.md §2 | Source at `.artifacts/src/linux-6.12.110-choice-stream-d1` | `…-choice-stream-d3` (`scripts/build-kernel`) |
| REPRODUCING.md §3, README.md | Unit-test module lists | 8 modules, 99 tests (section 8.1) |
| REPRODUCING.md §3 | 1288 traces / 38652 ops / 324964 operand pairs | 1611 / 44967 / 424476 (D3 evidence) |
| REPRODUCING.md | `wg-mutants.py` about 20 minutes | about 16 min per mutant; 18.5 h for all 70 |
| README.md | Full check ~1.5 hours; kernel `.artifacts/kernel-net` | ~45 min on the old host; `.artifacts/kernel-net-choice` |
| harness/README.md | Oracle `.artifacts/kernel-net-rcov` | `.artifacts/kernel-net-choice` (`harness/linux.py`) |
| docs/worktree-practices.md | One QEMU guest at a time, `qemu.lock` | `LEANUX_QEMU_SLOTS` (default 3), `qemu.lock{,.1,.2}` |
| docs/offline-usage.md | `check-guest.py` uses `.artifacts/kernel` | That is the base profile, not the oracle; set `LEANUX_KERNEL_BUILD` (section 7) |
| dependencies/validation.json | Bootstrap needs bwrap and user namespaces | Retired; no Bubblewrap (docs/offline-usage.md) |
