# Nono setup for this project

The implemented setup runs the staged tools directly inside nono. It supersedes
the earlier proposals to change network enforcement or introduce a build worker.
No namespace or mount operations are required by the development launcher.

Your standalone agent profile is
`~/.config/nono/profiles/codex-local.json`, extending `nolabs-ai/codex`.
It already grants workdir writes and the runtime reads needed here. It also
permits selected API and Go-download domains; it is a filtered-network agent
profile, not a complete network block. No changes to this profile, its parent,
`claude-local.json`, or the global draft directory were made for this setup.

Continue using that profile through your usual nono launch with Codex's separate
built-in tool sandbox disabled. Run project commands through `scripts/in-bundle`.
The runner redirects caches and tool lookup into the project. It inherits the
session's OS restrictions and does not alter HOME or install global tools.

The check itself, run under the agent profile, is the validation of the
sandbox: it needs no global Lean, Go or Python package caches.

Compatibility was also checked using a project-local copy of `codex-local`,
retaining its filesystem rules, environment settings and pathname Unix-socket
mediation while replacing its network settings with a full block. Lean/C/C++
builds, the QEMU/KCOV guest and MCP diagnostics passed. Temporary supervisor
state used for that check was removed afterward, and the shared profile's hash
was unchanged.

The build checks and logs are described in [offline usage](offline-usage.md).
Outside nono, `scripts/in-bundle` remains only an environment runner and has
no security boundary of its own. Its permissions are always those of its caller.

The original failure had two separate possible sources: Codex's own tool sandbox
and standalone nono. Tests outside Codex's tool sandbox established that nono
filesystem confinement also prevents new mounts. That is why changing a
network permission would not have fixed the old Bubblewrap launcher. Direct
tool execution avoids those operations while retaining nono's enforcement.
