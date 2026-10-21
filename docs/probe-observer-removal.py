#!/usr/bin/env python3
"""One-off probe of the peer-read observation; no production source is edited.

Run after building Leanux.Proofs.WG.Peers.Access, from the repository root:
python3 docs/probe-observer-removal.py
Use the repository's optional bundle and capped wrapper on the shared box.
"""
from pathlib import Path
import subprocess
import tempfile


root = Path(__file__).resolve().parents[1]
source = (root / "Leanux/Proofs/WG/Peers/Access.lean").read_text()


def between(start, end):
    return source[source.index(start):source.index(end)]


header = """import Leanux.Proofs.WG.Peers.Frames
import Leanux.Proofs.WG.Lifetimes.Events
import Leanux.Proofs.Logged.WGPrefix
namespace RemovalProbe
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Lifetimes
"""
getter = between("abbrev PeerEvent :=", "/-- An absent device")
coverage = between("@[simp] theorem getPeerPrefix_run", "@[simp] theorem setPeerPrefix_run")
erasure = between("theorem getPeerPrefix_erases", "theorem setPeerPrefix_erases")
event = "h ++ [.read pid p.internalId]"
assert getter.count(event) == 1
mutant = getter.replace(event, "h")
survivors = """
theorem retained_history (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List PeerEvent) :
    (runStatePrefix (getPeerPrefix pid) w a h).2 = h := by
  simp only [runStatePrefix, runPrefix, getPeerPrefix, StateT.run, ExceptT.run, ExceptT.mk]
  cases (getPeer pid) w a <;> rfl
theorem safe_history (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List PeerEvent)
    (safe : AccessEvent.Safe h) :
    AccessEvent.Safe (runStatePrefix (getPeerPrefix pid) w a h).2 := by
  rw [retained_history]
  exact safe
#print axioms RemovalProbe.getPeerPrefix_erases
#print axioms RemovalProbe.safe_history
"""

(root / ".tmp").mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix="observer-removal-", dir=root / ".tmp") as temp:
    folder = Path(temp)
    for name, body, should_pass in [
        ("baseline", getter + coverage + erasure, True),
        ("one_event_removed", mutant + coverage + erasure, False),
        ("surviving_claims", mutant + erasure + survivors, True),
    ]:
        path = folder / f"{name}.lean"
        path.write_text(header + body + "\nend RemovalProbe\n")
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=root,
                                capture_output=True, text=True, timeout=120)
        output = result.stdout + result.stderr
        print(f"{name}: exit {result.returncode}\n{output}", flush=True)
        if should_pass:
            if result.returncode or "warning:" in output:
                raise SystemExit(f"FAIL: {name} did not pass cleanly")
        elif result.returncode != 1 or "rfl" not in output or "error:" not in output:
            raise SystemExit("FAIL: mutation did not produce the expected source-equation failure")
print("PASS: removing the read breaks coverage; erasure and safe retained history survive")
