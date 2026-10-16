import Leanux.Runner

/-! The stale raw slot's destructive callback in isolation. This fixture
is an isolated WG execution; the current runner rejects the historical
device-replacement recipe while a stepped dump is pending. -/
namespace Leanux.Proofs.WG.LifetimeSafety.CursorWitness
open Leanux Leanux.WG

def replacementKey : Key := [127] ++ List.replicate 31 0

def replacementPeer : Peer :=
  { remoteStatic := replacementKey, presharedKey := [], precomputedStaticStatic := [],
    internalId := 55, refcount := 1 }

def staleCursor : DumpCtx := { hasWg := true, nextPeer := some 26 }

def replacementWorld : WGWorld :=
  let d : Device :=
    { ifindex := 4, ifname := "wg0", numPeers := 1,
      peers := Std.TreeMap.ofList [(26, replacementPeer)], peerList := [26],
      peerHashtable := [(replacementKey, 26)], nextPeer := 27 }
  { Runner.initialWG true with
    dev := some d
    peerCounter := 55
    nlSock8 := { ctx := staleCursor, cbRunning := true } }

def before : Option (Nat × Nat × Bool) :=
  (replacementWorld.dev.bind (·.peers[26]?)).map fun p =>
    (p.internalId, p.refcount, p.isDead)

/-- Result of the actual callback, retaining the store lookup and both
configuration indexes that should not point at a released live peer. -/
def afterDone : Option (Option Nat × List Nat × List Nat) := do
  let ((_, w), _) ← (((wgGetDeviceDone staleCursor).run replacementWorld).run
    { env := Runner.harnessEnv, timing := Env.timing }).toOption
  let d ← w.dev
  pure ((d.peers[26]?).map (·.internalId), d.peerList, d.peerHashtable.map (·.2))

end Leanux.Proofs.WG.LifetimeSafety.CursorWitness
