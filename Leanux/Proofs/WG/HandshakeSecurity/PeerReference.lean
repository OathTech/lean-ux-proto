import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveFrames
import Leanux.Proofs.WG.Queues.RxCleanupProtection

/-! Resident peer reference positivity is independent of the holder budget.
The invariant concerns normal source boundaries: a stopped final release can
have performed its decrement before reporting a queue or timer failure. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

variable {w v : WGWorld} {d : Device} {pid : PeerId} {peer : Peer}

def view (w : WGWorld) : PeerId → Option Nat :=
  fun pid => (w.dev.bind fun d => d.peers[pid]?).map Peer.refcount

def Positive (counts : PeerId → Option Nat) : Prop :=
  ∀ pid count, counts pid = some count → 0 < count

def Inv (w : WGWorld) : Prop := Positive (view w)

theorem resident (before : Inv w) (device : w.dev = some d)
    (found : d.peers[pid]? = some peer) : 0 < peer.refcount :=
  before pid peer.refcount (by simp [view,device,found])

theorem of_residents (positive : ∀ (d : Device) (pid : PeerId) (peer : Peer), w.dev = some d →
    d.peers[pid]? = some peer → 0 < peer.refcount) : Inv w := by
  intro pid count found
  cases device : w.dev with
  | none => simp [view,device] at found
  | some d =>
    cases stored : d.peers[pid]? with
    | none => simp [view,device,stored] at found
    | some peer =>
      have same : peer.refcount = count := by simpa [view,device,stored] using found
      exact same ▸ positive d pid peer device stored

theorem replace (before : Inv w) (pid : PeerId) (peer : Peer)
    (positive : 0 < peer.refcount) :
    Inv {w with dev := w.dev.map fun d => {d with peers := d.peers.insert pid peer}} := by
  apply of_residents
  intro d other out device found
  cases initial : w.dev with
  | none => simp [initial] at device
  | some old =>
    have same : d = {old with peers := old.peers.insert pid peer} := by
      simpa only [initial,Option.map_some,Option.some.injEq] using device.symm
    subst d
    by_cases eq : pid = other
    · subst other
      have same : peer = out := by simpa using found
      exact same ▸ positive
    · exact resident before initial (by simpa [Std.TreeMap.getElem?_insert,eq] using found)

theorem erase (before : Inv w) (device : w.dev = some d) (pid : PeerId) :
    Inv {w with dev := some {d with peers := d.peers.erase pid}} := by
  apply of_residents
  intro out other peer same found
  cases same
  by_cases eq : pid = other
  · subst other; simp at found
  · exact resident before device (by simpa [Std.TreeMap.getElem?_erase,eq] using found)

theorem absent (none : w.dev = none) : Inv w := by
  intro pid count found
  simp [view,none] at found

theorem initial (net bare : Bool) : Inv (Runner.initialWG net bare) := by
  cases net <;> cases bare <;> intro pid count found <;>
    simp [view,Runner.initialWG] at found

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
