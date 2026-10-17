import Leanux.Proofs.WG.Config.Precomputation
import Leanux.Proofs.WG.Index.Table
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def zeroedHandshake (p : Peer) : Peer :=
  { p with
    ephemeralPrivate := List.replicate 32 0
    remoteEphemeral := List.replicate 32 0
    hash := List.replicate 32 0
    chainingKey := List.replicate 32 0
    remoteIndex := 0
    handshakeState := 0 }

def expiryReadPrefix (pid : PeerId) : WG.M Unit := do
  requireNotPending pid "clearing the handshake"
  handshakeClear pid

def expiryZeroDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  withPeer { d with indexTable := d.indexTable.filter fun e => !(e.owner == .handshake pid) }
    pid (zeroedHandshake p)


/-- The original pre-clock prefix, including entry dereference and ordered
index removal before the handshake peer write. Stops remain partial. -/
theorem expiryReadPrefix_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (expiryReadPrefix pid) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (expiryZeroDevice d pid p)) := by
  let removed : Device := {d with indexTable := Index.removeOwner (.handshake pid) d.indexTable}
  let zeroed := withPeer removed pid (zeroedHandshake p)
  have hword : Ensures (IndexOwner.peerDeref (.handshake pid))
      (fun g => g.dev = some d) (fun _ g => g.dev = some d) := by
    intro g ambient result final after device run
    cases word : p.handshakeEntryPeer <;>
      simp [IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev, device, resident,
        word, unsupported, AmbientM.unsupported] at run
    · cases run
    · rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact device
  have hremove : Ensures (liftIndex (indexRemove (.handshake pid)))
      (fun g => g.dev = some d) (fun _ g => g.dev = some removed) := by
    intro g ambient result final after device run
    obtain ⟨u, out, tail, execution, post⟩ := Index.indexRemove_exact (.handshake pid) d g ambient device
    rw [run] at execution
    cases execution
    exact post
  have hclear : Ensures (handshakeClear pid) (fun g => g.dev = some d)
      (fun _ g => g.dev = some zeroed) := by
    unfold handshakeClear
    refine ensures_bind _ _ hword ?_
    intro _
    refine ensures_bind _ _ hremove ?_
    intro _ g ambient result final after device run
    simp [handshakeZero, getPeer, getDev, device, removed, resident, setPeer, modifyDev] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl
  unfold expiryReadPrefix
  simp only [requireNotPending, pure_bind]
  exact hclear

end Leanux.Proofs.WG.Config
