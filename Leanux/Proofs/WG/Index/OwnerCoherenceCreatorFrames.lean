import Leanux.Proofs.WG.Index.OwnerCoherenceCreatorModel
import Leanux.Proofs.WG.Index.OwnerCoherenceTableSource
import Leanux.Proofs.WG.Index.OwnerCoherenceSessionFrames
import Leanux.Proofs.WG.Noise.SlotFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Native writes to the publishing peer preserve the joint owner invariant
when the embedded owner word and count remain unchanged. -/
theorem modifyPeer_handshakePublisher (pid : PeerId) (f : Peer → Peer)
    (word : ∀ p, (f p).handshakeEntryPeer = p.handshakeEntryPeer)
    (count : ∀ p, (f p).refcount = p.refcount) :
    Ensures (modifyPeer pid f)
      (fun g => ∀ d, g.dev = some d → HandshakePublisher pid d)
      (fun _ g => ∀ d, g.dev = some d → HandshakePublisher pid d) := by
  intro g ambient result final after pre run
  change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
  cases device : g.dev with
  | none =>
    simp [getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      have coherent := (pre d device).1
      obtain ⟨target, q, oldWord, found, positive, self⟩ := (pre d device).2
      change target = pid at self
      subst target
      have same : q = p := Option.some.inj (found.symm.trans resident)
      subst q
      have own : p.handshakeEntryPeer = some pid := by
        simpa [ownerWord, resident] using oldWord
      simp [getPeer, getDev, device, resident, setPeer, modifyDev] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      intro current present
      cases present
      refine ⟨peerWrite_owner_coherent d pid p (f p) resident (word p) (count p) coherent, ?_⟩
      refine ⟨pid, f p, ?_, by simp, ?_, rfl⟩
      · simp [ownerWord, word, own]
      · simpa [count] using positive

/-- The actual guarded insertion publishes the explicitly coherent owner;
all source collisions, exhausted draws and missing-device Stops remain. -/
theorem indexInsert_handshakePublisher (pid : PeerId) :
    Ensures (liftIndex (indexInsert (.handshake pid)))
      (fun g => ∀ d, g.dev = some d → HandshakePublisher pid d)
      (fun _ g => ∀ d, g.dev = some d → HandshakePublisher pid d) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [liftIndex, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨effect, coherent⟩ := indexInsert_owner_coherence (.handshake pid) d
      (pre d device).1 (pre d device).2 g ambient result final after device run
    change final.dev = _ at effect
    intro current present
    rw [effect] at present
    cases present
    exact ⟨coherent, (pre d device).2⟩

end Leanux.Proofs.WG.Index
