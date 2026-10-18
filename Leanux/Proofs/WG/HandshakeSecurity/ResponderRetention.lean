import Leanux.Proofs.WG.HandshakeSecurity.ResponderCoreTraffic
import Leanux.Proofs.WG.Queues.RxKeyProtection
import Leanux.Proofs.WG.Queues.CurrentSlotFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues.RxCredits Lifetimes

theorem current_pool (w : WGWorld) (pid : PeerId) :
    current w pid = (w.dev.bind fun d => d.peers[pid]?).bind
      (fun p => p.keypairCurrent.bind (pool w)) := by
  cases device : w.dev with
  | none => simp [current, device]
  | some d =>
    have poolEq : pool w = fun kid => (d.keypairs[kid]?).map keyCore := by
      funext kid
      simp [pool, device]
    rw [poolEq]
    cases peer : d.peers[pid]? <;> simp [current, device, peer]

/-- Slot retention and immutable key retention together preserve the concrete
current responder identity; neither constituent alone implies this fact. -/
theorem current_retained {w v : WGWorld}
    (slots : KeyEffect NoPromotion w v) (keys : Retains (pool w) (pool v)) :
    ∀ pid core, current v pid = some core → current w pid = some core := by
  intro pid core resident
  rw [current_pool] at resident ⊢
  obtain ⟨p, peer, rest⟩ := Option.bind_eq_some_iff.mp resident
  obtain ⟨kid, currentSlot, material⟩ := Option.bind_eq_some_iff.mp rest
  have cell : currentCells v pid = some (p.internalId, some kid) := by
    simp [currentCells, peer, currentCell, currentSlot]
  obtain ⟨old, before, change⟩ := slots.currents pid p.internalId (some kid) cell
  rcases change with change | ⟨_, _, impossible⟩
  · obtain ⟨oldPeer, oldResident, fields⟩ := Option.map_eq_some_iff.mp before
    have oldSlot : oldPeer.keypairCurrent = some kid :=
      (congrArg Prod.snd fields).trans change.symm
    rw [oldResident, Option.bind_some, oldSlot, Option.bind_some]
    exact keys kid core material
  · cases impossible

theorem current_retained_fields {w v : WGWorld}
    (fields : CurrentSlots.fields v = CurrentSlots.fields w)
    (keys : Retains (pool w) (pool v)) :
    ∀ pid core, current v pid = some core → current w pid = some core := by
  intro pid core resident
  rw [current_pool] at resident ⊢
  obtain ⟨p, peer, rest⟩ := Option.bind_eq_some_iff.mp resident
  obtain ⟨kid, currentSlot, material⟩ := Option.bind_eq_some_iff.mp rest
  have cells := congrFun (congrArg (fun f => f.2.1) fields) pid
  have afterCell : ((v.dev.bind fun d => d.peers[pid]?).map CurrentSlots.slotCell) =
      some (some kid, p.keypairPrevious, p.keypairNext) := by
    simp [peer, CurrentSlots.slotCell, currentSlot]
  have beforeCell : ((w.dev.bind fun d => d.peers[pid]?).map CurrentSlots.slotCell) =
      some (some kid, p.keypairPrevious, p.keypairNext) := cells.symm.trans afterCell
  obtain ⟨oldPeer, oldResident, shape⟩ := Option.map_eq_some_iff.mp beforeCell
  have oldSlot : oldPeer.keypairCurrent = some kid := congrArg Prod.fst shape
  rw [oldResident, Option.bind_some, oldSlot, Option.bind_some]
  exact keys kid core material

theorem Authorized.retain {confirmed : List Nat} {w v : WGWorld}
    (entry : Authorized confirmed w) (slots : KeyEffect NoPromotion w v)
    (keys : Retains (pool w) (pool v)) : Authorized confirmed v := by
  intro pid core resident responder
  exact entry pid core (current_retained slots keys pid core resident) responder

/-- Full native staging cannot introduce an unconfirmed responder as current,
including all no-key/drop branches and final-release deletion. -/
theorem sendStagedPackets_authorized (pid : PeerId) (confirmed : List Nat) :
    Preserves (Authorized confirmed) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  apply entry.retain
  · exact (KeyEffects.iff_run_ambient _ _).mp
      (staged_send_keyEffect (allowed := NoPromotion) pid) w a result v b run
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (sendStagedPackets_core pid) w a result v b run

end Leanux.Proofs.WG.HandshakeSecurity.Responder
