import Leanux.Proofs.WG.Noise.PendingTicketClaims
import Leanux.Proofs.WG.Keypairs.MaterialOrigin
import Leanux.Proofs.WG.Queues.CurrentSlotFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes

def pending (d : Device) (pid : PeerId) : Option Nat := do
  let p ← d.peers[pid]?
  let kid ← p.keypairNext
  let k ← d.keypairs[kid]?
  pure k.internalId

def view (w : WGWorld) : Store PeerId :=
  ⟨w.keypairCounter, fun pid => w.dev.bind fun d => pending d pid⟩

theorem view_bounded (h : List LifetimeEvent) (w : WGWorld)
    (allocation : AllocationInv h w) : Bounded (view w) := by
  intro pid stamp present
  simp only [view] at present ⊢
  obtain ⟨d,device,member⟩ := Option.bind_eq_some_iff.mp present
  unfold pending at member
  obtain ⟨p,peer,member⟩ := Option.bind_eq_some_iff.mp member
  obtain ⟨kid,next,member⟩ := Option.bind_eq_some_iff.mp member
  obtain ⟨k,key,eq⟩ := Option.bind_eq_some_iff.mp member
  have stamped : k.internalId = stamp := Option.some.inj eq
  exact allocation.keyBounded kid stamp (by
    simp [keyStore,keypairResidents,device,key,stamped])

theorem view_initial (net bare : Bool) :
    view (Runner.initialWG net bare) = {frontier:=0,slots:=fun _=>none} := by
  unfold view pending Runner.initialWG
  split <;> rfl

/-- Slot bounds prohibit allocation from reviving a dangling pending slot.
The original global counter advances even before a pending ticket is installed. -/
theorem allocation_view (w : WGWorld) (d : Device) (word : Option PeerId)
    (device : w.dev = some d) (slots : CurrentSlots.Inv w) :
    view (keyAllocationWorld w d word) = advance (view w) := by
  apply Store.ext
  · rfl
  · funext pid
    change pending (keyAllocationDevice d (w.keypairCounter+1) word) pid =
      w.dev.bind (fun d => pending d pid)
    rw [device]
    simp only [Option.bind_some]
    unfold pending
    cases peer : d.peers[pid]? with
    | none => simp [keyAllocationDevice,peer]
    | some p =>
      cases next : p.keypairNext with
      | none => simp [keyAllocationDevice,peer,next]
      | some kid =>
        have below := ((CurrentSlots.inv_iff w).mp slots d pid p kid device peer
          (Or.inr (Or.inr next))).1
        have key := (MaterialOrigin.allocation_fields w d word kid below).2.2.2
        simpa [keyAllocationDevice,peer,next] using
          congrArg (fun item : Option Keypair => item.bind (fun k => some k.internalId)) key

theorem allocation_unused_step (w : WGWorld) (d : Device) (word : Option PeerId)
    (device : w.dev = some d) (slots : CurrentSlots.Inv w) :
    Step (view w) none (view (keyAllocationWorld w d word)) := by
  rw [allocation_view w d word device slots]
  exact .unused (Retained.refl _)

end Leanux.Proofs.WG.Noise.PendingTickets
