import Leanux.Proofs.WG.HandshakeSecurity.ResponderH1
import Leanux.Proofs.WG.Lifetimes.Store

/-! Pending allocation identities, observed at the native confirmation cut.
The inventory is indexed by peer slots; clearing, deletion and replacement may
remove tickets. Confirmation history is separate from current-slot permission.
This module supplies local transport, not initialized driver closure. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

def nextSlot (w : WGWorld) (pid : PeerId) : Option KeypairId :=
  (w.dev.bind fun d => d.peers[pid]?).bind Peer.keypairNext

def view (w : WGWorld) : Store PeerId :=
  ⟨w.keypairCounter,fun pid => (nextSlot w pid).bind (keypairResidents w)⟩

def label (kid : KeypairId) (r : WGRunWitness Bool) : Option Nat :=
  if r.value then keypairResidents r.before kid else none

structure Inv (confirmed : List Nat) (w : WGWorld) : Prop where
  bounded : Bounded (view w)
  unique : Unique (view w)
  distinct : confirmed.Nodup
  past : ∀ stamp ∈ confirmed, stamp ≤ w.keypairCounter
  absent : ∀ stamp ∈ confirmed, Absent (view w) stamp

theorem Inv.retained (hi : Inv confirmed w) (step : Retained (view w) (view v)) :
    Inv confirmed v := by
  refine ⟨step.bounded hi.bounded,step.unique hi.unique,hi.distinct,?_,?_⟩
  · intro stamp member
    change stamp ≤ (view v).frontier
    rw [step.1]
    exact hi.past stamp member
  · intro stamp member
    exact step.absent (hi.absent stamp member)

theorem Inv.advanced (hi : Inv confirmed w) (step : Transition (view w) (view v))
    (bounded : Bounded (view v)) (unique : Unique (view v)) : Inv confirmed v := by
  refine ⟨bounded,unique,hi.distinct,?_,?_⟩
  · intro stamp member
    exact Nat.le_trans (hi.past stamp member) step.1
  · intro stamp member
    exact step.absent (hi.past stamp member) (hi.absent stamp member)

/-- The local native receipt consumes its pending allocation before any later
caller Stop. The old history cannot already contain that allocation. -/
theorem Inv.confirmed {confirmed : List Nat} (hi : Inv confirmed w) (pid : PeerId) (stamp : Nat)
    (resident : (view w).slots pid = some stamp)
    (step : Retained ((view w).put pid none) (view v)) :
    Inv (confirmed ++ [stamp]) v := by
  have fresh : stamp ∉ confirmed := fun member => hi.absent stamp member pid resident
  refine ⟨step.bounded (erase_bounded _ _ hi.bounded),
    step.unique ((erase_retained _ _).unique hi.unique),?_,?_,?_⟩
  · exact List.nodup_append.mpr ⟨hi.distinct,by simp,by
      intro a old b new same
      have : b = stamp := by simpa only [List.mem_singleton] using new
      have equal : a = stamp := same.trans this
      exact fresh (equal ▸ old)⟩
  · intro value member
    have front : v.keypairCounter = w.keypairCounter := step.1
    rw [front]
    rcases List.mem_append.mp member with old | new
    · exact hi.past value old
    · have same : value = stamp := by simpa only [List.mem_singleton] using new
      subst value
      exact hi.bounded pid stamp resident
  · intro value member
    rcases List.mem_append.mp member with old | new
    · exact step.absent ((erase_retained _ _).absent (hi.absent value old))
    · have same : value = stamp := by simpa only [List.mem_singleton] using new
      subst value
      exact step.absent (hi.unique.erase_absent resident)

theorem view_initial (net bare : Bool) :
    view (Runner.initialWG net bare) = ⟨0,fun _ => none⟩ := by
  unfold view nextSlot keypairResidents Runner.initialWG
  split <;> rfl

theorem initial (net bare : Bool) : Inv [] (Runner.initialWG net bare) := by
  refine ⟨?_,?_,by simp,by simp,by simp⟩
  · rw [view_initial]
    intro pid stamp impossible
    cases impossible
  · rw [view_initial]
    intro pid other stamp impossible
    cases impossible

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
