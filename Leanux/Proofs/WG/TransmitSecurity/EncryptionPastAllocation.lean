import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastFrames

/-! Native batch allocation advances the shared packet frontier and returns
fresh IDs. Every previously encrypted identity is excluded from this batch,
including after a failed or abandoned earlier submission. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option pp.structureInstances false

def Admissible (past : List (Option Nat × SkbId)) (items : List SkbId) (s : View) : Prop :=
  ∀ d, s.device = some d → ∀ label ∈ past, label.1 = some d.epoch → label.2 ∉ items

private theorem cursor (packets : List DataPacket) :
    SameView (fun w : WGWorld => w.netIfindexNext) (packets.mapM newTxSkb) := by
  intro initial
  induction packets with
  | nil => exact preserves_pure []
  | cons packet packets ih =>
    simp only [List.mapM_cons]
    apply preserves_bind
    · unfold newTxSkb
      apply hoare_liftSkb
      intro w d store before device
      exact before
    · intro id
      exact preserves_bind ih (fun _ => preserves_pure _)

/-- Allocation does not admit work by itself; its returned IDs are disjoint
from every prior encryption and may safely be offered once to the native ring. -/
theorem allocate (packets : List DataPacket) (before : Inv past active (view w))
    (a b : Ambient) (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    Inv past active (view v) ∧ Admissible past items (view v) := by
  have epochs : v.netIfindexNext = w.netIfindexNext :=
    (ProjectedAction.iff_run_ambient _ _ _).mp (cursor packets) w a items v b run
  have ring := (ProjectedAction.iff_run_ambient _ _ _).mp
    (TxDisposition.LiveFrontier.allocation_ring packets) w a items v b run
  cases device : w.dev with
  | none =>
    cases packets with
    | nil => cases run; exact ⟨before,by intro d found; simp [view,device] at found⟩
    | cons packet packets =>
      simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨_,_,_,first,_⟩ := run
      simp [newTxSkb,liftSkb_run,device] at first
  | some d =>
    obtain ⟨ids,_,e,endpoint,frontier,epoch,_⟩ := TxDisposition.ItemSeparation.allocate_result packets device run
    have rings : e.encryptQueue = d.encryptQueue := by
      have pair : (e.ifindex,e.encryptQueue) = (d.ifindex,d.encryptQueue) := by
        simpa only [TxRing.nativeCell,device,endpoint,Option.map_some,Option.some.injEq] using ring
      exact congrArg Prod.snd pair
    have kept : Inv past active (view v) := by
      refine ⟨before.1,?_⟩
      intro label member
      apply (before.2 label member).shrink
      · exact Nat.le_of_eq epochs.symm
      · intro current found
        have same : current = ⟨e.ifindex,e.nextSkb,e.encryptQueue.items⟩ := by
          simpa only [view,endpoint,Option.map_some,Option.some.injEq] using found.symm
        subst current
        refine ⟨⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩,by simp [view,device],epoch,?_,?_⟩
        · rw [frontier]; exact Nat.le_add_right _ _
        · intro id member
          simpa only [rings] using member
    refine ⟨kept,?_⟩
    intro current found label member matching
    have same : current = ⟨e.ifindex,e.nextSkb,e.encryptQueue.items⟩ := by
      simpa only [view,endpoint,Option.map_some,Option.some.injEq] using found.symm
    subst current
    obtain ⟨generation,tag,_,safe⟩ := before.2 label member
    have sameEpoch : d.ifindex = generation := by
      exact epoch.symm.trans (Option.some.inj (matching.symm.trans tag))
    have bound := (safe ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩ (by simp [view,device]) sameEpoch).1
    intro inBatch
    rw [ids] at inBatch
    obtain ⟨offset,_,equal⟩ := List.mem_range'.mp inBatch
    have lower : d.nextSkb ≤ label.2 := by
      simpa only [equal,Nat.one_mul] using Nat.le_add_right d.nextSkb offset
    exact (Nat.not_lt_of_ge lower) bound

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
