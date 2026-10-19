import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterActors
import Leanux.Proofs.WG.Queues.HolderEntryPollFree

/-! Observer and native endpoint facts are paired only on the same action.
The wrapper lemmas retain the original socket and netlink guard order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Frames
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

theorem pair (action : RxHistory.Obs α) (original : Leanux.M α)
    (erase : ErasesPrefix action original)
    (old : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe action)
    (account : ∀ w h, Inv cs loans h w → ∀ result v,
      original.run w=.ok (result,v) → ExactBoundary cs loans v.wg) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe action := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ := old w h hi.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at post
    exact ⟨post,account w h hi out.1 out.2 ((erase w h).symm.trans run)⟩

theorem pair_native (action : RxHistory.Obs α) (original : Leanux.M α)
    (erase : ErasesPrefix action original)
    (old : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe action)
    (account : Preserves (fun w : World => ExactBoundary cs loans w.wg) original) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe action :=
  pair action original erase old (fun w _ hi result v run =>
    (hoare_iff_run _ _ _).mp account w result v hi.2 run)

theorem lift (P : WGWorld → Prop) (action : WG.M α) (keeps : Preserves P action) :
    Preserves (fun w : World => P w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact (hoare_iff_run_ambient _ _ _).mp keeps w.wg w.ambient result v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) action w v result run)

theorem socket (P : World → Prop)
    (store : ∀ w v, wgStoreView v.wg=wgStoreView w.wg → P w → P v)
    (fd : Nat) (body : Leanux.M Int) (keeps : Preserves P body) :
    Preserves P (socketCallOn fd body) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.socket_spec) P store fd body keeps

theorem netlink (P : World → Prop)
    (store : ∀ w v, wgStoreView v.wg=wgStoreView w.wg → P w → P v)
    (body : Leanux.M Int) (keeps : Preserves P body) : Preserves P (netlinkRequest body) := by
  have ambient {β : Type} (action : AmbientM β) : Preserves P (liftAmbient action) :=
    productAmbient_spec action P (fun w _ hi => store w _ rfl hi)
  unfold netlinkRequest socketCall
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | exact keeps
    | (rx_retention_head socketCallOn; apply socket P store)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem rtnetlink (P : World → Prop)
    (store : ∀ w v, wgStoreView v.wg=wgStoreView w.wg → P w → P v)
    (body : Leanux.M Int) (keeps : Preserves P body) : Preserves P (rtnetlinkRequest body) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.rtnetlink_spec) P store body keeps

theorem normal (action : RxHistory.Obs α) (original : Leanux.M α)
    (erase : ErasesPrefix action original)
    (keeps : PrefixPreserves (Inv cs loans) OwnerChecks.Safe action)
    (hi : Inv cs loans h w) (run : original.run w=.ok (result,v)) :
    Inv cs loans (runPrefix action w h).2 v := by
  have actual := (erase w h).trans run
  have post := (keeps w h hi).choose_spec.2.2
  simpa only [actual] using post

theorem boundary (action : RxHistory.Obs α) (original : Leanux.M α)
    (erase : ErasesPrefix action original)
    (keeps : ∀ cs, PrefixPreserves (Inv cs []) OwnerChecks.Safe action) : Preserves Boundary original := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  obtain ⟨h,cs,entry⟩ := hi
  exact ⟨(runPrefix action w h).2,cs,normal action original erase (keeps cs) entry run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Frames
