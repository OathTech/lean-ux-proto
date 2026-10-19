import Leanux.Proofs.WG.RetirementSecurity.HolderControlKeys

/-! Quiet controls and real lifecycle effects are joined to the original
audit journal. The source run supplies each normal endpoint; stopped prefixes
retain only the existing owner journal safety claim. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderOuter
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem audit (action : AuditM α) (original : Leanux.M α)
    (erases : ErasesPrefix action original)
    (owner : PrefixPreserves (HolderEntry.Inv carriers loans) OwnerChecks.Safe (RxHistory.audit action))
    (keys : ∀{w h result v},Inv carriers loans temporary [] [] h w→
      original.run w=.ok (result,v)→HolderAccount temporary v.wg)
    (physical : Preserves (fun w : World=>OccurrenceStack.Ready [] [] w.wg) original)
    (live : Preserves (fun w : World=>KeySlotLiveness.Inv w.wg) original) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.audit action) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := owner w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix (RxHistory.audit action) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have native := ((RxHistory.audit_erases erases) w h).symm.trans run
    exact ⟨post,keys entry native,(hoare_iff_run _ _ _).mp physical w out.1 out.2 entry.2.2.1 native,
      post.1.1.2.1,(hoare_iff_run _ _ _).mp live w out.1 out.2 entry.2.2.2.2 native⟩

theorem audit_boundary (action : AuditM α) (original : Leanux.M α)
    (erases : ErasesPrefix action original)
    (owner : PrefixPreserves (HolderEntry.Inv carriers loans) OwnerChecks.Safe (RxHistory.audit action))
    (keeps : Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) original)
    (physical : Preserves (fun w : World=>OccurrenceStack.Ready [] [] w.wg) original)
    (live : Preserves (fun w : World=>KeySlotLiveness.Inv w.wg) original) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.audit action) :=
  audit action original erases owner (fun entry run=>
    ((hoare_iff_run _ _ _).mp keeps _ _ _
      (HolderBoundary.of_owner entry.2.1 entry.1 entry.2.2.2.2) run).1.1) physical live

theorem up : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.audit envWgUpAudit) :=
  audit_boundary _ _ envWgUpAudit_erases HolderEntryControls.up HolderLifecycle.env_up
    OccurrenceControls.env_up KeySlotControls.env_up

theorem down : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.audit envWgDownAudit) :=
  audit_boundary _ _ envWgDownAudit_erases HolderEntryControls.down HolderLifecycle.env_down
    OccurrenceControls.env_down KeySlotControls.env_down

theorem cleanup : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.audit envNetnsCleanupAudit) :=
  audit_boundary _ _ envNetnsCleanupAudit_erases HolderEntryControls.cleanup HolderLifecycle.env_cleanup
    OccurrenceControls.env_cleanup KeySlotControls.env_cleanup

theorem audit_store (action : AuditM α) (original : Leanux.M α)
    (erases : ErasesPrefix action original)
    (owner : PrefixPreserves (HolderEntry.Inv carriers loans) OwnerChecks.Safe (RxHistory.audit action))
    (same : SameProductStore original) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.audit action) :=
  audit action original erases owner (fun entry run=>((hoare_iff_run _ _ _).mp
    (HolderScheduled.extra_product same) _ _ _ entry.2 run).1)
    (OccurrenceControls.product_store same) (KeySlotControls.product_store same)

theorem route : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.audit routeIntoWg0Audit) :=
  audit_store _ _ routeIntoWg0Audit_erases HolderEntryControls.route routeIntoWg0_sameKernel

theorem deladdr (family : Nat) : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.audit (wgDeladdrAudit family)) :=
  audit_store _ _ (wgDeladdrAudit_erases family) (HolderEntryControls.deladdr family) (wgDeladdr_sameKernel family)

theorem delroute (family : Nat) : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.audit (wgDelrouteAudit family)) :=
  audit_store _ _ (wgDelrouteAudit_erases family) (HolderEntryControls.delroute family) (wgDelroute_sameKernel family)

theorem scalar_points (w : World) :
    ownershipPointView {dev:=(envScalarView w).2.2.2.dev}=ownershipPointView w.wg := by
  unfold ownershipPointView ownershipAt peerAt keyReferenceView keyAt packetKeyWords
  simp only [envScalarView,envScalarStore,envScalarDevice,productStoreView,wgStoreView,
    Option.map_bind,Option.bind_map,Function.comp_def,Option.isSome_map]

theorem mtu (n : Nat) : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.audit (setMtuAudit n)) := by
  apply audit _ _ (setMtuAudit_erases n) (HolderEntryControls.mtu n) _
    (OccurrenceControls.env_mtu n) (KeySlotControls.env_mtu n)
  intro w h result v entry run
  apply entry.2.1.points
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w result v run
  rw [←scalar_points v,←scalar_points w,same]

end Leanux.Proofs.WG.RetirementSecurity.HolderOuter
