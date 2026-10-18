import Leanux.Proofs.WG.Queues.FundedHandoff

/-! The TX rekey check keeps the actual queued-handshake handoff in the
funding account. Its conditional clock/key reads do not assume validity,
successful queueing, or a normal return from a partial source guard. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.TxReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- The actual TX freshness prefix only reads WG state before its possible
queued-handshake call. This rule composes that real call under any predicate. -/
theorem keepKeyFresh_preserves (P : WGWorld → Prop) (pid : PeerId)
    (queued : Preserves P (sendQueuedHandshakeInitiation pid false)) :
    Preserves P (keepKeyFresh pid) := by
  have getter : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi hr
    exact (getPeer_normal pid w v p a b hr).1 ▸ hi
  have keyGetter (kid : KeypairId) : Preserves P (getKeypair kid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a key v b hi hr
    exact (KeyTimes.getKeypair_return kid w v key a b hr).1 ▸ hi
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact getter)
    | (index_material_head getKeypair; exact keyGetter _)
    | (index_material_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp P)
    | (index_material_head sendQueuedHandshakeInitiation; exact queued)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem keepKeyFresh_transfers (pid : PeerId) : Transfers (keepKeyFresh pid) := by
  apply (Transfers.iff_run_ambient _).mpr
  intro w a result v b hr
  exact (hoare_iff_run_ambient _ _ _).mp
    (keepKeyFresh_preserves (Transfer w) pid
      (Transfers.wp (project := id) (sendQueued_transfers pid false) w))
    w a result v b (Transfer.refl w) hr

private theorem fresh_keys (pid : PeerId) : KeyEffects NoPromotion (keepKeyFresh pid) := by
  apply keyEffects_of_wp
  intro initial
  exact keepKeyFresh_preserves (KeyEffect NoPromotion initial) pid
    (KeyEffects.wp (queued_keyEffect (allowed := NoPromotion) pid false) initial)

private theorem fresh_stable (pid : PeerId) (hs : StableRx cs w)
    (a b : Ambient) (hr : ((keepKeyFresh pid).run w).run a = .ok (((),v),b)) :
    StableRx cs v := by
  obtain ⟨delta,handoff⟩ := (Transfers.iff_run_ambient _).mp (keepKeyFresh_transfers pid)
    w a () v b hr
  apply hs.retains
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp (RxRing.keepKeyFresh_cell pid) w a () v b hr
  · exact handoff.rx
  · exact (hoare_iff_run_ambient _ _ _).mp
      (keepKeyFresh_preserves (ResidentsRetained (rxQueues w) ∘ rxQueues) pid
        (RetainsRx.wp (sendQueuedHandshakeInitiation_rxQueues pid false) (rxQueues w)))
      w a () v b (rx_retained_refl _) hr
  · exact (hoare_iff_run_ambient _ _ _).mp
      (keepKeyFresh_preserves (NapiFrames.Retained (NapiFrames.napiView w)) pid
        ((pinned_const _private.Leanux.Proofs.WG.Queues.NapiFrames.«0».Leanux.Proofs.WG.Queues.NapiFrames.sendQueued_preserves)
          pid false (NapiFrames.napiView w))) w a () v b (NapiFrames.refl w) hr

/-- Any durable handoff made by the real TX freshness check stays charged
alongside the original supplied obligations. The stable RX ledger is unchanged. -/
theorem keepKeyFresh_funded (pid : PeerId) (hi : CarrierState cs loans w)
    (hs : StableRx cs w) (a b : Ambient)
    (hr : ((keepKeyFresh pid).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧
      CarrierState cs (loans ++ delta.owners) v ∧ StableRx cs v := by
  have transferred := (Transfers.iff_run_ambient _).mp (keepKeyFresh_transfers pid) w a () v b hr
  have effect := (KeyEffects.iff_run_ambient _ _).mp (fresh_keys pid) w a () v b hr
  obtain ⟨delta,step⟩ := transferred
  have keys : KeysCompatible v :=
    ⟨effect.rxCompatible step.rx hi.keys.1,
      effect.currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩
  obtain ⟨actual,step,funded⟩ := hi.transfer_funded ⟨delta,step⟩ keys
  exact ⟨actual,step,funded,fresh_stable pid hs a b hr⟩

end Leanux.Proofs.WG.Queues.RxCredits.TxReservation
