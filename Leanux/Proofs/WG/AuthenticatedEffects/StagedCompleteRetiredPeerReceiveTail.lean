import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeMaintenance

/-! Actual receive completion repays the selected owner after statistics and
timer work. The response session uses the actual staged-send account delta. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

theorem boundary {action : WG.M α}
    (same : ∀holders, Preserves (Account holders cs loans) action) :
    Preserves (ExactBoundary cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b input run
  obtain ⟨holders,account⟩ := input
  exact ⟨holders,(hoare_iff_run_ambient _ _ _).mp (same holders) w a x v b account run⟩

theorem device (f : Device → Device)
    (same : ∀ w, HolderEncrypt.fields {w with dev := w.dev.map f}=HolderEncrypt.fields w) :
    Preserves (Account holders cs loans) (modifyDev f) := by
  apply Account.native_fields
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  exact same w

theorem finish_account (o : Owner) (msg : List UInt8) : Hoare (HandshakeReceive.finish (some o.slot) o.slot msg)
    (Account holders cs (o::loans)) (fun _ => Account holders cs loans) := by
  have stats : Preserves (Account holders cs (o::loans))
      (modifyDev fun d => {d with rxPackets := d.rxPackets+1,rxBytes:=d.rxBytes+msg.length}) := by
    apply device
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd : w.dev <;> simp [hd,rxView]
  unfold HandshakeReceive.finish timersAnyAuthenticatedPacketReceived
  rw [← bind_assoc]
  apply hoare_bind _ _ (Account.update o.slot (fun p => {p with rxBytes:=p.rxBytes+msg.length})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl))
  intro _
  apply hoare_bind _ _ stats
  intro _
  apply hoare_bind _ _ (del_timer _ _)
  intro _
  apply hoare_bind _ _ (traversal _)
  intro _
  exact payment o


theorem finish_selected (o : Owner) (msg : List UInt8) :
    Hoare (HandshakeReceive.finishSelected (some o.slot) msg)
      (Account holders cs (o::loans)) (fun _ => Account holders cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b account run
  change ((HandshakeReceive.finish (some o.slot) o.slot msg).run w).run
    (CounterWindow.record a .hsWrongPacket false) = .ok ((x,v),b) at run
  exact (hoare_iff_run_ambient _ _ _).mp (finish_account o msg) w _ x v b account run

/-- Both actual response-session outcomes preserve a single exact account;
only its genuine keepalive/staging branch can add durable holders. -/
theorem response_session (pid : PeerId) : Hoare (HandshakeReceive.responseSession pid)
    (fun w => ExactBoundary cs loans w ∧ ConfiguredIdentity.Inv w ∧ OwnerBounds.Carrier w ∧ CurrentSlots.Inv w)
    (fun _ => ExactBoundary cs loans) := by
  have first : Hoare (beginSession pid)
      (fun w => ExactBoundary cs loans w ∧ ConfiguredIdentity.Inv w ∧ OwnerBounds.Carrier w ∧ CurrentSlots.Inv w)
      (fun _ => ExactBoundary cs loans) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hi run
    obtain ⟨⟨holders,account⟩,configured,owners,slots⟩ := hi
    exact ⟨holders,session account pid configured owners slots a b run⟩
  unfold HandshakeReceive.responseSession
  apply hoare_bind _ _ first
  intro result
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsRespSessionBegun result) (ExactBoundary cs loans))
  intro begun
  cases begun with
  | false => exact preserves_pure _
  | true =>
    apply preserves_bind (boundary (fun _ => derived pid))
    intro _
    apply preserves_bind (boundary (fun _ => completed pid .walltimeLastHandshake))
    intro _
    exact keepalive_boundary pid

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
