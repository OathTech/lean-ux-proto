import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshakeSendFrames

/-! Native keepalive preparation may stage one plaintext; only the original
staged-send continuation allocates and publishes TX packet occurrences. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

def keepalivePrepare (pid : PeerId) : WG.M Bool := do
  let p ← getPeer pid
  if ← branch .keepaliveStagedEmpty p.staged.isEmpty then
    if ← branch .keepaliveNoMem !(← hiddenAlloc .keepaliveSkb) then return false
    setPeer pid { p with staged := p.staged ++ [{ mtu := (← getDev).mtu }] }
  pure true

theorem keepalive_factor (pid : PeerId) : sendKeepalive pid = (do
    let ready ← keepalivePrepare pid
    if ready then sendStagedPackets pid) := by
  unfold sendKeepalive keepalivePrepare
  simp only [bind_assoc]
  congr 1
  funext p
  congr 1
  funext empty
  split
  · simp only [bind_assoc]
    congr 1
    funext allocation
    congr 1
    funext refused
    split
    · simp
    · simp only [bind_assoc]
      congr 1
  · simp

theorem keepalive_prepare_wire (pid : PeerId) : SameView txCryptWire (keepalivePrepare pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold keepalivePrepare
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' crypt_wire_step initial

theorem keepalive_prepare_queues (pid : PeerId) : SameView handoffTxView (keepalivePrepare pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold keepalivePrepare
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head getDev; exact (getDev_sameWGStore.of_factor
        (fun s => handoffTxView {dev := s.dev}) handoffTxView (fun _ => rfl)).wp (· = initial))
    | crypt_queue_step initial

theorem keepalive_prepare_geometry (pid : PeerId) :
    SameView StagingOccurrences.geometry (keepalivePrepare pid) := by
  intro initial
  change Preserves (fun w => StagingOccurrences.geometry w = initial) _
  unfold keepalivePrepare
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | staging_geometry_step initial

theorem keepalive (pid : PeerId) : Preserves (OccurrenceStack.Ready locals active) (sendKeepalive pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have allocated := Allocated.native (sendKeepalivePrefix_erases pid)
    (sendKeepalivePrefix_preserves_ambient allocationAmbient allocationTx pid) before.1 a b run
  cases result
  rw [keepalive_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,prepared,tail⟩ := run
  have physical := (hoare_iff_run_ambient _ _ _).mp
    (TransmitOccurrences.passive (keepalive_prepare_geometry pid)
      (keepalive_prepare_wire pid) (keepalive_prepare_queues pid))
    w a ready u c ⟨before.1.bounded,before.2⟩ prepared
  refine ⟨allocated,?_⟩
  cases ready with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact physical.2
  | true =>
    simp only [ite_true] at tail
    exact CryptStaging.staged ⟨⟨physical.1,physical.2.1⟩,physical.2.2⟩ pid c b tail

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
