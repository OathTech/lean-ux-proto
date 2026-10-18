import Leanux.Proofs.WG.Index.ConfigurationStageSource
import Leanux.Proofs.WG.Index.ConfigurationUpdateSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem keepaliveSetup_entry (cs : Ledger) (loans : Reservations)
    (pid : PeerId) (interval : Nat) (running : Bool) :
    Preserves (Entry cs loans) (HolderConfigTail.setup pid interval running) := by
  apply peerReadUpdate_preserves (Entry cs loans) pid (fun p => {p with persistentKeepaliveInterval:=interval})
  · intro p initial
    change Preserves (fun w : WGWorld => w=initial) _
    unfold WG.andM
    simp (config := {zeta:=false}) only [branch]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  · apply join_entry cs loans _
    · exact (pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.modifyPeer)
        pid _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
        (fun _ _ h=>h) (fun _=>rfl) (fun _=>rfl)
    · exact (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.update_peer)
        pid _ (fun _=>rfl)
    · intro w a result v b pre run
      exact (hoare_iff_run_ambient _ _ _).mp
        (frame_core (modifyPeer_fields pid (fun p=>{p with persistentKeepaliveInterval:=interval})
          (fun _=>rfl))) w a result v b pre.2 run

theorem keepalive_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (sendKeepalive pid) := by
  apply join_entry cs loans _
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    exact ⟨(hoare_iff_run_ambient _ _ _).mp (HolderTimers.keepalive_boundary pid)
      w a result v b pre.1 run,
      BaseCoherence.transport pre.2.1
        ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.keepalive_view pid) w a result v b run),
      (hoare_iff_run_ambient _ _ _).mp (ConfiguredTraffic.keepalive pid) w a result v b pre.2.2 run⟩
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive_slots) pid
  · exact StagingRich.keepalive_core pid

theorem out_entry (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (ret : Int) :
    Hoare (do peerPut (some paid.slot)
              _ ← branch .peerZeroPsk attrs.presharedKey.isSome
              pure ret : WG.M Int)
      (Entry cs (paid::loans)) (fun _=>Entry cs loans) := by
  apply hoare_bind _ _ ((ensures_iff _ _ _).mp (pay cs loans paid))
  intro _
  exact preserves_bind (hoare_liftAmbient (AmbientM.branch .peerZeroPsk attrs.presharedKey.isSome) _)
    (fun _=>preserves_pure ret)

theorem finish_entry (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (ret : Int) :
    Hoare (peerTailFinishSource attrs (some paid.slot) paid.slot ret)
      (Entry cs (paid::loans)) (fun _=>Entry cs loans) := by
  rw [HolderConfigTail.finish_factor]
  apply hoare_bind _ _ (read_entry cs (paid::loans))
  intro d
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerHasKeepalive attrs.keepalive.isSome) _)
  intro keep
  have tail : Hoare (do
      if ← branch .peerRunning d.running then sendStagedPackets paid.slot
      peerPut (some paid.slot)
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) (Entry cs (paid::loans)) (fun _=>Entry cs loans) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerRunning d.running) _)
    intro running
    cases running with
    | false => exact out_entry cs loans paid attrs ret
    | true =>
      exact hoare_bind _ _ (staged_entry cs (paid::loans) paid.slot)
        (fun _=>out_entry cs loans paid attrs ret)
  cases keep with
  | false => exact tail
  | true =>
    apply hoare_bind _ _ (keepaliveSetup_entry cs (paid::loans) paid.slot (attrs.keepalive.getD 0) d.running)
    intro send
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) _)
    intro keepNow
    cases keepNow with
    | false => exact tail
    | true => exact hoare_bind _ _ (keepalive_entry cs (paid::loans) paid.slot) (fun _=>tail)

end Leanux.Proofs.WG.Index.ConfigurationIndex
