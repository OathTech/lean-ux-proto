import Leanux.Proofs.WG.Index.ConfigurationAllowedRulesSource
import Leanux.Proofs.WG.Index.ConfigurationPeerModel
import Leanux.Proofs.WG.Index.ConfigurationAllowedSource
import Leanux.Proofs.WG.Index.ConfigurationTailSource
import Leanux.Proofs.WG.Index.ConfigurationLoanSource
import Leanux.Proofs.WG.Index.ConfigurationEndpointFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

/-- The original allowed-IP tail, including malformed attributes and negative
insertion results. Supplied contracts are for the actual native leaf calls and
same original cleanup, rather than replacement callbacks. -/
theorem allowedIps_rule (P Q : WGWorld → Prop) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (next : Int → WG.M Int)
    (allowed : ∀ ip, Preserves P (setAllowedip pid ip))
    (out : ∀ ret, Hoare (do
      peerPut peer
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) P (fun _=>Q))
    (finish : ∀ ret, Hoare (next ret) P (fun _=>Q)) :
    Hoare (peerAllowedIpsSource attrs peer pid next) P (fun _=>Q) :=
  allowedIps_members_rule P Q attrs peer pid next (fun ip _ => allowed ip) out finish

/-- Complete original acquired-peer tail. Any normal return pays the actual
selected caller loan, including early allowed-IP errors; all slot, accounting,
and index facts come from the current source prefix. -/
theorem tail_entry (cs : Ledger) (loans : Reservations) (paid : Owner) (attrs : PeerAttrs) :
    Hoare (peerConfigTailSource attrs (some paid.slot) paid.slot)
      (Entry cs (paid::loans)) (fun _=>Entry cs loans) := by
  rw [peerConfigTailSource_factor]
  exact allowedIps_rule _ _ attrs (some paid.slot) paid.slot _
    (setAllowedip_entry cs (paid::loans) paid.slot)
    (out_entry cs loans paid attrs) (finish_entry cs loans paid attrs)
theorem endpoint_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) (e : Endpoint) :
    Preserves (Entry cs loans) (setPeerEndpoint pid e) :=
  accounted_fields_entry cs loans _ (HolderConfigUpdate.endpoint_boundary pid e)
    (BaseCoherence.endpoint_view pid e) (ConfiguredReceiveLeaves.setPeerEndpoint_view pid e)
    (CurrentSlots.fields_preserves (project:=id)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) pid e))
    (endpoint_fields pid e)

theorem psk_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) (key : Key) :
    Preserves (Entry cs loans) (getPeer pid >>= fun p=>setPeer pid {p with presharedKey:=key}) := by
  apply join_entry cs loans _
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.modifyPeer)
      pid _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _=>rfl) (fun _=>rfl)
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.update_peer)
      pid _ (fun _=>rfl)
  · intro w a result v b pre run
    exact (hoare_iff_run_ambient _ _ _).mp
      (frame_core (modifyPeer_fields pid (fun p=>{p with presharedKey:=key}) (fun _=>rfl)))
      w a result v b pre.2 run

theorem updatePrefix_entry (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (paid : Owner) (flags : UInt32) (psk : Option Key) :
    Preserves (Entry cs loans) (HolderConfigUpdate.updatePrefix attrs paid flags psk) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigUpdate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate.prefix_factor)]
  apply preserves_bind
  · index_unfold _private.Leanux.Proofs.WG.Queues.HolderConfigUpdate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate.pskStep
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSetPsk psk.isSome) _)
    intro yes
    cases yes with
    | false=>exact preserves_pure _
    | true=>exact psk_entry cs loans paid.slot (psk.getD [])
  · intro _
    apply preserves_bind
    · index_unfold _private.Leanux.Proofs.WG.Queues.HolderConfigUpdate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate.endpointStep
      unfold WG.andM
      simp (config:={zeta:=false}) only [branch,invariant]
      repeat' first
        | (rx_retention_head setPeerEndpoint; exact endpoint_entry _ _ _ _)
        | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
        | rx_retention_step
    · intro _
      index_unfold _private.Leanux.Proofs.WG.Queues.HolderConfigUpdate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate.replaceStep
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)) _)
      intro yes
      cases yes with
      | false=>exact preserves_pure _
      | true=>exact removeByPeer_entry cs loans paid.slot

/-- Actual selected peer update, with its branch-specific remove/out ordering.
The selected loan and base-list membership come from the preceding lookup or
creation cut; no successful leaf result is supplied. -/
theorem update_entry (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (paid : Owner) (flags : UInt32) (psk : Option Key) :
    Ensures (peerConfigUpdateSource attrs (some paid.slot) flags psk paid.slot)
      (fun w=>Entry cs (paid::loans) w ∧ paid.slot∈BaseCoherence.slots w)
      (fun _=>Entry cs loans) := by
  intro w a result v b pre run
  by_cases remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=true
  · exact (removeMe cs loans paid attrs flags psk remove w a result v b pre run).2
  · have no : (flags &&& WGPEER_F_REMOVE_ME != 0)=false := Bool.eq_false_iff.mpr remove
    rw [HolderConfigUpdate.update_factor] at run
    simp only [no] at run
    change ((HolderConfigUpdate.updateTail attrs paid flags psk).run w).run
      (CounterWindow.record a .peerRemoveMe false)=.ok ((result,v),b) at run
    have tail : Hoare (HolderConfigUpdate.updateTail attrs paid flags psk)
        (Entry cs (paid::loans)) (fun _=>Entry cs loans) := by
      rw [HolderConfigUpdate.tail_factor]
      exact hoare_bind _ _ (updatePrefix_entry cs (paid::loans) attrs paid flags psk)
        (fun _=>tail_entry cs loans paid attrs)
    exact (hoare_iff_run_ambient _ _ _).mp tail w _ result v b pre.1 run

end Leanux.Proofs.WG.Index.ConfigurationIndex
