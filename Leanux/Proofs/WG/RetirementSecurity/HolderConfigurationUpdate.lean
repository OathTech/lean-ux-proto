import Leanux.Proofs.WG.RetirementSecurity.HolderConfigurationTail
import Leanux.Proofs.WG.RetirementSecurity.HolderHandshakePeerFrames
import Leanux.Proofs.WG.RetirementSecurity.HolderRemovalConfiguration

/-! Exact key accounting for the ordinary acquired-peer configuration arm.
The real lookup supplies spare peer credit; no caller-release readiness is
assumed at the eventual out path after allowed-IP edits and TX staging. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open HolderKeepalive HolderConsume
variable {selected : PeerId}

theorem endpoint (pid : PeerId) (e : Endpoint) :
    Preserves (HolderKeepalive.Selected temporary selected) (setPeerEndpoint pid e) := by
  apply join (MaintenanceCall.erases (.endpoint pid e)) (MaintenanceCall.allocation (.endpoint pid e))
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact Prod.ext ((ProjectedAction.iff_run_ambient _ _ _).mp (endpoint_ownership pid e) w a result v b run)
      ((ProjectedAction.iff_run_ambient _ _ _).mp (control_peers (setPeerEndpoint_control pid e)) w a result v b run)
  · exact CurrentSlots.fields_preserves (project:=id)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) pid e)

theorem remove_routes (pid : PeerId) :
    Preserves (HolderKeepalive.Selected temporary selected) (removeByPeer pid) := by
  apply join (AllowedIpsCall.erases (.removePeer pid)) (AllowedIpsCall.allocation (.removePeer pid))
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact Prod.ext ((ProjectedAction.iff_run_ambient _ _ _).mp (removeByPeer_ownership pid) w a result v b run)
      (congrArg (fun s=>s.1.1.1) ((ProjectedAction.iff_run_ambient _ _ _).mp
        (HolderConfigUpdate.removeByPeer_fields pid) w a result v b run))
  · exact CurrentSlots.Removal.removeByPeer_preserves pid

theorem update_then (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (stamp : ∀p,(f p).internalId=p.internalId)
    (fields : ∀p,peerOwnership (f p)=peerOwnership p)
    (slots : ∀p,Affiliation.peerCell (f p)=Affiliation.peerCell p)
    (count : ∀p,(f p).refcount=p.refcount) (rx : ∀p,(f p).rxQueue=p.rxQueue)
    (next : ∀x,Preserves (HolderKeepalive.Selected temporary selected) (tail x)) :
    Preserves (HolderKeepalive.Selected temporary selected)
      (getPeer pid >>= fun p=>setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update_selected pid f stamp fields slots count rx) next

theorem update_prefix (attrs : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key) :
    Preserves (HolderKeepalive.Selected temporary selected) (HolderConfigUpdate.updatePrefix attrs o flags psk) := by
  unfold HolderConfigUpdate.updatePrefix WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (receive_update_head setPeer; apply update_selected <;> intro p <;> rfl)
    | (receive_update_head Bind.bind
       apply update_then
       · intro p; rfl
       · intro p; rfl
       · intro p; rfl
       · intro p; rfl
       · intro p; rfl
       intro x)
    | (rx_retention_head setPeerEndpoint; exact endpoint _ _)
    | (rx_retention_head removeByPeer; exact remove_routes _)
    | (rx_retention_head getPeer; exact getPeer_preserves _ _)
    | (rx_retention_head getDev; exact store getDev_sameWGStore)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rxstack_preserves_join
    | rx_retention_step

theorem ordinary (attrs : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key)
    (remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=false) :
    Hoare (Configuration.peerConfigUpdateSource attrs (some o.slot) flags psk o.slot)
      (HolderKeepalive.Selected temporary o.slot) (fun _=>HolderAccount temporary) := by
  rw [HolderConfigUpdate.update_factor]
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  simp only [remove] at run
  change ((HolderConfigUpdate.updateTail attrs o flags psk).run w).run
    (CounterWindow.record a .peerRemoveMe false)=.ok ((result,v),b) at run
  have keeps : Hoare (HolderConfigUpdate.updateTail attrs o flags psk)
      (HolderKeepalive.Selected temporary o.slot) (fun _=>HolderAccount temporary) := by
    rw [HolderConfigUpdate.tail_factor]
    exact hoare_bind _ _ (update_prefix attrs o flags psk) (fun _=>tail attrs o.slot)
  exact (hoare_iff_run_ambient _ _ _).mp keeps w _ result v b before run

theorem lookup_ordinary (key : Key) (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (before : HolderKeepalive.Ready temporary w)
    (remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=false) (a middle b : Ambient)
    (lookup : ((pubkeyLookup key).run w).run a=.ok ((some pid,u),middle))
    (run : ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run middle=
      .ok ((result,v),b)) : HolderAccount temporary v := by
  have acquired := (hoare_iff_run_ambient _ _ _).mp (HolderConsume.pubkey key) w a (some pid) u middle before.1 lookup
  have allocation := Allocated.native (pubkeyLookupPrefix_erases key)
    (pubkeyLookupPrefix_preserves_ambient allocationAmbient key) before.2.1 a middle lookup
  have slots := (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.Configuration.pubkey_preserves key)
    w a (some pid) u middle before.2.2 lookup
  obtain ⟨d,p,_,_,_,_⟩ := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.pubkeyLookup_borrowed_spec key (wgStoreView w)) w a (some pid) u middle rfl lookup
  exact (hoare_iff_run_ambient _ _ _).mp (ordinary attrs (⟨d.ifindex,pid,p.internalId⟩ : Owner) flags psk remove)
    u middle result v b ⟨⟨acquired.1,allocation,slots⟩,acquired.2 pid rfl⟩ run

/-- Both actual update arms retain key credit. The ordinary arm uses its own
lookup loan; the removal arm uses the actual independently funded base holder
and slot-clear/drain/payment chain. -/
theorem lookup_update (key : Key) (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (before : HolderKeepalive.Ready temporary w) (peers : holders.Funded carriers loans w)
    (stable : StableRx carriers w) (anchors : SlotPeerReferences holders loans w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (a middle b : Ambient)
    (lookup : ((pubkeyLookup key).run w).run a=.ok ((some pid,u),middle))
    (run : ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run middle=
      .ok ((result,v),b)) : HolderAccount temporary v := by
  cases remove : (flags &&& WGPEER_F_REMOVE_ME != 0) with
  | false => exact lookup_ordinary key attrs flags psk before remove a middle b lookup run
  | true => exact (HolderRemoval.lookup_update_remove key attrs flags psk before.1 peers stable anchors
      coherent configured remove a middle b lookup run).2.2.1

end Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
