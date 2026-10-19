import Leanux.Proofs.WG.Config.ConfiguredCommandFrames
import Leanux.Proofs.WG.Queues.JointPeerCommand
import Leanux.Proofs.WG.AllowedIps.RoutingNoiseReceiveFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

/-- The actual H2 acquisition result and the same cut's routing ownership. -/
def Acquired (cs : Ledger) (loans : Reservations) (peer : Option PeerId)
    (g : WGWorld) : Prop :=
  Index.ConfigurationIndex.Acquired cs loans peer g ∧ Ready g

theorem select_join {α : Type} (cs : Ledger) (loans : Reservations) (pid : PeerId)
    (action : WG.M α)
    (account : Preserves (Index.ConfigurationIndex.Entry cs loans) action)
    (routing : Preserves Ready action)
    (base : SameView BaseCoherence.view action) :
    Preserves (SelectedEntry cs loans pid) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  have same := congrArg Prod.fst ((ProjectedAction.iff_run_ambient _ _ _).mp
    base g a result v b run)
  change BaseCoherence.slots v=BaseCoherence.slots g at same
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp account g a result v b pre.1.1 run,
    (hoare_iff_run_ambient _ _ _).mp routing g a result v b pre.1.2 run⟩,
    same.symm ▸ pre.2⟩

theorem psk_selected (cs : Ledger) (loans : Reservations) (pid : PeerId) (key : Key) :
    Preserves (SelectedEntry cs loans pid)
      (getPeer pid >>= fun p=>setPeer pid {p with presharedKey:=key}) :=
  select_join cs loans pid _ (Index.ConfigurationIndex.psk_entry cs loans pid key)
    (retained_ready _ (ProjectedRetainsRoutingCall.of_same
      (modifyPeer_routing pid (fun p=>{p with presharedKey:=key}) (fun _=>rfl))) (psk_base pid key))
    (psk_base pid key)

theorem endpoint_selected (cs : Ledger) (loans : Reservations) (pid : PeerId) (endpoint : Endpoint) :
    Preserves (SelectedEntry cs loans pid) (setPeerEndpoint pid endpoint) :=
  select_join cs loans pid _ (Index.ConfigurationIndex.endpoint_entry cs loans pid endpoint)
    (retained_ready _ (ProjectedRetainsRoutingCall.of_same (setPeerEndpoint_routing pid endpoint))
      (BaseCoherence.endpoint_view pid endpoint))
    (BaseCoherence.endpoint_view pid endpoint)

theorem replace_selected (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (SelectedEntry cs loans pid) (removeByPeer pid) :=
  select_join cs loans pid _ (Index.ConfigurationIndex.removeByPeer_entry cs loans pid)
    (removeByPeer_ready pid) (BaseCoherence.removeByPeer_view pid)

theorem prefix_selected (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (paid : Owner) (flags : UInt32) (psk : Option Key) :
    Preserves (SelectedEntry cs loans paid.slot)
      (HolderConfigUpdate.updatePrefix attrs paid flags psk) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigUpdate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate.prefix_factor)]
  apply preserves_bind
  · index_unfold _private.Leanux.Proofs.WG.Queues.HolderConfigUpdate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate.pskStep
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSetPsk psk.isSome) _)
    intro yes
    cases yes with
    | false=>exact preserves_pure _
    | true=>exact psk_selected cs loans paid.slot (psk.getD [])
  · intro _
    apply preserves_bind
    · index_unfold _private.Leanux.Proofs.WG.Queues.HolderConfigUpdate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate.endpointStep
      unfold WG.andM
      simp (config:={zeta:=false}) only [branch,invariant]
      repeat' first
        | (rx_retention_head setPeerEndpoint; exact endpoint_selected _ _ _ _)
        | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
        | rx_retention_step
    · intro _
      index_unfold _private.Leanux.Proofs.WG.Queues.HolderConfigUpdate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate.replaceStep
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)) _)
      intro yes
      cases yes with
      | false=>exact preserves_pure _
      | true=>exact replace_selected cs loans paid.slot

theorem remove_ready (peer : Option PeerId) : Preserves Ready (peerRemove peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  obtain ⟨d,device,t4,t6,represented,owners⟩ := pre
  obtain ⟨out,u4,u6,present,next,configured⟩ :=
    peerRemove_configured_run d t4 t6 peer represented owners g a result v b device run
  exact ⟨out,present,u4,u6,next,configured⟩

theorem remove_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Ensures (peerRemove (some pid)) (SelectedEntry cs loans pid) (fun _=>Entry cs loans) := by
  intro g a result v b pre run
  exact ⟨Index.ConfigurationIndex.remove_selected cs loans pid g a result v b
    ⟨pre.1.1,pre.2⟩ run,
    (hoare_iff_run_ambient _ _ _).mp (remove_ready (some pid)) g a result v b pre.1.2 run⟩

/-- The original selected update preserves all configured route owners and
pays its real caller loan, including REMOVE_ME and every normal errno. -/
theorem update_entry (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) (paid : Owner) (flags : UInt32) (psk : Option Key) :
    Ensures (Configuration.peerConfigUpdateSource attrs (some paid.slot) flags psk paid.slot)
      (SelectedEntry cs (paid::loans) paid.slot) (fun _=>Entry cs loans) := by
  intro g a result v b pre run
  by_cases remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=true
  · simp only [Configuration.peerConfigUpdateSource,remove] at run
    change ((do peerRemove (some paid.slot)
                peerPut (some paid.slot)
                _ ← branch .peerZeroPsk attrs.presharedKey.isSome
                pure (0 : Int) : WG.M Int).run g).run
      (CounterWindow.record a .peerRemoveMe true)=.ok ((result,v),b) at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨ignored,u,c,removed,tail⟩ := run
    cases ignored
    have current := remove_entry cs (paid::loans) paid.slot g _ () u c pre removed
    exact (hoare_iff_run_ambient _ _ _).mp (out_entry cs loans paid attrs 0)
      u c result v b current tail
  · have no : (flags &&& WGPEER_F_REMOVE_ME != 0)=false := Bool.eq_false_iff.mpr remove
    rw [HolderConfigUpdate.update_factor] at run
    simp only [no] at run
    change ((HolderConfigUpdate.updateTail attrs paid flags psk).run g).run
      (CounterWindow.record a .peerRemoveMe false)=.ok ((result,v),b) at run
    have tail : Hoare (HolderConfigUpdate.updateTail attrs paid flags psk)
        (SelectedEntry cs (paid::loans) paid.slot) (fun _=>Entry cs loans) := by
      rw [HolderConfigUpdate.tail_factor]
      exact hoare_bind _ _ (prefix_selected cs (paid::loans) attrs paid flags psk)
        (fun _=>tail_entry cs loans paid attrs shape)
    exact (hoare_iff_run_ambient _ _ _).mp tail g _ result v b pre run

theorem lookup_acquired (cs : Ledger) (loans : Reservations) (key : Key) :
    Ensures (pubkeyLookup key) (Entry cs loans) (Acquired cs loans) := by
  intro g a result v b pre run
  exact ⟨Index.ConfigurationIndex.lookup cs loans key g a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp
      (retained_ready _ (ProjectedRetainsRoutingCall.of_same (pubkeyLookup_routing key))
        (BaseCoherence.pubkeyLookup_view key)) g a result v b pre.2 run⟩

theorem update_acquired (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Hoare (Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid)
      (Acquired cs loans (some pid)) (fun _=>Entry cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  obtain ⟨⟨paid,slot,entry,member⟩,ready⟩ := pre
  subst pid
  exact update_entry cs loans attrs shape paid flags psk g a result v b
    ⟨⟨entry,ready⟩,member⟩ run

theorem none_out (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs) (ret : Int) :
    Preserves (Entry cs loans) (do
      peerPut none
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.noneOut_entry cs loans attrs ret) g a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp (out_ready attrs none ret) g a result v b pre.2 run⟩

theorem create_update (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) (key : Key) (psk : Option Key) (flags : UInt32) :
    Preserves (Entry cs loans) (do
      match ← peerCreate key psk with
      | .error code =>
        _ ← branch .peerCreateErr true
        peerPut none
        _ ← branch .peerZeroPsk attrs.presharedKey.isSome
        pure code
      | .ok pid =>
        _ ← branch .peerCreateErr false
        peerGet pid
        Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨created,u,c,creation,tail⟩ := run
  have createdEntry := (create_entry cs loans key psk g a created u c pre creation).1
  cases created with
  | error code =>
    change ((do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure code : WG.M Int).run u).run
      (CounterWindow.record c .peerCreateErr true)=.ok ((result,v),b) at tail
    exact (hoare_iff_run_ambient _ _ _).mp (none_out cs loans attrs code)
      u _ result v b createdEntry tail
  | ok pid =>
    change ((peerGet pid >>= fun _=>Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run
      (CounterWindow.record c .peerCreateErr false)=.ok ((result,v),b) at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,d,acquire,finish⟩ := tail
    cases ignored
    have ready := (hoare_iff_run_ambient _ _ _).mp
      (retained_ready _ (ProjectedRetainsRoutingCall.of_same (peerGet_routing pid))
        (BaseCoherence.peerGet_view pid)) u _ () z d createdEntry.2 acquire
    have acquired := Index.ConfigurationIndex.creation_acquire_entry cs loans key psk
      g u z a c d pid pre.1 creation acquire
    exact (hoare_iff_run_ambient _ _ _).mp (update_acquired cs loans attrs shape flags psk pid)
      z d result v b ⟨acquired,ready⟩ finish

theorem acquired_entry (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) :
    Hoare (peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
      (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (Configuration.peerConfigUpdateSource attrs) key psk flags peer)
      (Acquired cs loans peer) (fun _=>Entry cs loans) := by
  cases peer with
  | some pid =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro g a result v b pre run
    change ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run g).run
      (CounterWindow.record a .peerNotFound false)=.ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp
      (update_acquired cs loans attrs shape flags psk pid) g _ result v b pre run
  | none =>
    change Preserves (Entry cs loans) _
    unfold peerCommandAcquiredWith WG.andM
    simp (config:={zeta:=false}) only [branch,invariant]
    repeat' first
      | contradiction
      | (env_bind_head peerCreate; exact create_update cs loans attrs shape key psk _)
      | (rx_retention_head getDev
         apply (hoare_iff_run_ambient _ _ _).mpr
         intro g a result v b pre run
         obtain ⟨rfl,rfl,_⟩ := DecryptCarrier.getDev_current a b run
         exact pre)
      | (env_bind_head peerPut; exact none_out cs loans attrs _)
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step

/-- Whole original peer command. Selection and creation are derived from the
actual source prefix; only parsed address shape is required of attribute members. -/
theorem command_entry (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) : Preserves (Entry cs loans) (setPeerCmd attrs) := by
  rw [←Configuration.setPeerCmd_source,Configuration.setPeerCmdSource_factor]
  unfold setPeerCmdWith WG.andM
  simp (config:={zeta:=false}) only [branch,invariant]
  repeat' first
    | contradiction
    | (env_bind_head pubkeyLookup
       apply hoare_bind _ _ ((ensures_iff _ _ _).mp (lookup_acquired cs loans _))
       intro peer
       exact acquired_entry cs loans attrs shape _ _ _ peer)
    | (env_bind_head peerPut; exact none_out cs loans attrs _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.Config.OwnerConfiguration
