import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationTail
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRemoval
import Leanux.Proofs.WG.Queues.HolderConfigUpdate

/-! Actual acquired-peer updates retain one exact account through metadata,
allowed-IP replacement, staging and native removal. The final caller payment
is distinct from the base occurrence retired by peerRemove. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders
namespace ConfigurationUpdate

theorem dstReset_boundary (pid : PeerId) : Preserves (ExactBoundary cs loans) (dstCacheReset pid) := by
  unfold dstCacheReset
  simp only [getAmbient,hiddenJiffies]
  repeat' first
    | (receive_update_head setPeer
       apply TimerFrames.modify_boundary
       all_goals first | (intro p; rfl) | (intro p kid h; exact h))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))
    | rx_retention_step

theorem removeByPeer_boundary (pid : PeerId) : Preserves (ExactBoundary cs loans) (removeByPeer pid) :=
  ExactBoundary.native_fields (HolderConfigUpdate.removeByPeer_fields pid)

theorem endpoint_boundary (pid : PeerId) (endpoint : Endpoint) :
    Preserves (ExactBoundary cs loans) (setPeerEndpoint pid endpoint) := by
  have write : Preserves (ExactBoundary cs loans) (do
      setPeer pid {(←getPeer pid) with endpoint:=some endpoint}
      dstCacheReset pid) := by
    simpa only [bind_assoc] using preserves_bind
      (TimerFrames.modify_boundary
        pid (fun p => {p with endpoint:=some endpoint})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ _ h => h) (fun _ => rfl)) (fun _ => dstReset_boundary pid)
  have record (d : Decision) (b : Bool) : Preserves (ExactBoundary cs loans) (branch d b : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch d b) _
  unfold setPeerEndpoint
  simp only [requireNotPending,pure_bind]
  apply preserves_bind (show Preserves (ExactBoundary cs loans) (getPeer pid) from by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b before run
    exact (getPeer_normal pid w v p a b run).1 ▸ before)
  intro p
  apply preserves_bind (ExactBoundary.native_fields (HolderEncrypt.store_fields (endpointEq_sameStore endpoint p.endpoint)))
  intro eq
  apply preserves_bind (record _ _)
  intro same
  cases same with
  | true => exact preserves_pure _
  | false =>
    apply preserves_bind (record _ _)
    intro v4
    cases v4 with
    | true => exact write
    | false =>
      apply preserves_bind (record _ _)
      intro v6
      cases v6 with
      | true => exact write
      | false => exact preserves_pure _

def updateTail (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key) : WG.M Int := do
  if ← branch .peerSetPsk psk.isSome then
    setPeer o.slot {(← getPeer o.slot) with presharedKey:=psk.getD []}
  if ← branch .peerHasEndpoint a.endpoint.isSome then
    let some e := a.endpoint | invariant "unreachable"
    if ← WG.andM (branch .peerEndpointV4Len (e.len==16)) (branch .peerEndpointV4Family (e.family==AF_INET)) then
      setPeerEndpoint o.slot {family:=e.family,addr:=e.addr,port:=e.port}
    else if ← WG.andM (branch .peerEndpointV6Len (e.len==28)) (branch .peerEndpointV6Family (e.family==AF_INET6)) then
      setPeerEndpoint o.slot {family:=e.family,addr:=e.addr,port:=e.port,scope:=e.scope,flowinfo:=e.flowinfo}
  if ← branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) then removeByPeer o.slot
  Configuration.peerConfigTailSource a (some o.slot) o.slot

theorem update_factor (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key) :
    Configuration.peerConfigUpdateSource a (some o.slot) flags psk o.slot = (do
      if ← branch .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0) then
        peerRemove (some o.slot)
        peerPut (some o.slot)
        _ ← branch .peerZeroPsk a.presharedKey.isSome
        pure 0
      else updateTail a o flags psk) := by
  rfl

def updatePrefix (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key) : WG.M Unit := do
  if ← branch .peerSetPsk psk.isSome then
    setPeer o.slot {(← getPeer o.slot) with presharedKey:=psk.getD []}
  if ← branch .peerHasEndpoint a.endpoint.isSome then
    let some e := a.endpoint | invariant "unreachable"
    if ← WG.andM (branch .peerEndpointV4Len (e.len==16)) (branch .peerEndpointV4Family (e.family==AF_INET)) then
      setPeerEndpoint o.slot {family:=e.family,addr:=e.addr,port:=e.port}
    else if ← WG.andM (branch .peerEndpointV6Len (e.len==28)) (branch .peerEndpointV6Family (e.family==AF_INET6)) then
      setPeerEndpoint o.slot {family:=e.family,addr:=e.addr,port:=e.port,scope:=e.scope,flowinfo:=e.flowinfo}
  if ← branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) then removeByPeer o.slot

theorem tail_factor (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key) :
    updateTail a o flags psk = (updatePrefix a o flags psk >>= fun _ => Configuration.peerConfigTailSource a (some o.slot) o.slot) := by
  cases endpoint : a.endpoint <;> simp only [updateTail,updatePrefix,endpoint,bind_assoc,pure_bind,bind_if_source]

private def pskStep (o : Owner) (psk : Option Key) : WG.M Unit := do
  if ← branch .peerSetPsk psk.isSome then
    setPeer o.slot {(← getPeer o.slot) with presharedKey:=psk.getD []}

private theorem psk_boundary (o : Owner) (psk : Option Key) :
    Preserves (ExactBoundary cs loans) (pskStep o psk) := by
  unfold pskStep
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSetPsk psk.isSome) _)
  intro yes
  cases yes with
  | false => exact preserves_pure _
  | true =>
    exact TimerFrames.modify_boundary
      o.slot (fun p => {p with presharedKey:=psk.getD []})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ _ h => h) (fun _ => rfl)

private def endpointStep (a : PeerAttrs) (o : Owner) : WG.M Unit := do
  if ← branch .peerHasEndpoint a.endpoint.isSome then
    let some e := a.endpoint | invariant "unreachable"
    if ← WG.andM (branch .peerEndpointV4Len (e.len==16)) (branch .peerEndpointV4Family (e.family==AF_INET)) then
      setPeerEndpoint o.slot {family:=e.family,addr:=e.addr,port:=e.port}
    else if ← WG.andM (branch .peerEndpointV6Len (e.len==28)) (branch .peerEndpointV6Family (e.family==AF_INET6)) then
      setPeerEndpoint o.slot {family:=e.family,addr:=e.addr,port:=e.port,scope:=e.scope,flowinfo:=e.flowinfo}

private theorem endpointStep_boundary (a : PeerAttrs) (o : Owner) :
    Preserves (ExactBoundary cs loans) (endpointStep a o) := by
  unfold endpointStep WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact endpoint_boundary _ _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

private def replaceStep (o : Owner) (flags : UInt32) : WG.M Unit := do
  if ← branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) then removeByPeer o.slot

private theorem replace_boundary (o : Owner) (flags : UInt32) :
    Preserves (ExactBoundary cs loans) (replaceStep o flags) := by
  unfold replaceStep
  apply preserves_bind (hoare_liftAmbient
    (AmbientM.branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)) _)
  intro yes
  cases yes with
  | false => exact preserves_pure _
  | true => exact removeByPeer_boundary _

private theorem prefix_factor (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key) :
    updatePrefix a o flags psk = (do pskStep o psk; endpointStep a o; replaceStep o flags) := by
  cases endpoint : a.endpoint <;> simp only [updatePrefix,pskStep,endpointStep,replaceStep,endpoint,bind_assoc,pure_bind,bind_if_source]

theorem prefix_boundary (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key) :
    Preserves (ExactBoundary cs loans) (updatePrefix a o flags psk) := by
  rw [prefix_factor]
  exact preserves_bind (psk_boundary o psk) (fun _ =>
    preserves_bind (endpointStep_boundary a o) (fun _ => replace_boundary o flags))

theorem updateTail_paid (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key) :
    Hoare (updateTail a o flags psk) (ExactBoundary cs (o::loans)) (fun _ => ExactBoundary cs loans) := by
  rw [tail_factor]
  exact hoare_bind _ _ (prefix_boundary a o flags psk) (fun _ => ConfigurationTail.tail a o)

/-- Actual acquired-peer update: its removal branch pays the base occurrence
as well as the caller loan; ordinary updates retain their concrete work delta. -/
theorem update_paid (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key)
    (hi : ExactBoundary cs (o::loans) w) (coherent : BaseCoherence.Inv w)
    (member : o.slot ∈ BaseCoherence.slots w) (ambient final : Ambient)
    (run : ((Configuration.peerConfigUpdateSource a (some o.slot) flags psk o.slot).run w).run ambient =
      .ok ((result,v),final)) : ExactBoundary cs loans v := by
  by_cases remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=true
  · obtain ⟨holders,account⟩ := hi
    have selected : o.slot ∈ holders.base.map Owner.slot := by rw [account.funded.aligned.base]; exact member
    simp only [Configuration.peerConfigUpdateSource,remove] at run
    change ((do peerRemove (some o.slot)
                peerPut (some o.slot)
                _ ← branch .peerZeroPsk a.presharedKey.isSome
                pure (0 : Int) : WG.M Int).run w).run
      (CounterWindow.record ambient .peerRemoveMe true)=.ok ((result,v),final) at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨ignored,u,c,removed,tail⟩ := run
    cases ignored
    have ready := Removal.some_peer account o.slot
      (BaseCoherence.holder_unique coherent account.funded.aligned) selected _ c removed
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,d,paid,done⟩ := tail
    cases ignored
    obtain ⟨after,_,account⟩ := Removal.payment ready paid
    change Except.ok ((0,z),CounterWindow.record d .peerZeroPsk a.presharedKey.isSome)=.ok ((result,v),final) at done
    cases done
    exact ⟨after,account⟩
  · have no : (flags &&& WGPEER_F_REMOVE_ME != 0)=false := Bool.eq_false_iff.mpr remove
    rw [update_factor] at run
    simp only [no] at run
    change ((updateTail a o flags psk).run w).run
      (CounterWindow.record ambient .peerRemoveMe false)=.ok ((result,v),final) at run
    exact (hoare_iff_run_ambient _ _ _).mp (updateTail_paid a o flags psk) w _ result v final hi run

end ConfigurationUpdate
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
