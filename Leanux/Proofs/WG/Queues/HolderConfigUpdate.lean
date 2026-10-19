import Leanux.Proofs.WG.Queues.HolderConfigTail
import Leanux.Proofs.WG.Queues.BaseLookupRemoval

/-! The original acquired-peer update retains actual configuration changes,
base removal, and its final caller-reference payment. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

theorem removeByPeer_fields (pid : PeerId) : SameView HolderEncrypt.fields (removeByPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have base := (ProjectedAction.iff_run_ambient _ _ _).mp (BaseRemoval.removeByPeer_view pid) w a result v b run
  have other := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderBaseRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.removeByPeer_other) pid)
    w a result v b run
  change (sendView v,(passiveView v).2,handoffTxView v) = (sendView w,(passiveView w).2,handoffTxView w) at other
  change (DecryptCarrier.decryptView v,passiveView v,sendView v,handoffTxView v) =
    (DecryptCarrier.decryptView w,passiveView w,sendView w,handoffTxView w)
  have first : DecryptCarrier.decryptView v = DecryptCarrier.decryptView w := congrArg Prod.fst base
  have list : (passiveView v).1=(passiveView w).1 := congrArg (fun s => s.2.getD []) base
  have send := congrArg (fun s => s.1) other
  have passive := congrArg (fun s => s.2.1) other
  have tx := congrArg (fun s => s.2.2) other
  exact Prod.ext first (Prod.ext (Prod.ext list passive) (Prod.ext send tx))

theorem removeByPeer_boundary (pid : PeerId) : Preserves (Boundary cs loans) (removeByPeer pid) :=
  HolderEncrypt.native_boundary (removeByPeer_fields pid)

theorem dstReset_boundary (pid : PeerId) : Preserves (Boundary cs loans) (dstCacheReset pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.frame_boundary) _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.dstCacheReset_frame) pid)
    (fun _ _ => (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.control_keeps)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.dstCacheReset_view) pid))

theorem endpoint_boundary (pid : PeerId) (endpoint : Endpoint) :
    Preserves (Boundary cs loans) (setPeerEndpoint pid endpoint) := by
  have write : Preserves (Boundary cs loans) (do
      setPeer pid {(←getPeer pid) with endpoint:=some endpoint}
      dstCacheReset pid) := by
    simpa only [bind_assoc] using preserves_bind
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_boundary)
        pid (fun p => {p with endpoint:=some endpoint})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ _ h => h) (fun _ => rfl)) (fun _ => dstReset_boundary pid)
  have record (d : Decision) (b : Bool) : Preserves (Boundary cs loans) (branch d b : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch d b) _
  unfold setPeerEndpoint
  simp only [requireNotPending,pure_bind]
  apply preserves_bind ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceive.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive.read) pid)
  intro p
  apply preserves_bind (HolderEncrypt.native_boundary (HolderEncrypt.store_fields (endpointEq_sameStore endpoint p.endpoint)))
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
    Preserves (Boundary cs loans) (pskStep o psk) := by
  unfold pskStep
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSetPsk psk.isSome) _)
  intro yes
  cases yes with
  | false => exact preserves_pure _
  | true =>
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_boundary)
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
    Preserves (Boundary cs loans) (endpointStep a o) := by
  unfold endpointStep WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact endpoint_boundary _ _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

private def replaceStep (o : Owner) (flags : UInt32) : WG.M Unit := do
  if ← branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) then removeByPeer o.slot

private theorem replace_boundary (o : Owner) (flags : UInt32) :
    Preserves (Boundary cs loans) (replaceStep o flags) := by
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
    Preserves (Boundary cs loans) (updatePrefix a o flags psk) := by
  rw [prefix_factor]
  exact preserves_bind (psk_boundary o psk) (fun _ =>
    preserves_bind (endpointStep_boundary a o) (fun _ => replace_boundary o flags))

theorem updateTail_paid (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key) :
    Hoare (updateTail a o flags psk) (Boundary cs (o::loans)) (fun _ => Boundary cs loans) := by
  rw [tail_factor]
  exact hoare_bind _ _ (prefix_boundary a o flags psk) (fun _ => HolderConfigTail.tail a o)

/-- Actual acquired-peer update: its removal branch pays the base occurrence
as well as the caller loan; ordinary updates retain their concrete work delta. -/
theorem update_paid (a : PeerAttrs) (o : Owner) (flags : UInt32) (psk : Option Key)
    (hi : Boundary cs (o::loans) w) (coherent : BaseCoherence.Inv w)
    (member : o.slot ∈ BaseCoherence.slots w) (ambient final : Ambient)
    (run : ((Configuration.peerConfigUpdateSource a (some o.slot) flags psk o.slot).run w).run ambient =
      .ok ((result,v),final)) : Boundary cs loans v := by
  by_cases remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=true
  · obtain ⟨holders,funded,stable⟩ := hi
    have selected : o.slot ∈ holders.base.map Owner.slot := by rw [funded.aligned.base]; exact member
    have post := BaseLookupRemoval.update_remove a flags psk o funded stable
      (BaseCoherence.holder_unique coherent funded.aligned) selected remove ambient final run
    obtain ⟨after,_,funded,stable⟩ := post.2
    exact ⟨after,funded,stable⟩
  · have no : (flags &&& WGPEER_F_REMOVE_ME != 0)=false := Bool.eq_false_iff.mpr remove
    rw [update_factor] at run
    simp only [no] at run
    change ((updateTail a o flags psk).run w).run
      (CounterWindow.record ambient .peerRemoveMe false)=.ok ((result,v),final) at run
    exact (hoare_iff_run_ambient _ _ _).mp (updateTail_paid a o flags psk) w _ result v final hi run

/-- The actual successful lookup supplies the caller loan and structural
selection needed by either update arm, without an intermediate funding premise. -/
theorem lookup_update (key : Key) (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    {holders : DurableHolders} (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (ambient middle final : Ambient)
    (lookup : ((pubkeyLookup key).run w).run ambient = .ok ((some pid,u),middle))
    (run : ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run middle =
      .ok ((result,v),final)) : Boundary cs loans v := by
  obtain ⟨o,slot,funded,stable,coherent,_,member⟩ :=
    BaseLookupRemoval.lookup_selected key hi stable coherent configured ambient middle lookup
  subst pid
  exact update_paid attrs o flags psk ⟨holders,funded,stable⟩ coherent
    (by unfold BaseCoherence.slots; rw [←funded.aligned.base]; exact member) middle final run

end Leanux.Proofs.WG.Queues.RxCredits.HolderConfigUpdate
