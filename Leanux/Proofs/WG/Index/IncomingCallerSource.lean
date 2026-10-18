import Leanux.Proofs.WG.Index.IncomingCallerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders
namespace Incoming

theorem cut_bounds {cs : Ledger} {loans : Reservations} {w : WGWorld}
    (cut : Cut cs loans w) (ambient : Ambient) :
    InitializedBounds.EndpointSafe (Campaign2.snapshot w ambient) := by
  obtain ⟨history,allocation⟩ := cut.1
  intro d device
  change w.dev=some d at device
  exact ⟨cut.2.1.2.2 (Affiliation.state d) (by simp [Affiliation.view,device]),
    allocation.peerSlots d device,allocation.keySlots d device⟩

/-- Use the existing concrete observer of the same native call. Its actual
returned journal supplies the allocation fact, including refusal results. -/
theorem allocation_normal {α : Type} (action : WG.M α) (observed : MixedM α)
    (erases : ErasesStatePrefix observed action)
    (preserves : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe observed)
    (history : List LifetimeEvent) (w v : WGWorld) (ambient after : Ambient) (result : α)
    (entry : AllocationInv history w)
    (run : (action.run w).run ambient = .ok ((result,v),after)) :
    AllocationInv (runStatePrefix observed w ambient history).2 v := by
  have erased := (erases w ambient history).trans run
  have post := (preserves w ambient history entry).choose_spec.2.2
  change (runPrefix (observed.run w) ambient history).1 = .ok ((result,v),after) at erased
  rw [erased] at post
  exact post

theorem handshake_allocated (call : HandshakeCall) :
    Ensures call.original (fun w => ∃ history,AllocationInv history w)
      (fun _ w => ∃ history,AllocationInv history w) := by
  intro w a result v b pre run
  obtain ⟨history,allocation⟩ := pre
  exact ⟨_,allocation_normal call.original call.observed call.erases call.allocation
    history w v a b result allocation run⟩

theorem cut_of_aux {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w : World}
    (entry : Reached.Aux initial loans before history w) :
    ∃ suffix, history=before++suffix ∧
      Cut (remaining initial (NapiCarrier.removedPackets suffix)) loans w.wg := by
  obtain ⟨suffix,holders,eq,funded,stable⟩ := Reached.aux_funded entry
  exact ⟨suffix,eq,⟨_,entry.1.2.1.allocation⟩,
    ⟨⟨holders,funded,stable⟩,HandshakeEntry.of_owner entry.1.2.1 entry.1.2.2⟩,
    entry.2⟩

theorem consumeInitiation_cut (cs : Ledger) (loans : Reservations) (msg : List UInt8) :
    Ensures (consumeInitiation msg) (Cut cs loans) (Selected cs loans) := by
  intro w a result v b pre run
  obtain ⟨holders,funded,stable⟩ := pre.2.1.1
  have acquired := HandshakeEntry.initiation_funded msg funded stable pre.2.1.2 a b run
  have allocation := handshake_allocated (.consumeInitiation msg) w a result v b pre.1 run
  have base := BaseCoherence.transport pre.2.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.consumeInitiation_view msg)
      w a result v b run)
  have core := consumeInitiation_indexCore msg w a result v b pre.2.2.2 run
  cases result with
  | none => exact ⟨allocation,⟨⟨holders,acquired.1⟩,acquired.2⟩,base,core⟩
  | some pid =>
    obtain ⟨paid,slot,account,stable⟩ := acquired.1
    exact ⟨paid,slot,allocation,⟨⟨holders,account,stable⟩,acquired.2⟩,base,core⟩

theorem consumeResponse_cut (cs : Ledger) (loans : Reservations) (msg : List UInt8) :
    Ensures (consumeResponse msg) (Cut cs loans) (Selected cs loans) := by
  intro w a result v b pre run
  obtain ⟨holders,funded,stable⟩ := pre.2.1.1
  have acquired := HandshakeEntry.response_funded msg funded stable pre.2.1.2 a b run
  have allocation := handshake_allocated (.consumeResponse msg) w a result v b pre.1 run
  have base := BaseCoherence.transport pre.2.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.consumeResponse_view msg)
      w a result v b run)
  have core := consumeResponse_indexCore msg w a result v b pre.2.2.2 run
  cases result with
  | none => exact ⟨allocation,⟨⟨holders,acquired.1⟩,acquired.2⟩,base,core⟩
  | some pid =>
    obtain ⟨paid,slot,account,stable⟩ := acquired.1
    exact ⟨paid,slot,allocation,⟨⟨holders,account,stable⟩,acquired.2⟩,base,core⟩

theorem allocated {α : Type} (action : WG.M α) (observed : MixedM α)
    (erases : ErasesStatePrefix observed action)
    (preserves : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe observed) :
    Ensures action (fun w => ∃ h,AllocationInv h w) (fun _ w => ∃ h,AllocationInv h w) := by
  intro w a result v b pre run
  obtain ⟨history,entry⟩ := pre
  exact ⟨_,allocation_normal action observed erases preserves history w v a b result entry run⟩

theorem cut_join {α : Type} (cs : Ledger) (loans : Reservations) (action : WG.M α)
    (observed : MixedM α) (erases : ErasesStatePrefix observed action)
    (allocation : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe observed)
    (account : Preserves (HandshakeResponse.Input cs loans) action)
    (base : SameView BaseCoherence.view action)
    (core : Ensures action (Cut cs loans) (fun _ => Reached.Core)) :
    Ensures action (Cut cs loans) (fun _ => Cut cs loans) := by
  intro w a result v b pre run
  exact ⟨allocated action observed erases allocation w a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp account w a result v b pre.2.1 run,
    BaseCoherence.transport pre.2.2.1 ((ProjectedAction.iff_run_ambient _ _ _).mp base w a result v b run),
    core w a result v b pre run⟩

theorem response_cut (cs : Ledger) (paid : Owner) (loans : Reservations) :
    Ensures (sendHandshakeResponse paid.slot) (Cut cs (paid::loans)) (fun _ => Cut cs (paid::loans)) := by
  intro w a result v b pre run
  have native := Reached.response_native cs paid loans w v a b result pre.2.1
    (cut_bounds pre a) pre.2.2.1 pre.2.2.2 run
  exact ⟨allocated _ (HandshakeSendCall.response paid.slot).observed
    (HandshakeSendCall.response paid.slot).erases (HandshakeSendCall.response paid.slot).allocation
    w a result v b pre.1 run,native⟩

theorem endpoint_cut (cs : Ledger) (loans : Reservations) (pid : PeerId) (src : SkbSource) :
    Ensures (setPeerEndpointFromSkb pid src) (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans _ (HandshakeReceiveCall.endpoint pid src).observed
    (HandshakeReceiveCall.endpoint pid src).erases (HandshakeReceiveCall.endpoint pid src).allocation
    (HandshakeResponse.endpoint pid src)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceHandshake.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.endpointFromSkb_structure) pid src)
  intro w a result v b pre run
  exact core_sender _ (endpointFromSkb_sender pid src)
    ((ensures_iff _ _ _).mpr (setPeerEndpointFromSkb_tables pid src))
    w a result v b pre.2.2.2 run

theorem session_cut (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Ensures (beginSession pid) (Cut cs loans) (fun _ => Cut cs loans) := by
  have account : Preserves (HandshakeResponse.Input cs loans) (beginSession pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    exact ⟨(hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.session) pid)
      w a result v b pre run,
      (hoare_iff_run_ambient _ _ _).mp (HandshakeReceiveSlots.session pid) w a result v b pre.2 run⟩
  apply cut_join cs loans _ (beginSessionPrefix pid)
    (beginSessionPrefix_erases pid) (beginSessionPrefix_allocation pid)
    account (BaseCoherence.beginSession_view pid)
  intro w a result v b pre run
  exact Reached.session_core pid w a result v b ⟨cut_bounds pre a,pre.2.2.2⟩ run

theorem keepalive_cut (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Ensures (sendKeepalive pid) (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans _ (TxStagingCall.keepalive pid).observed
    (TxStagingCall.keepalive pid).erases (TxStagingCall.keepalive pid).allocation
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join) _
      (HolderTimers.keepalive_boundary pid)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive) pid))
    (BaseCoherence.keepalive_view pid)
  intro w a result v b pre run
  exact StagingRich.keepalive_core pid w a result v b ⟨pre.2.1.2.2,pre.2.2.2⟩ run

theorem derived_cut (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Ensures (timersSessionDerived pid) (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans _ (HandshakeSendCall.sessionDerived pid).observed
    (HandshakeSendCall.sessionDerived pid).erases (HandshakeSendCall.sessionDerived pid).allocation
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join) _
      (HandshakeReceive.sessionDerived pid)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.derived) pid))
    ((BaseCoherence.modTimer_view .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).map (fun _ => ()))
  intro w a result v b pre run
  exact core_sender _ (sender_derived pid)
    ((ensures_iff _ _ _).mpr (timersSessionDerived_tables pid)) w a result v b pre.2.2.2 run

theorem traversal_cut (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Ensures (timersTraversal pid) (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans _ (MaintenanceCall.traversal pid).observed
    (MaintenanceCall.traversal pid).erases (MaintenanceCall.traversal pid).allocation
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join) _
      (HandshakeReceive.traversal pid)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.traversal) pid))
    (BaseCoherence.traversal_view pid)
  intro w a result v b pre run
  exact core_sender _ (sender_traversal pid)
    ((ensures_iff _ _ _).mpr (traversal_tables pid)) w a result v b pre.2.2.2 run

theorem handshakeComplete_cut (cs : Ledger) (loans : Reservations) (pid : PeerId) (site : HiddenSite) :
    Ensures (timersHandshakeComplete pid site) (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans _ (MaintenanceCall.handshakeComplete pid site).observed
    (MaintenanceCall.handshakeComplete pid site).erases (MaintenanceCall.handshakeComplete pid site).allocation
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join) _
      (HandshakeReceive.handshakeComplete pid site)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.complete) pid site))
    (BaseCoherence.handshakeComplete_view pid site)
  intro w a result v b pre run
  exact core_sender _ (handshakeComplete_sender pid site)
    ((ensures_iff _ _ _).mpr (timersHandshakeComplete_tables pid site)) w a result v b pre.2.2.2 run

theorem received_cut (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Ensures (timersAnyAuthenticatedPacketReceived pid) (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans _ (MaintenanceCall.authenticatedReceived pid).observed
    (MaintenanceCall.authenticatedReceived pid).erases (MaintenanceCall.authenticatedReceived pid).allocation
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join) _
      (HolderTimers.delTimer_boundary pid .newHandshake)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.received) pid))
    (BaseCoherence.delTimer_view pid .newHandshake)
  intro w a result v b pre run
  exact core_sender _ (sender_delTimer pid .newHandshake)
    ((ensures_iff _ _ _).mpr (timersAnyAuthenticatedPacketReceived_tables pid)) w a result v b pre.2.2.2 run

theorem responseSession_cut (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Ensures (HandshakeReceive.responseSession pid) (Cut cs loans) (fun _ => Cut cs loans) := by
  unfold HandshakeReceive.responseSession
  refine ensures_bind _ _ (session_cut cs loans pid) ?_
  intro begun
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .hsRespSessionBegun begun) (Cut cs loans))) ?_
  intro active
  cases active with
  | false => intro w a result v b pre run; cases run; exact pre
  | true =>
    refine ensures_bind _ _ (derived_cut cs loans pid) ?_
    intro _
    exact ensures_bind _ _ (handshakeComplete_cut cs loans pid _) (fun _ => keepalive_cut cs loans pid)

theorem initiation_some (cs : Ledger) (paid : Owner) (loans : Reservations) (src : SkbSource) :
    Ensures (HandshakeInitiation.afterLookup (some paid.slot) src) (Cut cs (paid::loans))
      (fun peer w => peer=some paid.slot ∧ Cut cs (paid::loans) w) := by
  have inner : Ensures (do
      setPeerEndpointFromSkb paid.slot src
      sendHandshakeResponse paid.slot
      pure (some paid.slot) : WG.M (Option PeerId)) (Cut cs (paid::loans))
      (fun peer w => peer=some paid.slot ∧ Cut cs (paid::loans) w) := by
    refine ensures_bind _ _ (endpoint_cut cs (paid::loans) paid.slot src) ?_
    intro _
    refine ensures_bind _ _ (response_cut cs paid loans) ?_
    intro _
    intro w a result v b pre run
    cases run
    exact ⟨rfl,pre⟩
  intro w a result v b pre run
  change ((do
      setPeerEndpointFromSkb paid.slot src
      sendHandshakeResponse paid.slot
      pure (some paid.slot) : WG.M (Option PeerId)).run w).run
        (CounterWindow.record a .hsInitNoPeer false)=.ok ((result,v),b) at run
  exact inner w _ result v b pre run

theorem initiation_branch (cs : Ledger) (loans : Reservations) (msg : List UInt8) (src : SkbSource) :
    Ensures (HandshakeInitiation.branchSource msg src) (Cut cs loans) (Selected cs loans) := by
  intro w a result v b pre run
  unfold HandshakeInitiation.branchSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,consume,tail⟩ := run
  have acquired := consumeInitiation_cut cs loans msg w a peer u c pre consume
  cases peer with
  | none =>
    change Except.ok ((none,u),CounterWindow.record c .hsInitNoPeer true)=.ok ((result,v),b) at tail
    cases tail
    exact acquired
  | some pid =>
    obtain ⟨paid,slot,held⟩ := acquired
    subst pid
    have post := initiation_some cs paid loans src u c result v b held tail
    rw [post.1]
    exact ⟨paid,rfl,post.2⟩

theorem response_some (cs : Ledger) (paid : Owner) (loans : Reservations) (src : SkbSource) :
    Ensures (HandshakeResponse.afterLookup (some paid.slot) src) (Cut cs (paid::loans))
      (fun peer w => peer=some paid.slot ∧ Cut cs (paid::loans) w) := by
  have inner : Ensures (do
      setPeerEndpointFromSkb paid.slot src
      HandshakeReceive.responseSession paid.slot
      pure (some paid.slot) : WG.M (Option PeerId)) (Cut cs (paid::loans))
      (fun peer w => peer=some paid.slot ∧ Cut cs (paid::loans) w) := by
    refine ensures_bind _ _ (endpoint_cut cs (paid::loans) paid.slot src) ?_
    intro _
    refine ensures_bind _ _ (responseSession_cut cs (paid::loans) paid.slot) ?_
    intro _
    intro w a result v b pre run
    cases run
    exact ⟨rfl,pre⟩
  intro w a result v b pre run
  change ((do
      setPeerEndpointFromSkb paid.slot src
      HandshakeReceive.responseSession paid.slot
      pure (some paid.slot) : WG.M (Option PeerId)).run w).run
        (CounterWindow.record a .hsRespNoPeer false)=.ok ((result,v),b) at run
  exact inner w _ result v b pre run

theorem response_branch (cs : Ledger) (loans : Reservations) (msg : List UInt8) (src : SkbSource) :
    Ensures (HandshakeResponse.branchSource msg src) (Cut cs loans) (Selected cs loans) := by
  intro w a result v b pre run
  unfold HandshakeResponse.branchSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,consume,tail⟩ := run
  have acquired := consumeResponse_cut cs loans msg w a peer u c pre consume
  cases peer with
  | none =>
    change Except.ok ((none,u),CounterWindow.record c .hsRespNoPeer true)=.ok ((result,v),b) at tail
    cases tail
    exact acquired
  | some pid =>
    obtain ⟨paid,slot,held⟩ := acquired
    subst pid
    have post := response_some cs paid loans src u c result v b held tail
    rw [post.1]
    exact ⟨paid,rfl,post.2⟩

theorem payment_cut (cs : Ledger) (paid : Owner) (loans : Reservations) :
    Ensures (peerPut (some paid.slot)) (Cut cs (paid::loans)) (fun _ => Cut cs loans) := by
  intro w a result v b pre run
  have paidCore := Reached.peerPut_boundary_core cs paid loans w a result v b
    ⟨⟨pre.2.1.1,pre.2.2.1,(HandshakeEntry.entry_facts pre.2.1.2).1⟩,pre.2.2.2⟩ run
  have entry := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.pay) (some paid.slot))
    w a result v b pre.2.1.2 run
  have allocation := allocated _ (peerPutMixed (some paid.slot))
    (peerPutMixed_erases (some paid.slot)) (peerPutMixed_allocation (some paid.slot))
    w a result v b pre.1 run
  exact ⟨allocation,⟨paidCore.1.1,entry⟩,paidCore.1.2.1,paidCore.2⟩

theorem peerStats_cut (cs : Ledger) (loans : Reservations) (pid : PeerId) (len : Nat) :
    Ensures (modifyPeer pid fun p => {p with rxBytes:=p.rxBytes+len})
      (Cut cs loans) (fun _ => Cut cs loans) := by
  let f := fun p : Peer => {p with rxBytes:=p.rxBytes+len}
  apply cut_join cs loans _ (modifyPeerKeysPrefix pid f)
    (modifyPeerKeysPrefix_erases pid f)
    (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient allocationAmbient (fun _ => True) pid f (fun _ => rfl)))
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join) _
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceive.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive.update)
        pid f (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl))
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.update)
        pid f (fun _ => rfl) (fun _ => rfl)))
  · exact ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_read) pid).bind
      (fun p => (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_write) pid (f p))
  · intro w a result v b pre run
    exact core_sender _ (sender_modifyPeer pid f (fun _ => rfl))
      ((ensures_iff _ _ _).mpr (modifyPeer_tables pid f)) w a result v b pre.2.2.2 run

theorem receiveStats_cut (cs : Ledger) (loans : Reservations) (len : Nat) :
    Ensures (modifyDev (rxStatsUpdate len)) (Cut cs loans) (fun _ => Cut cs loans) := by
  have account : Preserves (HandshakeResponse.Input cs loans) (modifyDev (rxStatsUpdate len)) := by
    apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join)
    · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceive.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive.modifyDevice)
      intro w
      unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
      unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
      cases hd : w.dev <;> simp [hd,rxView,rxStatsUpdate]
    · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.modifyDevice)
      all_goals intro d; rfl
  apply cut_join cs loans _ (liftWGPrefix (modifyDev (rxStatsUpdate len)))
    (erasesStatePrefix_lift _) (allocationRx.stats len) account
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_update)
      (rxStatsUpdate len) (fun _ => rfl) (fun _ => rfl))
  intro w a result v b pre run
  have frame : SameView senderFields (modifyDev (rxStatsUpdate len)) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro g c value out e native
    cases native
    simp only [senderFields,Option.map_map,Function.comp_def]
    rfl
  exact core_sender _ frame ((ensures_iff _ _ _).mpr (receiveStats_tables len))
    w a result v b pre.2.2.2 run

theorem finish_cut (cs : Ledger) (paid : Owner) (loans : Reservations) (msg : List UInt8) :
    Ensures (HandshakeReceive.finish (some paid.slot) paid.slot msg)
      (Cut cs (paid::loans)) (fun _ => Cut cs loans) := by
  have updateFactor (f : Peer → Peer) :
      modifyPeer paid.slot f = (do let p ← getPeer paid.slot; setPeer paid.slot (f p)) := rfl
  have statsFactor : rxStatsUpdate msg.length = (fun d : Device =>
      {d with rxPackets:=d.rxPackets+1,rxBytes:=d.rxBytes+msg.length}) := rfl
  have factor : HandshakeReceive.finish (some paid.slot) paid.slot msg = (do
      modifyPeer paid.slot (fun p => {p with rxBytes:=p.rxBytes+msg.length})
      modifyDev (rxStatsUpdate msg.length)
      timersAnyAuthenticatedPacketReceived paid.slot
      timersTraversal paid.slot
      peerPut (some paid.slot)) := by
    simp only [HandshakeReceive.finish,updateFactor,statsFactor,bind_assoc]
  rw [factor]
  refine ensures_bind _ _ (peerStats_cut cs (paid::loans) paid.slot msg.length) ?_
  intro _
  refine ensures_bind _ _ (receiveStats_cut cs (paid::loans) msg.length) ?_
  intro _
  refine ensures_bind _ _ (received_cut cs (paid::loans) paid.slot) ?_
  intro _
  exact ensures_bind _ _ (traversal_cut cs (paid::loans) paid.slot) (fun _ => payment_cut cs paid loans)

theorem finishSelected_cut (cs : Ledger) (loans : Reservations) (peer : Option PeerId) (msg : List UInt8) :
    Ensures (HandshakeReceive.finishSelected peer msg) (Selected cs loans peer) (fun _ => Cut cs loans) := by
  intro w a result v b pre run
  cases peer with
  | none =>
    simp [HandshakeReceive.finishSelected,branch,invariant,AmbientM.invariant] at run
    cases run
  | some pid =>
    obtain ⟨paid,slot,held⟩ := pre
    subst pid
    change ((HandshakeReceive.finish (some paid.slot) paid.slot msg).run w).run
      (CounterWindow.record a .hsWrongPacket false)=.ok ((result,v),b) at run
    exact finish_cut cs paid loans msg w _ result v b held run

theorem complete_cut (cs : Ledger) (loans : Reservations) (peer : Option PeerId) (msg : List UInt8) :
    Ensures (HandshakeArms.complete peer msg) (Selected cs loans peer) (fun _ => Cut cs loans) := by
  cases peer with
  | none => intro w a result v b pre run; cases run; exact pre
  | some pid => exact finishSelected_cut cs loans (some pid) msg

/-- The original initiation arm includes its actual missing-peer return and,
when selected, the shared statistics/timer/payment continuation. -/
theorem initiation_arm (cs : Ledger) (loans : Reservations) (msg : List UInt8) (src : SkbSource) :
    Ensures (HandshakeArms.initiation msg src) (Cut cs loans) (fun _ => Cut cs loans) := by
  rw [HandshakeArms.initiation_factor]
  exact ensures_bind _ _ (initiation_branch cs loans msg src) (fun peer => complete_cut cs loans peer msg)

/-- The original response arm preserves the current index/account cut through
session refusal or creation, keepalive work and the actual selected payment. -/
theorem response_arm (cs : Ledger) (loans : Reservations) (msg : List UInt8) (src : SkbSource) :
    Ensures (HandshakeArms.response msg src) (Cut cs loans) (fun _ => Cut cs loans) := by
  rw [HandshakeArms.response_factor]
  exact ensures_bind _ _ (response_branch cs loans msg src) (fun peer => complete_cut cs loans peer msg)


end Incoming
end Leanux.Proofs.WG.Index
