import Leanux.Proofs.WG.Noise.ReceptionCoverageFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ReceptionCaller
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Origins

theorem record_coverage {α : Type} (entry : TagMap)
    (operation : TagOperation) (wrap : α → TagReturn) (action : WG.M α)
    (mapped : (do let x ← action; pure (wrap x)) = runTagOperation operation) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (record operation wrap action) := by
  unfold record receiptWGObserved
  have captured : StatePrefixEnsures
      (fun h g _ => NativeCoverage entry h g) (fun _ => True) (captureWGRun action)
      (fun r h g _ =>
        TagCoverage entry h (receipt operation wrap r).before.tagAt ∧
        ReceiptValid (receipt operation wrap r) ∧
        (receipt operation wrap r).after.tagAt = responseTagMap g.dev) := by
    apply StatePrefixEnsures.captureWGRun action
    · intro h g ambient prior; trivial
    · intro h g ambient value final after prior run
      refine ⟨prior, ⟨g, ambient, final, after, rfl, rfl, ?_⟩, rfl⟩
      change ((runTagOperation operation).run g).run ambient =
        .ok ((wrap value, final), after)
      rw [← mapped]
      change (((action.run g).run ambient) >>= fun ((x,next),inputs) =>
        Except.ok ((wrap x,next),inputs)) = _
      rw [run]
      rfl
  apply StatePrefixEnsures.bind captured
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ h g _ => NativeCoverage entry h g)
  · apply StatePrefixEnsures.emit (receipt operation wrap r)
    · intro h g ambient prior; trivial
    · intro h g ambient prior
      change TagCoverage entry (h ++ [receipt operation wrap r]) (responseTagMap g.dev)
      rw [← prior.2.2]
      exact prior.1.receipt _ prior.2.1.effect
  · intro u
    exact pure_coverage entry r.value

theorem response_coverage (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (observeResponse pid) := by
  have clock (site : HiddenSite) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (hiddenClock64 site : WG.M Int64)) :=
    lift_coverage_exact entry _ (ResponseCaller.clock_tag_frame site)
  have mac (msg : List UInt8) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (addMacToPacket pid msg)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      addMacToPacket_spec_tagMap_variant pid msg g.dev g ambient result final after rfl run)
  have derived :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (timersSessionDerived pid)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      ResponseSuffix.derived_tag_frame pid g.dev g ambient result final after rfl run)
  have traversal :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (timersTraversal pid)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      ResponseSuffix.traversal_tag_frame pid g.dev g ambient result final after rfl run)
  have sent :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (timersAnyAuthenticatedPacketSent pid)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      ResponseSuffix.delTimer_tag_frame pid .sendKeepalive g.dev g ambient result final after rfl run)
  have send (msg : List UInt8) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (sendBufferToPeer pid msg)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      sendBufferToPeer_spec_tagMap_variant pid msg g.dev g ambient result final after rfl run)
  unfold observeResponse HandshakeSources.responseWith
  dsimp (config := { zeta := false }) only [ops]
  change StatePrefixEnsures (fun h g _ => NativeCoverage entry h g) (fun _ => True) _
    (fun _ h g _ => NativeCoverage entry h g)
  repeat' first
    | (maintenance_head record; exact record_coverage entry _ _ _ rfl)
    | (maintenance_lift_action_head hiddenClock64; exact clock _)
    | (maintenance_lift_action_head Bind.bind; exact peerUpdate_coverage entry _ _ (fun _ => rfl))
    | (maintenance_lift_action_head addMacToPacket; exact mac _)
    | (maintenance_lift_action_head timersSessionDerived; exact derived)
    | (maintenance_lift_action_head timersTraversal; exact traversal)
    | (maintenance_lift_action_head timersAnyAuthenticatedPacketSent; exact sent)
    | (maintenance_lift_action_head sendBufferToPeer; exact send _)
    | (maintenance_lift_action_head branch; exact ambient_coverage entry (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient_coverage entry (AmbientM.invariant _))
    | (maintenance_head Pure.pure; exact pure_coverage entry _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h g _ => NativeCoverage entry h g))
    | maintenance_intro
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction


theorem after_coverage (entry : TagMap) (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (macState : MacState) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (observeAfter msg src loaded macState) := by
  have proceed :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (WG.orM
          (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (macState == .withCookie)))
          (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (macState == .noCookie))))) := by
    apply lift_coverage_exact
    intro g ambient result final after run
    cases loaded <;> cases macState <;> cases run <;> rfl
  have needs :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (WG.andM
          (branch .hsNeedsCookieLoaded loaded) (branch .hsNeedsCookieMac (macState == .noCookie)))) := by
    apply lift_coverage_exact
    intro g ambient result final after run
    cases loaded <;> cases macState <;> cases run <;> rfl
  have cookie :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (sendHandshakeCookie msg src)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      sendHandshakeCookie_spec_tagMap_variant msg src g.dev g ambient result final after rfl run)
  have endpoint (pid : PeerId) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (setPeerEndpointFromSkb pid src)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      ReceptionTagSupport.setPeerEndpointFromSkb_tag_frame pid src g.dev
        g ambient result final after rfl run)
  have derived (pid : PeerId) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (timersSessionDerived pid)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      ResponseSuffix.derived_tag_frame pid g.dev g ambient result final after rfl run)
  have complete (pid : PeerId) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (timersHandshakeComplete pid)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      ReceptionTagSupport.handshakeComplete_tag_frame pid .walltimeLastHandshake g.dev
        g ambient result final after rfl run)
  have keepalive (pid : PeerId) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (sendKeepalive pid)) :=
    lift_coverage_retained entry _ (Index.sendKeepalive_tags_retained pid)
  have received (pid : PeerId) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (timersAnyAuthenticatedPacketReceived pid)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      ResponseSuffix.delTimer_tag_frame pid .newHandshake g.dev
        g ambient result final after rfl run)
  have traversal (pid : PeerId) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (timersTraversal pid)) :=
    lift_coverage_exact entry _ (fun g ambient result final after run =>
      ResponseSuffix.traversal_tag_frame pid g.dev g ambient result final after rfl run)
  have put (peer : Option PeerId) :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (WG.peerPut peer)) :=
    lift_coverage_retained entry _ (fun g ambient result final after run =>
      Index.staging_tags _ (fun entry => Index.staging_peerPut entry peer)
        g ambient result final after run)
  have rxStats :
      StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
        (liftWGPrefix (modifyDev (Lifetimes.rxStatsUpdate msg.length))) := by
    apply lift_coverage_exact
    intro g ambient result final after run
    cases run
    change responseTagMap (g.dev.map (Lifetimes.rxStatsUpdate msg.length)) = responseTagMap g.dev
    cases g.dev <;> rfl
  unfold observeAfter HandshakeSources.afterMacWith
  simp (config := { zeta := false }) only [← observeResponse_eq]
  dsimp (config := { zeta := false }) only [ops]
  change StatePrefixEnsures (fun h g _ => NativeCoverage entry h g) (fun _ => True) _
    (fun _ h g _ => NativeCoverage entry h g)
  repeat' first
    | (maintenance_head observeResponse; exact response_coverage entry _)
    | (maintenance_head record; exact record_coverage entry _ _ _ rfl)
    | (maintenance_lift_action_head WG.orM; exact proceed)
    | (maintenance_lift_action_head WG.andM; exact needs)
    | (maintenance_lift_action_head sendHandshakeCookie; exact cookie)
    | (maintenance_lift_action_head setPeerEndpointFromSkb; exact endpoint _)
    | (maintenance_lift_action_head timersSessionDerived; exact derived _)
    | (maintenance_lift_action_head timersHandshakeComplete; exact complete _)
    | (maintenance_lift_action_head sendKeepalive; exact keepalive _)
    | (maintenance_lift_action_head timersAnyAuthenticatedPacketReceived; exact received _)
    | (maintenance_lift_action_head timersTraversal; exact traversal _)
    | (maintenance_lift_action_head WG.peerPut; exact put _)
    | (maintenance_lift_action_head modifyDev; exact rxStats)
    | (maintenance_lift_action_head Bind.bind; exact peerUpdate_coverage entry _ _ (fun _ => rfl))
    | (maintenance_lift_action_head branch; exact ambient_coverage entry (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient_coverage entry (AmbientM.invariant _))
    | (maintenance_head Pure.pure; exact pure_coverage entry _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h g _ => NativeCoverage entry h g))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction


theorem afterNative_coverage (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (mac : MacState)
    (g : WGWorld) (ambient : Ambient) (history : List TagReceipt)
    (final : WGWorld) (after : Ambient)
    (run : afterNative msg src loaded mac g ambient = .ok ((history,final),after)) :
    TagCoverage (responseTagMap g.dev) history (responseTagMap final.dev) := by
  cases observed : runWGPrefix (observeAfter msg src loaded mac) g ambient [] with
  | mk result events =>
    cases result with
    | error stop =>
      simp only [afterNative,observed,Except.map] at run
      cases run
    | ok result =>
      obtain ⟨⟨u,current⟩,inputs⟩ := result
      cases u
      simp only [afterNative,observed,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      obtain ⟨suffix,appended,safe,normal⟩ :=
        after_coverage (responseTagMap g.dev) msg src loaded mac g ambient []
          (TagsRetained.refl _)
      have raw := observed
      simp only [runWGPrefix,runStatePrefix] at raw
      simpa only [raw, NativeCoverage] using normal

theorem observeClassified_coverage (msg : List UInt8) (src : SkbSource)
    (g : WGWorld) (ambient : Ambient) (call : ReceptionCall)
    (final : WGWorld) (after : Ambient)
    (run : observeClassified msg src g ambient = .ok ((call,final),after)) :
    TagCoverage (responseTagMap g.dev) call.receipts (responseTagMap final.dev) := by
  let next : Ambient := {ambient with steps := (ambient.steps.push
    {decision := .hsCookie, outcome := messageType msg == MESSAGE_HANDSHAKE_COOKIE,
      netRx := ambient.netRxSection})}
  change ((if messageType msg == MESSAGE_HANDSHAKE_COOKIE then
    (do cookieMessageConsume msg; pure (⟨.cookie,[]⟩ : ReceptionCall))
    else (do let r ← observeGate msg src
             let receipts ← afterNative msg src r.loaded r.mac
             pure (⟨.checked r,receipts⟩ : ReceptionCall))) g next) = _ at run
  by_cases cookie : (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = true
  · simp only [cookie,ite_true] at run
    change (cookieMessageConsume msg g next >>= fun ((_,current),inputs) =>
      Except.ok (((⟨.cookie,[]⟩ : ReceptionCall),current),inputs)) = _ at run
    cases consumed : cookieMessageConsume msg g next with
    | error stop => rw [consumed] at run; cases run
    | ok out =>
      obtain ⟨⟨u,current⟩,inputs⟩ := out
      have frame := ReceptionTagSupport.cookieMessageConsume_tag_frame
        msg g.dev g next u current inputs rfl consumed
      rw [consumed] at run
      cases run
      change TagsRetained (responseTagMap g.dev) (responseTagMap final.dev)
      rw [frame]
      exact TagsRetained.refl _
  · simp only [cookie] at run
    change (observeGate msg src g next >>= fun ((r,current),inputs) =>
      afterNative msg src r.loaded r.mac current inputs >>= fun ((history,last),tail) =>
        Except.ok (((⟨.checked r,history⟩ : ReceptionCall),last),tail)) = _ at run
    cases checked : observeGate msg src g next with
    | error stop => rw [checked] at run; cases run
    | ok out =>
      obtain ⟨⟨r,current⟩,inputs⟩ := out
      simp only [checked,bind,Except.bind] at run
      have frame := (observeGate_tags msg src g next r current inputs checked).2.2
      cases observed : afterNative msg src r.loaded r.mac current inputs with
      | error stop => rw [observed] at run; cases run
      | ok out =>
        obtain ⟨⟨history,last⟩,tail⟩ := out
        rw [observed] at run
        cases run
        have coverage := afterNative_coverage msg src r.loaded r.mac current inputs
          history last tail observed
        simpa only [frame] using coverage

end Leanux.Proofs.WG.Noise.ReceptionCaller
