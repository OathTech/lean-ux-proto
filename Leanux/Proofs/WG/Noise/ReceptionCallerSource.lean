import Leanux.Proofs.WG.Noise.TagSequenceSource
import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.Logged.NativeCapture

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ReceptionCaller
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Origins

abbrev Obs := WGPrefix TagReceipt

def receipt {α : Type} (operation : TagOperation) (wrap : α → TagReturn)
    (r : WGRunWitness α) : TagReceipt :=
  ⟨operation, Campaign2.snapshot r.before r.ambientBefore, wrap r.value,
    Campaign2.snapshot r.after r.ambientAfter⟩

def ReceiptValid (r : TagReceipt) : Prop :=
  ∃ g ambient final after,
    r.before = Campaign2.snapshot g ambient ∧
    r.after = Campaign2.snapshot final after ∧
    ((runTagOperation r.operation).run g).run ambient =
      .ok ((r.result, final), after)

theorem ReceiptValid.effect {r : TagReceipt} (valid : ReceiptValid r) :
    TagReceiptEffect r := by
  obtain ⟨g, ambient, final, after, beforeEq, afterEq, run⟩ := valid
  have effect := runTagOperation_effect r.operation r.before
    g ambient r.result final after beforeEq.symm run
  simpa only [← afterEq] using effect

def record {α : Type} (operation : TagOperation) (wrap : α → TagReturn)
    (a : WG.M α) : Obs α :=
  receiptWGObserved (liftWGPrefix a) (receipt operation wrap)

def ops : HandshakeSources.Ops Obs where
  step := liftWGPrefix
  session := fun pid => record (.beginSession pid) .begun (beginSession pid)
  modifyPeer := fun pid f => liftWGPrefix (do setPeer pid (f (← getPeer pid)))
  create := fun pid => record (.createResponse pid) .created (createResponse pid)
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  derived := fun pid => liftWGPrefix (timersSessionDerived pid)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := fun msg => record (.consumeInitiation msg) .consumed (consumeInitiation msg)
  response := fun msg => record (.consumeResponse msg) .consumed (consumeResponse msg)
  endpoint := fun pid src => liftWGPrefix (setPeerEndpointFromSkb pid src)
  complete := fun pid => liftWGPrefix (timersHandshakeComplete pid)
  keepalive := fun pid => liftWGPrefix (sendKeepalive pid)
  received := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketReceived pid)
  put := fun pid => liftWGPrefix (WG.peerPut pid)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)

def observeResponse (pid : PeerId) : Obs Unit := HandshakeSources.responseWith ops pid
def observeAfter (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) : Obs Unit :=
  HandshakeSources.afterMacWith ops msg src loaded mac
theorem observeResponse_eq (pid : PeerId) :
    observeResponse pid = HandshakeSources.responseWith ops pid := rfl
theorem observeAfter_eq (msg src loaded mac) :
    observeAfter msg src loaded mac = HandshakeSources.afterMacWith ops msg src loaded mac := rfl

def observe (msg : List UInt8) (src : SkbSource) : Obs Unit :=
  HandshakeSources.receptionWith ops msg src

theorem response_erases (pid : PeerId) :
    ErasesStatePrefix (observeResponse pid) (sendHandshakeResponse pid) := by
  rw [← HandshakeSources.response_original]
  unfold observeResponse HandshakeSources.responseWith
  dsimp (config := { zeta := false }) only [ops, HandshakeSources.original, record]
  repeat' first
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head receiptWGObserved; exact receiptWGObserved_erases (erasesStatePrefix_lift _) _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
    | maintenance_intro
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | contradiction
    | rfl

theorem afterMac_erases (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    ErasesStatePrefix (observeAfter msg src loaded mac)
      (Cookies.afterMac msg src loaded mac) := by
  rw [← HandshakeSources.afterMac_original]
  unfold observeAfter HandshakeSources.afterMacWith
  simp (config := { zeta := false }) only [← observeResponse_eq, HandshakeSources.response_original]
  dsimp (config := { zeta := false }) only [ops, HandshakeSources.original, record]
  repeat' first
    | (maintenance_head observeResponse; exact response_erases _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head receiptWGObserved; exact receiptWGObserved_erases (erasesStatePrefix_lift _) _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
    | maintenance_intro
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | contradiction
    | rfl

theorem observe_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (observe msg src) (receiveHandshakePacket msg src) := by
  rw [← HandshakeSources.reception_original]
  unfold observe HandshakeSources.receptionWith
  simp (config := { zeta := false }) only [← observeAfter_eq, HandshakeSources.afterMac_original]
  dsimp (config := { zeta := false }) only [ops, HandshakeSources.original, record]
  repeat' first
    | (maintenance_head observeAfter; exact afterMac_erases _ _ _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head receiptWGObserved; exact receiptWGObserved_erases (erasesStatePrefix_lift _) _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
    | maintenance_intro
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | contradiction
    | rfl

def ValidHistory (h : List TagReceipt) := ∀ r ∈ h, ReceiptValid r

theorem record_valid {α : Type} (operation : TagOperation) (wrap : α → TagReturn)
    (a : WG.M α)
    (mapped : (do let x ← a; pure (wrap x)) = runTagOperation operation) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory
      (record operation wrap a) := by
  unfold record receiptWGObserved
  have captured : StatePrefixEnsures (fun h _ _ => ValidHistory h) ValidHistory
      (captureWGRun a)
      (fun r h _ _ => ValidHistory h ∧ ReceiptValid (receipt operation wrap r)) := by
    apply StatePrefixEnsures.captureWGRun a
    · intro h g ambient prior
      exact prior
    · intro h g ambient x final after prior run
      refine ⟨prior, g, ambient, final, after, rfl, rfl, ?_⟩
      change ((runTagOperation operation).run g).run ambient =
        .ok ((wrap x, final), after)
      rw [← mapped]
      change (((a.run g).run ambient) >>= fun ((x,next),inputs) =>
        Except.ok ((wrap x,next),inputs)) = _
      rw [run]
      rfl
  apply StatePrefixEnsures.bind captured
  intro r
  have append : ∀ h, ValidHistory h ∧ ReceiptValid (receipt operation wrap r) →
      ValidHistory (h ++ [receipt operation wrap r]) := by
    intro h prior e member
    rcases List.mem_append.mp member with member | member
    · exact prior.1 e member
    · have same : e = receipt operation wrap r := by simpa using member
      subst e
      exact prior.2
  apply StatePrefixEnsures.bind (Q := fun _ h _ _ => ValidHistory h)
  · exact StatePrefixEnsures.emit _ (fun h _ _ prior => append h prior)
      (fun h _ _ prior => append h prior)
  · intro u
    exact StatePrefixEnsures.pure _ (fun _ _ _ prior => prior)
      (fun _ _ _ prior => prior)

theorem response_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (observeResponse pid) := by
  have lifted {α : Type} (a : WG.M α) :
      StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (liftWGPrefix a) :=
    StatePrefixEnsures.lift a (fun _ _ _ prior => prior)
      (fun _ _ _ _ _ _ prior _ => prior)
  have pureValid {α : Type} (x : α) :
      StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (pure x : Obs α) :=
    StatePrefixEnsures.pure x (fun _ _ _ prior => prior) (fun _ _ _ prior => prior)
  unfold observeResponse HandshakeSources.responseWith
  dsimp (config := { zeta := false }) only [ops]
  change StatePrefixEnsures (fun h _ _ => ValidHistory h) ValidHistory _
    (fun _ h _ _ => ValidHistory h)
  repeat' first
    | (maintenance_head record; exact record_valid _ _ _ rfl)
    | (maintenance_head liftWGPrefix; exact lifted _)
    | (maintenance_head Pure.pure; exact pureValid _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h _ _ => ValidHistory h))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction

theorem afterMac_valid (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (observeAfter msg src loaded mac) := by
  have lifted {α : Type} (a : WG.M α) :
      StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (liftWGPrefix a) :=
    StatePrefixEnsures.lift a (fun _ _ _ prior => prior)
      (fun _ _ _ _ _ _ prior _ => prior)
  have pureValid {α : Type} (x : α) :
      StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (pure x : Obs α) :=
    StatePrefixEnsures.pure x (fun _ _ _ prior => prior) (fun _ _ _ prior => prior)
  unfold observeAfter HandshakeSources.afterMacWith
  simp (config := { zeta := false }) only [← observeResponse_eq]
  dsimp (config := { zeta := false }) only [ops]
  change StatePrefixEnsures (fun h _ _ => ValidHistory h) ValidHistory _
    (fun _ h _ _ => ValidHistory h)
  repeat' first
    | (maintenance_head observeResponse; exact response_valid _)
    | (maintenance_head record; exact record_valid _ _ _ rfl)
    | (maintenance_head liftWGPrefix; exact lifted _)
    | (maintenance_head Pure.pure; exact pureValid _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h _ _ => ValidHistory h))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction

theorem observe_valid (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (observe msg src) := by
  have lifted {α : Type} (a : WG.M α) :
      StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (liftWGPrefix a) :=
    StatePrefixEnsures.lift a (fun _ _ _ prior => prior)
      (fun _ _ _ _ _ _ prior _ => prior)
  have pureValid {α : Type} (x : α) :
      StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (pure x : Obs α) :=
    StatePrefixEnsures.pure x (fun _ _ _ prior => prior) (fun _ _ _ prior => prior)
  unfold observe HandshakeSources.receptionWith
  simp (config := { zeta := false }) only [← observeAfter_eq]
  dsimp (config := { zeta := false }) only [ops]
  change StatePrefixEnsures (fun h _ _ => ValidHistory h) ValidHistory _
    (fun _ h _ _ => ValidHistory h)
  repeat' first
    | (maintenance_head observeAfter; exact afterMac_valid _ _ _ _)
    | (maintenance_head record; exact record_valid _ _ _ rfl)
    | (maintenance_head liftWGPrefix; exact lifted _)
    | (maintenance_head Pure.pure; exact pureValid _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h _ _ => ValidHistory h))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction

def ResponseShape (pid : PeerId) (h : List TagReceipt) : Prop :=
  (∃ cr, h = [cr] ∧ cr.operation = .createResponse pid ∧ cr.result = .created none) ∨
  (∃ cr se msg ok, h = [cr,se] ∧ cr.operation = .createResponse pid ∧
    cr.result = .created (some msg) ∧ se.operation = .beginSession pid ∧ se.result = .begun ok)

theorem lift_history {α : Type} (a : WG.M α) (P : List TagReceipt → Prop) :
    StatePrefixPreserves (fun h _ _ => P h) (fun _ => True) (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ prior _ => prior)

theorem record_then {α β : Type} (operation : TagOperation) (wrap : α → TagReturn)
    (a : WG.M α) (initial : List TagReceipt) (next : α → Obs β)
    (Q : β → List TagReceipt → WGWorld → Ambient → Prop)
    (rest : ∀ value r, r.operation = operation → r.result = wrap value →
      StatePrefixEnsures (fun h _ _ => h = initial ++ [r]) (fun _ => True) (next value) Q) :
    StatePrefixEnsures (fun h _ _ => h = initial) (fun _ => True)
      (record operation wrap a >>= next) Q := by
  unfold record receiptWGObserved
  rw [bind_assoc]
  apply StatePrefixEnsures.bind (Q := fun _ h _ _ => h = initial)
  · apply StatePrefixEnsures.captureWGRun a
    · intro h g ambient prior
      trivial
    · intro h g ambient value final after prior run
      exact prior
  intro r
  rw [bind_assoc]
  apply StatePrefixEnsures.bind
    (Q := fun _ h _ _ => h = initial ++ [receipt operation wrap r])
  · exact StatePrefixEnsures.emit _ (fun _ _ _ _ => True.intro)
      (fun _ _ _ prior => congrArg (· ++ [receipt operation wrap r]) prior)
  intro u
  simpa only [pure_bind] using
    rest r.value (receipt operation wrap r) rfl rfl

theorem branch_then {α : Type} (site : Decision) (value : Bool)
    (P : List TagReceipt → Prop) (next : Bool → Obs α)
    (Q : α → List TagReceipt → WGWorld → Ambient → Prop)
    (rest : StatePrefixEnsures (fun h _ _ => P h) (fun _ => True) (next value) Q) :
    StatePrefixEnsures (fun h _ _ => P h) (fun _ => True)
      (liftWGPrefix (branch site value : WG.M Bool) >>= next) Q := by
  apply StatePrefixEnsures.bind
    (Q := fun result h _ _ => result = value ∧ P h)
  · apply StatePrefixEnsures.lift
    · intro h g ambient prior
      trivial
    · intro h g ambient result final after prior run
      change Except.ok ((value,g),_) = _ at run
      cases run
      exact ⟨rfl, prior⟩
  intro result g ambient h prior
  obtain ⟨rfl, prior⟩ := prior
  exact rest g ambient h prior

theorem response_shape (pid : PeerId) (initial : List TagReceipt) :
    StatePrefixEnsures (fun h _ _ => h = initial) (fun _ => True) (observeResponse pid)
      (fun _ h _ _ => ∃ tail, h = initial ++ tail ∧ ResponseShape pid tail) := by
  let Finished := fun h => ∃ tail, h = initial ++ tail ∧ ResponseShape pid tail
  have pureFinished {α : Type} (x : α) :
      StatePrefixPreserves (fun h _ _ => Finished h) (fun _ => True) (pure x : Obs α) :=
    StatePrefixEnsures.pure x (fun _ _ _ _ => True.intro) (fun _ _ _ prior => prior)
  unfold observeResponse HandshakeSources.responseWith
  dsimp only [ops]
  apply StatePrefixEnsures.bind (lift_history _ (fun h => h = initial))
  intro now
  apply StatePrefixEnsures.bind (lift_history _ (fun h => h = initial))
  intro u
  apply record_then
  intro value cr operation result
  cases value with
  | none =>
    apply branch_then
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
    exact StatePrefixEnsures.pure () (fun _ _ _ _ => True.intro)
      (fun _ _ _ prior => ⟨[cr], prior, Or.inl ⟨cr,rfl,operation,result⟩⟩)
  | some msg =>
    apply branch_then
    simp only [Option.isSome_some, ite_true]
    apply StatePrefixEnsures.bind (lift_history _ (fun h => h = initial ++ [cr]))
    intro mac
    apply record_then
    intro ok se sessionOp sessionResult
    apply StatePrefixEnsures.consequence (P := fun h _ _ => Finished h)
    · change StatePrefixEnsures (fun h _ _ => Finished h) (fun _ => True) _
        (fun _ h _ _ => Finished h)
      repeat' first
        | (maintenance_head liftWGPrefix; exact lift_history _ Finished)
        | (maintenance_head Pure.pure; exact pureFinished _)
        | (maintenance_head Bind.bind
           apply StatePrefixEnsures.bind (Q := fun _ h _ _ => Finished h))
        | maintenance_intro
        | (maintenance_head ite; split)
        | (maintenance_head dite; split)
        | maintenance_reduce
        | maintenance_reduce_match
        | maintenance_match
        | contradiction
    · intro h g ambient prior
      refine ⟨[cr,se], ?_, Or.inr ⟨cr,se,msg,ok,rfl,operation,result,sessionOp,sessionResult⟩⟩
      simpa only [List.append_assoc,List.singleton_append] using prior
    · intro result h g ambient prior
      exact prior

def finish (msg : List UInt8) (peer : Option PeerId) : Obs Unit := do
  if ← ops.step (branch .hsWrongPacket peer.isNone) then
    ops.step (invariant "a wrong type of packet in the handshake queue")
  let some pid := peer | ops.step (invariant "unreachable")
  ops.modifyPeer pid fun p => {p with rxBytes := p.rxBytes + msg.length}
  ops.step (modifyDev (Lifetimes.rxStatsUpdate msg.length))
  ops.received pid
  ops.traversal pid
  ops.put peer

def selected (msg : List UInt8) (src : SkbSource) (needsCookie : Bool) : Obs Unit := do
  if ← ops.step (branch .hsSwitchInitiation (messageType msg == MESSAGE_HANDSHAKE_INITIATION)) then
    if ← ops.step (branch .hsInitNeedsCookie needsCookie) then
      ops.cookie msg src
      return
    let peer ← ops.initiation msg
    if ← ops.step (branch .hsInitNoPeer peer.isNone) then return
    let some pid := peer | do
      let peer ← ops.step (invariant "unreachable")
      finish msg peer
    ops.endpoint pid src
    observeResponse pid
    finish msg peer
  else if ← ops.step (branch .hsSwitchResponse (messageType msg == MESSAGE_HANDSHAKE_RESPONSE)) then
    if ← ops.step (branch .hsRespNeedsCookie needsCookie) then
      ops.cookie msg src
      return
    let peer ← ops.response msg
    if ← ops.step (branch .hsRespNoPeer peer.isNone) then return
    let some pid := peer | do
      let peer ← ops.step (invariant "unreachable")
      finish msg peer
    ops.endpoint pid src
    if ← ops.step (branch .hsRespSessionBegun (← ops.session pid)) then
      ops.derived pid
      ops.complete pid
      ops.keepalive pid
    finish msg peer
  else
    finish msg none

theorem after_selected (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    observeAfter msg src loaded mac = (do
      let proceed ← ops.step <| WG.orM
        (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (mac == .withCookie)))
        (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (mac == .noCookie)))
      if proceed then selected msg src false
      else if ← ops.step (WG.andM (branch .hsNeedsCookieLoaded loaded)
        (branch .hsNeedsCookieMac (mac == .noCookie))) then
        selected msg src true
      else pure ()) := by
  simp only [observeAfter, HandshakeSources.afterMacWith, selected, finish,
    observeResponse, pure_bind]
  rfl

theorem finish_history (msg : List UInt8) (peer : Option PeerId) (P : List TagReceipt → Prop) :
    StatePrefixPreserves (fun h _ _ => P h) (fun _ => True) (finish msg peer) := by
  have pureHistory {α : Type} (x : α) :
      StatePrefixPreserves (fun h _ _ => P h) (fun _ => True) (pure x : Obs α) :=
    StatePrefixEnsures.pure x (fun _ _ _ _ => True.intro) (fun _ _ _ prior => prior)
  unfold finish
  dsimp (config := {zeta := false}) only [ops]
  change StatePrefixEnsures (fun h _ _ => P h) (fun _ => True) _ (fun _ h _ _ => P h)
  repeat' first
    | (maintenance_head liftWGPrefix; exact lift_history _ P)
    | (maintenance_head Pure.pure; exact pureHistory _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h _ _ => P h))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction

def projectedResult (msg : List UInt8) (src : SkbSource) (g : WGWorld) (ambient : Ambient) :
    Campaign2.Outcome Unit × List TagReceipt :=
  let observed := runWGPrefix (observe msg src) g ambient []
  (Campaign2.observeResult observed.1, observed.2)

theorem projectedResult_erases (msg : List UInt8) (src : SkbSource)
    (g : WGWorld) (ambient : Ambient) :
    (projectedResult msg src g ambient).1 =
      Campaign2.observeResult (((receiveHandshakePacket msg src).run g).run ambient) :=
  congrArg Campaign2.observeResult (observe_erases msg src g ambient [])

theorem projectedResult_valid (msg : List UInt8) (src : SkbSource)
    (g : WGWorld) (ambient : Ambient) :
    ∀ r ∈ (projectedResult msg src g ambient).2, ReceiptValid r ∧ TagReceiptEffect r := by
  have sound := observe_valid msg src g ambient [] (by intro r member; cases member)
  obtain ⟨suffix,appended,valid,normal⟩ := sound
  intro r member
  have actual : ReceiptValid r := valid r member
  exact ⟨actual, actual.effect⟩

end Leanux.Proofs.WG.Noise.ReceptionCaller
