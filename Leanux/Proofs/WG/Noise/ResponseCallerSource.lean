import Leanux.Proofs.WG.Noise.ResponseMacFrames
import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.Logged.NativeCapture
import Leanux.Proofs.WG.Noise.CreationTagClaims
import Leanux.Proofs.WG.Noise.SessionTagClaims
import Leanux.Proofs.WG.Noise.TagSequenceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ResponseCaller
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Origins

inductive Event where
  | created (pid : PeerId) (run : WGRunWitness (Option (List UInt8)))
  | session (pid : PeerId) (run : WGRunWitness Bool)

abbrev Obs := WGPrefix Event

def ops : HandshakeSources.Ops Obs where
  step := liftWGPrefix
  session := fun pid => receiptWGObserved (liftWGPrefix (beginSession pid)) (.session pid)
  modifyPeer := fun pid f => liftWGPrefix (do setPeer pid (f (← getPeer pid)))
  create := fun pid => receiptWGObserved (liftWGPrefix (createResponse pid)) (.created pid)
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  derived := fun pid => liftWGPrefix (timersSessionDerived pid)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := fun msg => liftWGPrefix (consumeInitiation msg)
  response := fun msg => liftWGPrefix (consumeResponse msg)
  endpoint := fun pid src => liftWGPrefix (setPeerEndpointFromSkb pid src)
  complete := fun pid => liftWGPrefix (timersHandshakeComplete pid)
  keepalive := fun pid => liftWGPrefix (sendKeepalive pid)
  received := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketReceived pid)
  put := fun pid => liftWGPrefix (WG.peerPut pid)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)

def observe (pid : PeerId) : Obs Unit := HandshakeSources.responseWith ops pid

theorem observe_erases (pid : PeerId) :
    ErasesStatePrefix (observe pid) (sendHandshakeResponse pid) := by
  rw [← HandshakeSources.response_original]
  unfold observe HandshakeSources.responseWith
  simp only [ops, HandshakeSources.original]
  repeat' first
    | rfl
    | exact erasesStatePrefix_lift _
    | exact receiptWGObserved_erases (erasesStatePrefix_lift _) _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | maintenance_intro
    | (split)
    | contradiction


abbrev Tags := PeerId → Option Nat
def tags (g : WGWorld) : Tags := responseTagMap g.dev

def Event.Valid : Event → Prop
  | .created pid r => r.Valid (createResponse pid)
  | .session pid r => r.Valid (beginSession pid)

def ValidHistory (h : List Event) : Prop := ∀ e ∈ h, e.Valid

theorem validHistory_snoc {h : List Event} {event : Event}
    (prior : ValidHistory h) (valid : event.Valid) : ValidHistory (h ++ [event]) := by
  intro e hm
  rcases List.mem_append.mp hm with hm | hm
  · exact prior e hm
  · have same : e = event := by simpa using hm
    subst e
    exact valid

private theorem receipt_valid {α : Type} (a : WG.M α)
    (event : WGRunWitness α → Event)
    (valid : ∀ r, r.Valid a → (event r).Valid) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory
      (receiptWGObserved (liftWGPrefix a) event) := by
  unfold receiptWGObserved
  have captured : StatePrefixEnsures (fun h _ _ => ValidHistory h) ValidHistory
      (captureWGRun a) (fun r h _ _ => ValidHistory h ∧ (event r).Valid) := by
    apply StatePrefixEnsures.captureWGRun a
    · intro h g ambient prior
      exact prior
    · intro h g ambient x final after prior run
      exact ⟨prior, valid _ run⟩
  apply StatePrefixEnsures.bind captured
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ h _ _ => ValidHistory h)
  · apply StatePrefixEnsures.emit (event r)
    · intro h g ambient prior
      exact validHistory_snoc prior.1 prior.2
    · intro h g ambient prior
      exact validHistory_snoc prior.1 prior.2
  · intro u
    exact StatePrefixEnsures.pure r.value (fun _ _ _ prior => prior)
      (fun _ _ _ prior => prior)

theorem observe_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (observe pid) := by
  have lifted {α : Type} (a : WG.M α) :
      StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (liftWGPrefix a) :=
    StatePrefixEnsures.lift a (fun _ _ _ prior => prior)
      (fun _ _ _ _ _ _ prior _ => prior)
  have pureValid {α : Type} (x : α) :
      StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (pure x : Obs α) :=
    StatePrefixEnsures.pure x (fun _ _ _ prior => prior) (fun _ _ _ prior => prior)
  have created : StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory
      (ops.create pid) := receipt_valid _ (.created pid) (fun _ h => h)
  have session : StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory
      (ops.session pid) := receipt_valid _ (.session pid) (fun _ h => h)
  unfold observe HandshakeSources.responseWith
  simp only [ops]
  change StatePrefixEnsures (fun h _ _ => ValidHistory h) ValidHistory _
    (fun _ h _ _ => ValidHistory h)
  repeat' first
    | (maintenance_head receiptWGObserved; first | exact created | exact session)
    | (maintenance_head liftWGPrefix; exact lifted _)
    | (maintenance_head Pure.pure; exact pureValid _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h _ _ => ValidHistory h))
    | maintenance_intro
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction

def Event.Effect : Event → Prop
  | .created pid r =>
      (∀ target, tags r.after target = if r.value.isSome then
        if pid = target then some HANDSHAKE_CREATED_RESPONSE else tags r.before target
      else tags r.before target) ∧
      (r.value.isSome → tags r.before pid = some HANDSHAKE_CONSUMED_INITIATION)
  | .session pid r =>
      (∀ target, tags r.after target = if r.value then
        if pid = target then some HANDSHAKE_ZEROED else tags r.before target
      else tags r.before target) ∧
      (r.value = true → tags r.before pid = some HANDSHAKE_CREATED_RESPONSE ∨
        tags r.before pid = some HANDSHAKE_CONSUMED_RESPONSE)

theorem Event.effect {event : Event} (valid : event.Valid) : event.Effect := by
  cases event with
  | created pid r =>
    exact createResponse_tagMap pid r.before.dev r.before r.ambientBefore
      r.value r.after r.ambientAfter rfl valid
  | session pid r =>
    exact beginSession_tagMap pid r.before.dev r.before r.ambientBefore
      r.value r.after r.ambientAfter rfl valid

/-- Exactly the normally completed creator cut, followed by the session cut iff the
creator returned a message. This does not assert whole-call tag framing. -/
def Shape (pid : PeerId) (history : List Event) : Prop :=
  (∃ created, history = [.created pid created] ∧ created.value = none) ∨
  (∃ created session, history = [.created pid created, .session pid session] ∧
    created.value.isSome = true)

private theorem lift_history {α : Type} (a : WG.M α) (P : List Event → Prop) :
    StatePrefixPreserves (fun h _ _ => P h) (fun _ => True) (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ prior _ => prior)

private theorem exists_pre {ι α : Type} (P : ι → List Event → WGWorld → Ambient → Prop)
    (action : Obs α) (Q : α → List Event → WGWorld → Ambient → Prop)
    (proof : ∀ i, StatePrefixEnsures (P i) (fun _ => True) action Q) :
    StatePrefixEnsures (fun h g a => ∃ i, P i h g a) (fun _ => True) action Q := by
  intro g a h prior
  obtain ⟨i, hi⟩ := prior
  exact proof i g a h hi

private theorem pure_pre {α : Type} (condition : Prop)
    (P : List Event → WGWorld → Ambient → Prop) (action : Obs α)
    (Q : α → List Event → WGWorld → Ambient → Prop)
    (proof : condition → StatePrefixEnsures P (fun _ => True) action Q) :
    StatePrefixEnsures (fun h g a => condition ∧ P h g a) (fun _ => True) action Q := by
  intro g a h prior
  exact proof prior.1 g a h prior.2

private theorem receipt_append {α : Type} (a : WG.M α)
    (event : WGRunWitness α → Event) (initialHistory : List Event) :
    StatePrefixEnsures (fun h _ _ => h = initialHistory) (fun _ => True)
      (receiptWGObserved (liftWGPrefix a) event)
      (fun value h _ _ => ∃ r, r.value = value ∧ h = initialHistory ++ [event r]) := by
  unfold receiptWGObserved
  have captured : StatePrefixEnsures (fun h _ _ => h = initialHistory) (fun _ => True)
      (captureWGRun a) (fun _ h _ _ => h = initialHistory) := by
    apply StatePrefixEnsures.captureWGRun a
    · intro h g ambient prior
      trivial
    · intro h g ambient x final after prior run
      exact prior
  apply StatePrefixEnsures.bind captured
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ h _ _ => h = initialHistory ++ [event r])
  · apply StatePrefixEnsures.emit (event r)
    · intro h g ambient prior
      trivial
    · intro h g ambient prior
      rw [prior]
  · intro u
    exact StatePrefixEnsures.pure r.value (fun _ _ _ _ => True.intro)
      (fun _ _ _ prior => ⟨r, rfl, prior⟩)

private theorem branch_continue {α : Type} (site : Decision) (value : Bool)
    (P : List Event → Prop) (next : Bool → Obs α)
    (Q : α → List Event → WGWorld → Ambient → Prop)
    (rest : StatePrefixEnsures (fun h _ _ => P h) (fun _ => True) (next value) Q) :
    StatePrefixEnsures (fun h _ _ => P h) (fun _ => True)
      (liftWGPrefix (branch site value : WG.M Bool) >>= next) Q := by
  have observed : StatePrefixEnsures (fun h _ _ => P h) (fun _ => True)
      (liftWGPrefix (branch site value : WG.M Bool))
      (fun result h _ _ => result = value ∧ P h) := by
    apply StatePrefixEnsures.lift
    · intro h g ambient prior
      trivial
    · intro h g ambient result final after prior run
      change Except.ok ((value, g), _) = _ at run
      cases run
      exact ⟨rfl, prior⟩
  apply StatePrefixEnsures.bind observed
  intro result
  apply pure_pre (result = value)
  intro equal
  subst result
  exact rest

theorem observe_shape (pid : PeerId) (initialHistory : List Event) :
    StatePrefixEnsures (fun h _ _ => h = initialHistory) (fun _ => True) (observe pid)
      (fun _ h _ _ => ∃ suffix, h = initialHistory ++ suffix ∧ Shape pid suffix) := by
  let Finished : List Event → Prop :=
    fun h => ∃ suffix, h = initialHistory ++ suffix ∧ Shape pid suffix
  have pureFinished {α : Type} (x : α) :
      StatePrefixPreserves (fun h _ _ => Finished h) (fun _ => True) (pure x : Obs α) :=
    StatePrefixEnsures.pure x (fun _ _ _ _ => True.intro)
      (fun _ _ _ prior => prior)
  unfold observe HandshakeSources.responseWith
  simp only [ops]
  apply StatePrefixEnsures.bind (lift_history _ (fun h => h = initialHistory))
  intro now
  apply StatePrefixEnsures.bind (lift_history _ (fun h => h = initialHistory))
  intro u
  apply StatePrefixEnsures.bind (receipt_append _ (.created pid) initialHistory)
  intro createdValue
  apply exists_pre
  intro created
  apply pure_pre (created.value = createdValue)
  intro valueEq
  subst createdValue
  cases value : created.value with
  | none =>
    simp only [Option.isSome_none]
    apply branch_continue
    simp only [Bool.false_eq_true, ite_false]
    apply StatePrefixEnsures.pure ()
    · intro h g ambient prior
      trivial
    · intro h g ambient prior
      exact ⟨[.created pid created], prior, Or.inl ⟨created, rfl, value⟩⟩
  | some msg =>
    simp only [Option.isSome_some]
    apply branch_continue
    simp only [ite_true]
    apply StatePrefixEnsures.bind
      (Q := fun _ h _ _ => h = initialHistory ++ [Event.created pid created])
    · exact lift_history (addMacToPacket pid msg)
        (fun h => h = initialHistory ++ [Event.created pid created])
    intro msg'
    apply StatePrefixEnsures.bind
      (receipt_append (beginSession pid) (Event.session pid)
        (initialHistory ++ [Event.created pid created]))
    intro sessionValue
    apply exists_pre
    intro session
    apply pure_pre (session.value = sessionValue)
    intro valueEq
    subst sessionValue
    have completes (h : List Event)
        (prior : h = (initialHistory ++ [.created pid created]) ++ [.session pid session]) :
        Finished h := by
      refine ⟨[.created pid created, .session pid session], ?_,
        Or.inr ⟨created, session, rfl, ?_⟩⟩
      · simpa only [List.append_assoc, List.singleton_append] using prior
      · simp only [value, Option.isSome_some]
    apply StatePrefixEnsures.consequence
      (P := fun h _ _ => Finished h)
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
      exact completes h prior
    · intro result h g ambient prior
      exact prior


/-- Receipt shape and local source facts for a normally completed observer.
No tag frame for the surrounding caller code is assumed. -/
theorem observe_normal_receipts (pid : PeerId) (g final : WGWorld)
    (ambient after : Ambient) (history : List Event)
    (run : runWGPrefix (observe pid) g ambient [] =
      (.ok (((), final), after), history)) :
    Shape pid history ∧ ∀ event ∈ history, event.Valid ∧ event.Effect := by
  have shape := observe_shape pid [] g ambient [] rfl
  have valid := observe_valid pid g ambient [] (by intro e member; cases member)
  obtain ⟨suffix, appended, safe, normal⟩ := shape
  obtain ⟨suffix', appended', sound, normal'⟩ := valid
  have raw := run
  simp only [runWGPrefix, runStatePrefix] at raw
  simp only [raw] at normal sound
  obtain ⟨found, same, shape⟩ := normal
  simp only [List.nil_append] at same
  subst found
  refine ⟨shape, ?_⟩
  intro event member
  have hv := sound event member
  exact ⟨hv, Event.effect hv⟩

theorem original_normal_receipts (pid : PeerId) (g final : WGWorld)
    (ambient after : Ambient)
    (run : ((sendHandshakeResponse pid).run g).run ambient =
      .ok (((), final), after)) :
    ∃ history,
      runWGPrefix (observe pid) g ambient [] =
        (.ok (((), final), after), history) ∧
      Shape pid history ∧
      (∀ event ∈ history, event.Valid ∧ event.Effect) := by
  have erased := observe_erases pid g ambient []
  change (runWGPrefix (observe pid) g ambient []).1 = _ at erased
  rw [run] at erased
  cases observed : runWGPrefix (observe pid) g ambient [] with
  | mk result history =>
    have same : result = .ok (((), final), after) := by
      simpa only [observed] using erased
    subst result
    exact ⟨history, rfl, observe_normal_receipts pid g final ambient after history observed⟩

/-- A native normal-result adapter. A Stop remains a Stop; use projectedResult
to retain receipts alongside a stopped outcome. -/
def observeNative (pid : PeerId) : WG.M (List Event) := fun g ambient =>
  let observed := runWGPrefix (observe pid) g ambient []
  observed.1.map fun ((_, final), after) => ((observed.2, final), after)

theorem observeNative_erases (pid : PeerId) :
    (do let _ ← observeNative pid; pure ()) = sendHandshakeResponse pid := by
  funext g ambient
  have erased := observe_erases pid g ambient []
  change (runWGPrefix (observe pid) g ambient []).1 = _ at erased
  change (((observeNative pid).run g).run ambient >>= fun ((_, final), after) =>
    Except.ok (((), final), after)) = _
  cases observed : runWGPrefix (observe pid) g ambient [] with
  | mk result history =>
    cases result with
    | error stop =>
      simpa only [StateT.run, observeNative, observed, Except.map, bind, Except.bind] using erased
    | ok result =>
      obtain ⟨⟨u, final⟩, after⟩ := result
      cases u
      simpa only [StateT.run, observeNative, observed, Except.map, bind, Except.bind] using erased

theorem observeNative_claim (pid : PeerId) :
    Campaign2.Ensures (observeNative pid) (fun _ => True)
      (fun history _ => Shape pid history ∧
        ∀ event ∈ history, event.Valid ∧ event.Effect) := by
  intro g ambient history final after pre run
  cases observed : runWGPrefix (observe pid) g ambient [] with
  | mk result events =>
    cases result with
    | error stop =>
      simp only [StateT.run, observeNative, observed, Except.map] at run
      cases run
    | ok result =>
      obtain ⟨⟨u, current⟩, inputs⟩ := result
      cases u
      simp only [StateT.run, observeNative, observed, Except.map, Except.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
      exact observe_normal_receipts pid g current ambient inputs events observed

/-- Project actual native results while retaining the persistent journal on
both success and Stop. This is not execution on a reconstructed Snapshot. -/
def projectedResult (pid : PeerId) (g : WGWorld) (ambient : Ambient) :
    Campaign2.Outcome Unit × List Event :=
  let observed := runWGPrefix (observe pid) g ambient []
  (Campaign2.observeResult observed.1, observed.2)

theorem projectedResult_erases (pid : PeerId) (g : WGWorld) (ambient : Ambient) :
    (projectedResult pid g ambient).1 =
      Campaign2.observeResult (((sendHandshakeResponse pid).run g).run ambient) := by
  exact congrArg Campaign2.observeResult (observe_erases pid g ambient [])

theorem projectedResult_valid (pid : PeerId) (g : WGWorld) (ambient : Ambient) :
    ∀ event ∈ (projectedResult pid g ambient).2, event.Valid ∧ event.Effect := by
  have sound := observe_valid pid g ambient [] (by intro e member; cases member)
  obtain ⟨suffix, appended, valid, normal⟩ := sound
  intro event member
  have hv : event.Valid := valid event member
  exact ⟨hv, Event.effect hv⟩


/-- Data-only receipt projection; native witnesses remain in source support. -/
def Event.receipt : Event → TagReceipt
  | .created pid r =>
      ⟨.createResponse pid, Campaign2.snapshot r.before r.ambientBefore,
        .created r.value, Campaign2.snapshot r.after r.ambientAfter⟩
  | .session pid r =>
      ⟨.beginSession pid, Campaign2.snapshot r.before r.ambientBefore,
        .begun r.value, Campaign2.snapshot r.after r.ambientAfter⟩

/-- A projected receipt is backed by an actual native helper execution. -/
def ReceiptValid (receipt : TagReceipt) : Prop :=
  ∃ event : Event, event.receipt = receipt ∧ event.Valid

theorem Event.receipt_effect {event : Event} (valid : event.Valid) :
    TagReceiptEffect event.receipt := by
  cases event with
  | created pid r => exact Event.effect valid
  | session pid r => exact Event.effect valid

/-- Exact normal receipt order, including the original returned values. -/
def ReceiptShape (pid : PeerId) (receipts : List TagReceipt) : Prop :=
  (∃ created, receipts = [created] ∧
    created.operation = .createResponse pid ∧ created.result = .created none) ∨
  (∃ created session msg ok, receipts = [created, session] ∧
    created.operation = .createResponse pid ∧ created.result = .created (some msg) ∧
    session.operation = .beginSession pid ∧ session.result = .begun ok)

theorem Shape.project {pid : PeerId} {history : List Event}
    (shape : Shape pid history) : ReceiptShape pid (history.map Event.receipt) := by
  rcases shape with ⟨created, rfl, empty⟩ | ⟨created, session, rfl, present⟩
  · refine Or.inl ⟨(Event.created pid created).receipt, rfl, rfl, ?_⟩
    change TagReturn.created created.value = TagReturn.created none
    rw [empty]
  · cases value : created.value with
    | none => simp only [value, Option.isSome_none, Bool.false_eq_true] at present
    | some msg =>
      refine Or.inr ⟨(Event.created pid created).receipt,
        (Event.session pid session).receipt, msg, session.value, rfl, rfl, ?_, rfl, rfl⟩
      change TagReturn.created created.value = TagReturn.created (some msg)
      rw [value]

/-- Original source observer returning only Campaign2 receipt records. -/
def observeProjected (pid : PeerId) : WG.M (List TagReceipt) := do
  let history ← observeNative pid
  pure (history.map Event.receipt)

theorem observeProjected_discard (pid : PeerId) :
    (do let _ ← observeProjected pid; pure ()) = sendHandshakeResponse pid := by
  simp only [observeProjected, bind_assoc, pure_bind]
  exact observeNative_erases pid

/-- Initial tags reach the creator cut, and the creator's resulting tags reach
the session cut. No fact about the caller suffix after the session is asserted. -/
def NativeChain (entry : Tags) (history : List Event) : Prop :=
  (∃ pid created, history = [.created pid created] ∧ tags created.before = entry) ∨
  (∃ pid created session,
    history = [.created pid created, .session pid session] ∧
    tags created.before = entry ∧ tags session.before = tags created.after)

private theorem lift_frame {α : Type} (a : WG.M α) (initialHistory : List Event)
    (entry : Tags)
    (frame : ∀ g ambient x final after,
      ((a.run g).run ambient) = .ok ((x, final), after) → tags final = tags g) :
    StatePrefixEnsures (fun h g _ => h = initialHistory ∧ tags g = entry)
      (fun _ => True) (liftWGPrefix a)
      (fun _ h g _ => h = initialHistory ∧ tags g = entry) := by
  apply StatePrefixEnsures.lift
  · intro h g ambient prior
    trivial
  · intro h g ambient x final after prior run
    exact ⟨prior.1, (frame g ambient x final after run).trans prior.2⟩

private theorem receipt_cut {α : Type} (a : WG.M α) (event : WGRunWitness α → Event)
    (initialHistory : List Event) (entry : Tags) :
    StatePrefixEnsures (fun h g _ => h = initialHistory ∧ tags g = entry)
      (fun _ => True) (receiptWGObserved (liftWGPrefix a) event)
      (fun value h g _ => ∃ r, r.value = value ∧ tags r.before = entry ∧
        h = initialHistory ++ [event r] ∧ tags g = tags r.after) := by
  unfold receiptWGObserved
  have captured : StatePrefixEnsures
      (fun h g _ => h = initialHistory ∧ tags g = entry) (fun _ => True)
      (captureWGRun a)
      (fun r h g _ => tags r.before = entry ∧
        h = initialHistory ∧ tags g = tags r.after) := by
    apply StatePrefixEnsures.captureWGRun a
    · intro h g ambient prior
      trivial
    · intro h g ambient value final after prior run
      exact ⟨prior.2, prior.1, rfl⟩
  apply StatePrefixEnsures.bind captured
  intro r
  apply StatePrefixEnsures.bind
    (Q := fun _ h g _ => tags r.before = entry ∧
      h = initialHistory ++ [event r] ∧ tags g = tags r.after)
  · apply StatePrefixEnsures.emit (event r)
    · intro h g ambient prior
      trivial
    · intro h g ambient prior
      exact ⟨prior.1, congrArg (· ++ [event r]) prior.2.1, prior.2.2⟩
  · intro u
    exact StatePrefixEnsures.pure r.value (fun _ _ _ _ => True.intro)
      (fun _ _ _ prior => ⟨r, rfl, prior⟩)

private theorem branch_link {α : Type} (site : Decision) (value : Bool)
    (P : List Event → WGWorld → Ambient → Prop) (next : Bool → Obs α)
    (Q : α → List Event → WGWorld → Ambient → Prop)
    (stable : ∀ h g ambient after, P h g ambient → P h g after)
    (rest : StatePrefixEnsures P (fun _ => True) (next value) Q) :
    StatePrefixEnsures P (fun _ => True)
      (liftWGPrefix (branch site value : WG.M Bool) >>= next) Q := by
  have observed : StatePrefixEnsures P (fun _ => True)
      (liftWGPrefix (branch site value : WG.M Bool))
      (fun result h g ambient => result = value ∧ P h g ambient) := by
    apply StatePrefixEnsures.lift
    · intro h g ambient prior
      trivial
    · intro h g ambient result final after prior run
      change Except.ok ((value, g), _) = _ at run
      cases run
      exact ⟨rfl, stable h g ambient _ prior⟩
  apply StatePrefixEnsures.bind observed
  intro result
  apply pure_pre (result = value)
  intro equal
  subst result
  exact rest

theorem observe_chain (pid : PeerId) (entry : Tags) :
    StatePrefixEnsures (fun h g _ => h = [] ∧ tags g = entry)
      (fun _ => True) (observe pid) (fun _ h _ _ => NativeChain entry h) := by
  let Finished := NativeChain entry
  have lifted {α : Type} (a : WG.M α) :
      StatePrefixPreserves (fun h _ _ => Finished h) (fun _ => True) (liftWGPrefix a) :=
    StatePrefixEnsures.lift a (fun _ _ _ _ => True.intro)
      (fun _ _ _ _ _ _ prior _ => prior)
  have pureFinished {α : Type} (x : α) :
      StatePrefixPreserves (fun h _ _ => Finished h) (fun _ => True) (pure x : Obs α) :=
    StatePrefixEnsures.pure x (fun _ _ _ _ => True.intro)
      (fun _ _ _ prior => prior)
  unfold observe HandshakeSources.responseWith
  simp only [ops]
  apply StatePrefixEnsures.bind (lift_frame _ [] entry (clock_tag_frame _))
  intro now
  apply StatePrefixEnsures.bind (lift_frame _ [] entry (lastSent_tag_frame pid now))
  intro u
  apply StatePrefixEnsures.bind (receipt_cut _ (.created pid) [] entry)
  intro createdValue
  apply exists_pre
  intro created
  apply pure_pre (created.value = createdValue)
  intro valueEq
  subst createdValue
  apply pure_pre (tags created.before = entry)
  intro createdBefore
  cases value : created.value with
  | none =>
    simp only [Option.isSome_none]
    apply branch_link
    · intro h g ambient after prior
      exact prior
    simp only [Bool.false_eq_true, ite_false]
    apply StatePrefixEnsures.pure ()
    · intro h g ambient prior
      trivial
    · intro h g ambient prior
      exact Or.inl ⟨pid, created, prior.1, createdBefore⟩
  | some msg =>
    simp only [Option.isSome_some]
    apply branch_link
    · intro h g ambient after prior
      exact prior
    simp only [ite_true]
    have macFrame : ∀ g ambient x final after,
        (((addMacToPacket pid msg).run g).run ambient) = .ok ((x, final), after) →
          tags final = tags g := by
      intro g ambient x final after run
      exact addMacToPacket_spec_tagMap_variant pid msg g.dev
        g ambient x final after rfl run
    apply StatePrefixEnsures.bind
      (lift_frame (addMacToPacket pid msg) ([] ++ [Event.created pid created]) (tags created.after) macFrame)
    intro msg'
    apply StatePrefixEnsures.bind
      (receipt_cut (beginSession pid) (Event.session pid)
        ([] ++ [Event.created pid created]) (tags created.after))
    intro sessionValue
    apply exists_pre
    intro session
    apply pure_pre (session.value = sessionValue)
    intro valueEq
    subst sessionValue
    apply pure_pre (tags session.before = tags created.after)
    intro sessionBefore
    apply StatePrefixEnsures.consequence
      (P := fun h _ _ => Finished h)
    · change StatePrefixEnsures (fun h _ _ => Finished h) (fun _ => True) _
        (fun _ h _ _ => Finished h)
      repeat' first
        | (maintenance_head liftWGPrefix; exact lifted _)
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
      exact Or.inr ⟨pid, created, session, prior.1, createdBefore, sessionBefore⟩
    · intro result h g ambient prior
      exact prior

end Leanux.Proofs.WG.Noise.ResponseCaller

namespace Leanux.Proofs.WG.Noise.ResponseCaller
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem observe_normal_chain (pid : PeerId) (g final : WGWorld)
    (ambient after : Ambient) (history : List Event)
    (run : runWGPrefix (observe pid) g ambient [] =
      (.ok (((), final), after), history)) : NativeChain (tags g) history := by
  have linked := observe_chain pid (tags g) g ambient [] ⟨rfl, rfl⟩
  obtain ⟨suffix, appended, safe, normal⟩ := linked
  have raw := run
  simp only [runWGPrefix, runStatePrefix] at raw
  simpa only [raw] using normal

theorem observeNative_chain (pid : PeerId) (entry : Tags) :
    Campaign2.Ensures (observeNative pid) (fun s => s.tagAt = entry)
      (fun history _ => NativeChain entry history) := by
  intro g ambient history final after pre run
  cases observed : runWGPrefix (observe pid) g ambient [] with
  | mk result events =>
    cases result with
    | error stop =>
      simp only [StateT.run, observeNative, observed, Except.map] at run
      cases run
    | ok result =>
      obtain ⟨⟨u, current⟩, inputs⟩ := result
      cases u
      simp only [StateT.run, observeNative, observed, Except.map, Except.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
      have linked := observe_normal_chain pid g current ambient inputs events observed
      change tags g = entry at pre
      rwa [pre] at linked

end Leanux.Proofs.WG.Noise.ResponseCaller
