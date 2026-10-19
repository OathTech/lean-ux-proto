import Leanux.Proofs.WG.Roaming.EndpointAttemptSource
import Leanux.Proofs.WG.Roaming.InitiationCallClaims
import Leanux.Proofs.WG.Roaming.ResponseCallClaims
import Leanux.Proofs.WG.Roaming.EndpointSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeAttemptAuth
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
variable {E C α : Type}
def ValidHistory (valid : E → Prop) (h : List E) : Prop := ∀ e ∈ h, valid e
theorem native_history (valid : E → Prop) (action : WG.M α) :
    StatePrefixPreserves (fun h _ _ => ValidHistory valid h) (ValidHistory valid)
      (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · exact fun _ _ _ h => h
  · exact fun _ _ _ _ _ _ h _ => h
theorem beforeCall_valid (valid : E → Prop) (event : WGWorld → Ambient → E)
    (checked : ∀ g ambient, valid (event g ambient)) (action : WG.M α) :
    StatePrefixPreserves (fun h _ _ => ValidHistory valid h) (ValidHistory valid)
      (EndpointAttempt.beforeCall event (liftWGPrefix action)) := by
  intro g ambient history prior
  have safe : ValidHistory valid (history ++ [event g ambient]) := by
    intro e member
    rcases List.mem_append.mp member with old | fresh
    · exact prior e old
    · have same : e = event g ambient := by simpa using fresh
      subst e
      exact checked g ambient
  refine ⟨[event g ambient],rfl,safe,?_⟩
  have run : runPrefix ((EndpointAttempt.beforeCall event (liftWGPrefix action)).run g) ambient history =
      ((action.run g).run ambient, history ++ [event g ambient]) := rfl
  rw [run]
  cases (action.run g).run ambient <;> first | trivial | exact safe

theorem fromSkb_valid (valid : E → Prop) (pid : PeerId) (src : SkbSource)
    (setter : PeerId → Endpoint → WGPrefix E Unit)
    (checked : ∀ endpoint, endpoint = sourceEndpoint src →
      (src.family = 4 ∨ src.family = 6) →
      StatePrefixPreserves (fun h _ _ => ValidHistory valid h) (ValidHistory valid)
        (setter pid endpoint)) :
    StatePrefixPreserves (fun h _ _ => ValidHistory valid h) (ValidHistory valid)
      (EndpointAttempt.fromSkbWith (fun a => liftWGPrefix a) setter pid src) := by
  unfold EndpointAttempt.fromSkbWith
  apply StatePrefixEnsures.bind (Q := fun result h _ _ =>
    ValidHistory valid h ∧ result = some (sourceEndpoint src) ∧ (src.family = 4 ∨ src.family = 6))
  · apply StatePrefixEnsures.lift
    · exact fun _ _ _ h => h
    · intro h g ambient result current after prior run
      have facts := (ensures_iff _ _ _).mpr (endpointFromSkb_exact src (fun _ => True))
        g ambient result current after True.intro run
      exact ⟨prior,facts.2⟩
  · intro result
    apply StatePrefixEnsures.bind (Q := fun _ h _ _ =>
      ValidHistory valid h ∧ result = some (sourceEndpoint src) ∧ (src.family = 4 ∨ src.family = 6))
    · apply StatePrefixEnsures.lift
      · exact fun _ _ _ h => h.1
      · exact fun _ _ _ _ _ _ h _ => h
    · intro successful
      cases successful <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact StatePrefixEnsures.pure () (fun _ _ _ h => h.1) (fun _ _ _ h => h.1)
      · cases result with
        | none =>
          exact (native_history valid (invariant "unreachable")).consequence
            (fun _ _ _ h => h.1) (fun _ _ _ _ h => h)
        | some endpoint =>
          intro g ambient history prior
          exact checked endpoint (Option.some.inj prior.2.1) prior.2.2
            g ambient history prior.1


theorem fromSkb_erases (pid : PeerId) (src : SkbSource)
    (setter : PeerId → Endpoint → WGPrefix E Unit)
    (checked : ∀ endpoint, ErasesStatePrefix (setter pid endpoint) (setPeerEndpoint pid endpoint)) :
    ErasesStatePrefix
      (EndpointAttempt.fromSkbWith (fun a => liftWGPrefix a) setter pid src)
      (setPeerEndpointFromSkb pid src) := by
  rw [← EndpointAttempt.fromSkb_original]
  unfold EndpointAttempt.fromSkbWith
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro endpoint
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro success
  cases success <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact erasesStatePrefix_pure ()
  · cases endpoint with
    | none => exact erasesStatePrefix_lift _
    | some e => exact checked e

def callObserved (before : WG.M (Option C)) (peer : C → PeerId)
    (suffix : C → WG.M Unit) (src : SkbSource)
    (event : C → Endpoint → WGWorld → Ambient → E) : WGPrefix E Unit := do
  let candidate ← liftWGPrefix before
  match candidate with
  | none => pure ()
  | some cut =>
    EndpointAttempt.fromSkbWith (fun a => liftWGPrefix a)
      (fun pid endpoint => EndpointAttempt.beforeCall (event cut endpoint)
        (liftWGPrefix (setPeerEndpoint pid endpoint))) (peer cut) src
    liftWGPrefix (suffix cut)

theorem callObserved_erases (before : WG.M (Option C)) (peer : C → PeerId)
    (suffix : C → WG.M Unit) (src : SkbSource)
    (event : C → Endpoint → WGWorld → Ambient → E) :
    ErasesStatePrefix (callObserved before peer suffix src event)
      (before >>= fun candidate => match candidate with
        | none => pure ()
        | some cut => do setPeerEndpointFromSkb (peer cut) src; suffix cut) := by
  unfold callObserved
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro candidate
  cases candidate with
  | none => exact erasesStatePrefix_pure ()
  | some cut =>
    apply erasesStatePrefix_bind
    · exact fromSkb_erases (peer cut) src _
        (fun endpoint => EndpointAttempt.beforeCall_erases _ _ _ (erasesStatePrefix_lift _))
    · exact fun _ => erasesStatePrefix_lift _

theorem callObserved_valid (valid : E → Prop) (facts : C → Prop)
    (before : WG.M (Option C)) (peer : C → PeerId)
    (suffix : C → WG.M Unit) (src : SkbSource)
    (event : C → Endpoint → WGWorld → Ambient → E)
    (prefixFacts : Campaign2.Ensures before (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → facts cut))
    (checked : ∀ cut endpoint g ambient, facts cut → endpoint = sourceEndpoint src →
      (src.family = 4 ∨ src.family = 6) → valid (event cut endpoint g ambient)) :
    StatePrefixPreserves (fun h _ _ => ValidHistory valid h) (ValidHistory valid)
      (callObserved before peer suffix src event) := by
  unfold callObserved
  apply StatePrefixEnsures.bind (Q := fun result h _ _ =>
    ValidHistory valid h ∧ ∀ cut, result = some cut → facts cut)
  · apply StatePrefixEnsures.lift
    · exact fun _ _ _ h => h
    · intro h g ambient result current after prior run
      exact ⟨prior,prefixFacts g ambient result current after True.intro run⟩
  · intro candidate
    cases candidate with
    | none => exact StatePrefixEnsures.pure () (fun _ _ _ h => h.1) (fun _ _ _ h => h.1)
    | some cut =>
      intro g ambient history prior
      have cutFacts := prior.2 cut rfl
      have conversion := fromSkb_valid valid (peer cut) src
        (fun pid endpoint => EndpointAttempt.beforeCall (event cut endpoint)
          (liftWGPrefix (setPeerEndpoint pid endpoint)))
        (fun endpoint exactEndpoint family => beforeCall_valid valid (event cut endpoint)
          (fun g ambient => checked cut endpoint g ambient cutFacts exactEndpoint family) _)
      exact (conversion.bind (fun _ => native_history valid (suffix cut))) g ambient history prior.1

theorem initiation_erases (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (event : InitiationCallCut → Endpoint → WGWorld → Ambient → E) :
    ErasesStatePrefix
      (callObserved (initiationCallPrefix msg src) (fun cut => cut.consumed.pid)
        (fun cut => initiationAfterSetter msg cut.consumed.pid) src event)
      (receiveHandshakePacket msg src) := by
  rw [← receiveHandshakePacket_initiation msg src kind]
  unfold callObserved
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro candidate
  cases candidate with
  | none => exact erasesStatePrefix_pure ()
  | some cut =>
    change ErasesStatePrefix
      (do EndpointAttempt.fromSkbWith (fun a => liftWGPrefix a)
            (fun pid endpoint => EndpointAttempt.beforeCall (event cut endpoint)
              (liftWGPrefix (setPeerEndpoint pid endpoint))) (cut.consumed.pid) src
          liftWGPrefix (initiationAfterSetter msg cut.consumed.pid))
      (do setPeerEndpointFromSkb (cut.consumed.pid) src; initiationAfterSetter msg cut.consumed.pid)
    apply erasesStatePrefix_bind
    · exact fromSkb_erases (cut.consumed.pid) src _
        (fun endpoint => EndpointAttempt.beforeCall_erases _ _ _ (erasesStatePrefix_lift _))
    · exact fun _ => erasesStatePrefix_lift _

theorem response_erases (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (event : ResponseCallCut → Endpoint → WGWorld → Ambient → E) :
    ErasesStatePrefix
      (callObserved (responseCallPrefix msg src) (fun cut => cut.consumed.input.pid)
        (fun cut => responseAfterSetter msg cut.consumed.input.pid) src event)
      (receiveHandshakePacket msg src) := by
  rw [← receiveHandshakePacket_response msg src kind]
  unfold callObserved
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro candidate
  cases candidate with
  | none => exact erasesStatePrefix_pure ()
  | some cut =>
    change ErasesStatePrefix
      (do EndpointAttempt.fromSkbWith (fun a => liftWGPrefix a)
            (fun pid endpoint => EndpointAttempt.beforeCall (event cut endpoint)
              (liftWGPrefix (setPeerEndpoint pid endpoint))) (cut.consumed.input.pid) src
          liftWGPrefix (responseAfterSetter msg cut.consumed.input.pid))
      (do setPeerEndpointFromSkb (cut.consumed.input.pid) src; responseAfterSetter msg cut.consumed.input.pid)
    apply erasesStatePrefix_bind
    · exact fromSkb_erases (cut.consumed.input.pid) src _
        (fun endpoint => EndpointAttempt.beforeCall_erases _ _ _ (erasesStatePrefix_lift _))
    · exact fun _ => erasesStatePrefix_lift _

theorem initiation_valid (msg : List UInt8) (src : SkbSource)
    (valid : E → Prop) (event : InitiationCallCut → Endpoint → WGWorld → Ambient → E)
    (checked : ∀ cut endpoint g ambient, InitiationCallFacts msg cut →
      endpoint = sourceEndpoint src → (src.family = 4 ∨ src.family = 6) →
      valid (event cut endpoint g ambient)) :
    StatePrefixPreserves (fun h _ _ => ValidHistory valid h) (ValidHistory valid)
      (callObserved (initiationCallPrefix msg src) (fun cut => cut.consumed.pid)
        (fun cut => initiationAfterSetter msg cut.consumed.pid) src event) :=
  callObserved_valid valid (InitiationCallFacts msg) _ _ _ _ _
    (fun g ambient result current after pre run cut selected =>
      (initiationCallPrefix_facts msg src g ambient result current after pre run cut selected).2) checked

theorem response_valid (msg : List UInt8) (src : SkbSource)
    (valid : E → Prop) (event : ResponseCallCut → Endpoint → WGWorld → Ambient → E)
    (checked : ∀ cut endpoint g ambient, ResponseCallFacts msg cut →
      endpoint = sourceEndpoint src → (src.family = 4 ∨ src.family = 6) →
      valid (event cut endpoint g ambient)) :
    StatePrefixPreserves (fun h _ _ => ValidHistory valid h) (ValidHistory valid)
      (callObserved (responseCallPrefix msg src) (fun cut => cut.consumed.input.pid)
        (fun cut => responseAfterSetter msg cut.consumed.input.pid) src event) :=
  callObserved_valid valid (ResponseCallFacts msg) _ _ _ _ _
    (fun g ambient result current after pre run cut selected =>
      (responseCallPrefix_facts msg src g ambient result current after pre run cut selected).2) checked

end Leanux.Proofs.WG.Roaming.HandshakeAttemptAuth
