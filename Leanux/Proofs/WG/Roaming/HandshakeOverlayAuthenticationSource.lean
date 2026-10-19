import Leanux.Proofs.WG.Roaming.HandshakeOverlayProjectionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Origins
variable {E F α State : Type}

def attemptReception (msg : List UInt8) (src : SkbSource) : PrefixM Attempt Unit :=
  HandshakeSources.receptionWith
    (HandshakeEndpoint.ops productLift (fun pid src => liftWGObserver (endpointOnly msg pid src))) msg src

theorem initiation_cut (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    attemptReception msg src =
      liftWGObserver (HandshakeAttemptAuth.callObserved (initiationCallPrefix msg src)
        (fun cut => cut.consumed.pid) (fun cut => initiationAfterSetter msg cut.consumed.pid) src
        (fun cut ep g a => ⟨msg,src,cut.consumed.pid,ep,Campaign2.snapshot g a⟩)) := by
  rw [attemptReception,← initiation_context productLift _ msg src kind]
  unfold HandshakeAttemptAuth.callObserved
  rw [liftWGObserver_bind]
  apply congrArg (fun f => liftWGObserver (liftWGPrefix (initiationCallPrefix msg src)) >>= f)
  funext candidate
  cases candidate with
  | none => rfl
  | some cut =>
    change (liftWGObserver (endpointOnly msg cut.consumed.pid src) >>=
      fun _ => liftWGObserver (liftWGPrefix (initiationAfterSetter msg cut.consumed.pid))) = _
    rw [← liftWGObserver_bind]
    rfl

theorem response_cut (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    attemptReception msg src =
      liftWGObserver (HandshakeAttemptAuth.callObserved (responseCallPrefix msg src)
        (fun cut => cut.consumed.input.pid) (fun cut => responseAfterSetter msg cut.consumed.input.pid) src
        (fun cut ep g a => ⟨msg,src,cut.consumed.input.pid,ep,Campaign2.snapshot g a⟩)) := by
  rw [attemptReception,← response_context productLift _ msg src kind]
  unfold HandshakeAttemptAuth.callObserved
  rw [liftWGObserver_bind]
  apply congrArg (fun f => liftWGObserver (liftWGPrefix (responseCallPrefix msg src)) >>= f)
  funext candidate
  cases candidate with
  | none => rfl
  | some cut =>
    change (liftWGObserver (endpointOnly msg cut.consumed.input.pid src) >>=
      fun _ => liftWGObserver (liftWGPrefix (responseAfterSetter msg cut.consumed.input.pid))) = _
    rw [← liftWGObserver_bind]
    rfl


theorem beforeCall_at (valid : E → Prop) (P : WGWorld → Prop)
    (event : WGWorld → Ambient → E) (action : WG.M α)
    (checked : ∀ g a, P g → valid (event g a)) :
    StatePrefixEnsures (fun h g _ => HandshakeAttemptAuth.ValidHistory valid h ∧ P g)
      (HandshakeAttemptAuth.ValidHistory valid)
      (EndpointAttempt.beforeCall event (liftWGPrefix action))
      (fun _ h _ _ => HandshakeAttemptAuth.ValidHistory valid h) := by
  intro g a h prior
  have kept : HandshakeAttemptAuth.ValidHistory valid (h ++ [event g a]) := by
    intro e member
    rcases List.mem_append.mp member with old | new
    · exact prior.1 e old
    · have same : e = event g a := by simpa using new
      subst e
      exact checked g a prior.2
  refine ⟨[event g a],rfl,kept,?_⟩
  have run : runPrefix ((EndpointAttempt.beforeCall event (liftWGPrefix action)).run g) a h =
      ((action.run g).run a,h ++ [event g a]) := rfl
  rw [run]
  cases (action.run g).run a <;> first | trivial | exact kept

theorem fromSkb_at (valid : E → Prop) (P : WGWorld → Prop)
    (pid : PeerId) (src : SkbSource)
    (setter : PeerId → Endpoint → WGPrefix E Unit)
    (checked : ∀ ep, ep = sourceEndpoint src → (src.family = 4 ∨ src.family = 6) →
      StatePrefixEnsures (fun h g _ => HandshakeAttemptAuth.ValidHistory valid h ∧ P g)
        (HandshakeAttemptAuth.ValidHistory valid) (setter pid ep)
        (fun _ h _ _ => HandshakeAttemptAuth.ValidHistory valid h)) :
    StatePrefixEnsures (fun h g _ => HandshakeAttemptAuth.ValidHistory valid h ∧ P g)
      (HandshakeAttemptAuth.ValidHistory valid)
      (EndpointAttempt.fromSkbWith liftWGPrefix setter pid src)
      (fun _ h _ _ => HandshakeAttemptAuth.ValidHistory valid h) := by
  unfold EndpointAttempt.fromSkbWith
  apply StatePrefixEnsures.bind (Q := fun result h g _ =>
    HandshakeAttemptAuth.ValidHistory valid h ∧ P g ∧
    result = some (sourceEndpoint src) ∧ (src.family = 4 ∨ src.family = 6))
  · apply StatePrefixEnsures.lift
    · exact fun _ _ _ h => h.1
    · intro h g a result current after prior run
      have facts := (Noise.ensures_iff _ _ _).mpr (endpointFromSkb_exact src P)
        g a result current after prior.2 run
      exact ⟨prior.1,facts⟩
  · intro result
    apply StatePrefixEnsures.bind (Q := fun _ h g _ =>
      HandshakeAttemptAuth.ValidHistory valid h ∧ P g ∧
      result = some (sourceEndpoint src) ∧ (src.family = 4 ∨ src.family = 6))
    · apply StatePrefixEnsures.lift
      · exact fun _ _ _ h => h.1
      · intro h g a out current after prior run
        have same : current = g := by
          change Except.ok ((result.isSome,g),{a with steps := a.steps.push {
            decision := .epFromSkbOk,outcome := result.isSome,netRx := a.netRxSection}}) =
            Except.ok ((out,current),after) at run
          exact (Prod.mk.inj (Prod.mk.inj (Except.ok.inj run)).1).2.symm
        simpa only [same] using prior
    · intro success
      cases success <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact StatePrefixEnsures.pure () (fun _ _ _ h => h.1) (fun _ _ _ h => h.1)
      · cases result with
        | none =>
          exact (HandshakeAttemptAuth.native_history valid (invariant "unreachable")).consequence
            (fun _ _ _ h => h.1) (fun _ _ _ _ h => h)
        | some ep =>
          intro g a h prior
          exact checked ep (Option.some.inj prior.2.2.1) prior.2.2.2 g a h ⟨prior.1,prior.2.1⟩

theorem callObserved_at {C : Type} (valid : E → Prop) (facts : C → Prop)
    (device : C → Option Device) (before : WG.M (Option C)) (peer : C → PeerId)
    (suffix : C → WG.M Unit) (src : SkbSource)
    (event : C → Endpoint → WGWorld → Ambient → E)
    (prefixFacts : Campaign2.Ensures before (fun _ => True) (fun result s =>
      ∀ cut, result = some cut → facts cut ∧ device cut = s.wg.device))
    (checked : ∀ cut ep g a, facts cut → device cut = g.dev →
      ep = sourceEndpoint src → (src.family = 4 ∨ src.family = 6) → valid (event cut ep g a)) :
    StatePrefixPreserves (fun h _ _ => HandshakeAttemptAuth.ValidHistory valid h)
      (HandshakeAttemptAuth.ValidHistory valid)
      (HandshakeAttemptAuth.callObserved before peer suffix src event) := by
  unfold HandshakeAttemptAuth.callObserved
  apply StatePrefixEnsures.bind (Q := fun result h g _ =>
    HandshakeAttemptAuth.ValidHistory valid h ∧
      ∀ cut, result = some cut → facts cut ∧ device cut = g.dev)
  · apply StatePrefixEnsures.lift
    · exact fun _ _ _ h => h
    · intro h g a result current after prior run
      exact ⟨prior,prefixFacts g a result current after trivial run⟩
  · intro candidate
    cases candidate with
    | none => exact StatePrefixEnsures.pure () (fun _ _ _ h => h.1) (fun _ _ _ h => h.1)
    | some cut =>
      intro g a h prior
      have info := prior.2 cut rfl
      have conversion := fromSkb_at valid (fun g => device cut = g.dev) (peer cut) src
        (fun p ep => EndpointAttempt.beforeCall (event cut ep) (liftWGPrefix (setPeerEndpoint p ep)))
        (fun ep endpoint family => beforeCall_at valid _ (event cut ep) _
          (fun current after same => checked cut ep current after info.1 same endpoint family))
      exact (conversion.bind (fun _ => HandshakeAttemptAuth.native_history valid (suffix cut)))
        g a h ⟨prior.1,info.2⟩


theorem initiation_valid (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    PrefixPreserves (fun h _ => HandshakeAttemptAuth.ValidHistory Authenticated h)
      (HandshakeAttemptAuth.ValidHistory Authenticated) (attemptReception msg src) := by
  rw [initiation_cut msg src kind]
  exact (callObserved_at Authenticated (InitiationCallFacts msg)
    (fun cut => cut.beforeSetter.wg.device) _ _ _ src _
    (fun g a result current after _ run cut selected => by
      have fact := initiationCallPrefix_facts msg src g a result current after trivial run cut selected
      exact ⟨fact.2,congrArg (fun s : Campaign2.Snapshot => s.wg.device) fact.1⟩)
    (by
      intro cut ep g a facts atDevice exactEndpoint family
      exact ⟨exactEndpoint,family,Or.inl ⟨kind,cut,facts,rfl,atDevice.symm⟩⟩)).liftWGObserver

theorem response_valid (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    PrefixPreserves (fun h _ => HandshakeAttemptAuth.ValidHistory Authenticated h)
      (HandshakeAttemptAuth.ValidHistory Authenticated) (attemptReception msg src) := by
  rw [response_cut msg src kind]
  exact (callObserved_at Authenticated (ResponseCallFacts msg)
    (fun cut => cut.beforeSetter.wg.device) _ _ _ src _
    (fun g a result current after _ run cut selected => by
      have fact := responseCallPrefix_facts msg src g a result current after trivial run cut selected
      exact ⟨fact.2,congrArg (fun s : Campaign2.Snapshot => s.wg.device) fact.1⟩)
    (by
      intro cut ep g a facts atDevice exactEndpoint family
      exact ⟨exactEndpoint,family,Or.inr ⟨kind,cut,facts,rfl,atDevice.symm⟩⟩)).liftWGObserver


theorem afterMac_other (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState)
    (notInit : messageType msg ≠ MESSAGE_HANDSHAKE_INITIATION)
    (notResponse : messageType msg ≠ MESSAGE_HANDSHAKE_RESPONSE) :
    HandshakeSources.afterMacWith
      (HandshakeEndpoint.ops productLift (fun pid src => liftWGObserver (endpointOnly msg pid src))) msg src loaded mac =
    HandshakeSources.afterMacWith
      (HandshakeEndpoint.ops productLift (fun pid src => productLift.action (setPeerEndpointFromSkb pid src))) msg src loaded mac := by
  simp only [HandshakeSources.afterMacWith,HandshakeEndpoint.ops]
  simp only [HandshakeEndpoint.branch_native,HandshakeEndpoint.lift_bind,
    HandshakeEndpoint.lift_pure,pure_bind,bind_assoc]
  simp only [beq_eq_false_iff_ne.mpr notInit,beq_eq_false_iff_ne.mpr notResponse,
    Bool.false_eq_true,ite_false]


theorem native_valid (action : WG.M α) :
    PrefixPreserves (fun h _ => HandshakeAttemptAuth.ValidHistory Authenticated h)
      (HandshakeAttemptAuth.ValidHistory Authenticated) (productLift.action action) :=
  (HandshakeAttemptAuth.native_history Authenticated action).liftWGObserver


elab "overlay_action_head" head:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless target.isAppOf ``PrefixPreserves || target.isAppOf ``Appends do
    throwError "not an observer contract"
  let action := target.getAppArgs.back!
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo head
  unless action.isAppOf name do throwError "different action head"

theorem pure_valid (x : α) :
    PrefixPreserves (fun h _ => HandshakeAttemptAuth.ValidHistory Authenticated h)
      (HandshakeAttemptAuth.ValidHistory Authenticated) (pure x : PrefixM Attempt α) := by
  intro w h prior
  exact ⟨[],by simp,prior,prior⟩

theorem afterMac_quiet (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState)
    (notInit : messageType msg ≠ MESSAGE_HANDSHAKE_INITIATION)
    (notResponse : messageType msg ≠ MESSAGE_HANDSHAKE_RESPONSE) :
    PrefixPreserves (fun h _ => HandshakeAttemptAuth.ValidHistory Authenticated h)
      (HandshakeAttemptAuth.ValidHistory Authenticated)
      (HandshakeSources.afterMacWith
        (HandshakeEndpoint.ops productLift (fun pid src => productLift.action (setPeerEndpointFromSkb pid src)))
        msg src loaded mac) := by
  simp only [HandshakeSources.afterMacWith,HandshakeEndpoint.ops]
  simp only [HandshakeEndpoint.branch_native,HandshakeEndpoint.lift_bind,
    HandshakeEndpoint.lift_pure,pure_bind,bind_assoc]
  simp only [beq_eq_false_iff_ne.mpr notInit,beq_eq_false_iff_ne.mpr notResponse,
    Bool.false_eq_true,ite_false]
  repeat' first
    | (overlay_action_head HandshakeEndpoint.Lift.action; exact native_valid _)
    | exact pure_valid _
    | (overlay_action_head Bind.bind; apply PrefixPreserves.bind)
    | apply PrefixPreserves.ite
    | handshake_project_intro
    | split

theorem other_valid (msg : List UInt8) (src : SkbSource)
    (notInit : messageType msg ≠ MESSAGE_HANDSHAKE_INITIATION)
    (notResponse : messageType msg ≠ MESSAGE_HANDSHAKE_RESPONSE) :
    PrefixPreserves (fun h _ => HandshakeAttemptAuth.ValidHistory Authenticated h)
      (HandshakeAttemptAuth.ValidHistory Authenticated) (attemptReception msg src) := by
  unfold attemptReception HandshakeSources.receptionWith
  apply PrefixPreserves.bind (native_valid _)
  intro cookie
  cases cookie <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · apply PrefixPreserves.bind (native_valid _)
    intro loaded
    apply PrefixPreserves.bind (native_valid _)
    intro mac
    rw [afterMac_other msg src loaded mac notInit notResponse]
    exact afterMac_quiet msg src loaded mac notInit notResponse
  · exact (native_valid (cookieMessageConsume msg)).bind (fun _ => pure_valid ())

theorem attemptReception_valid (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun h _ => HandshakeAttemptAuth.ValidHistory Authenticated h)
      (HandshakeAttemptAuth.ValidHistory Authenticated) (attemptReception msg src) := by
  by_cases kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION
  · exact initiation_valid msg src kind
  · by_cases response : messageType msg = MESSAGE_HANDSHAKE_RESPONSE
    · exact response_valid msg src response
    · exact other_valid msg src kind response


end Leanux.Proofs.WG.Roaming.HandshakeOverlay
