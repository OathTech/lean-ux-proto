import Leanux.Proofs.WG.TimerDiscipline.SessionArmEventFrames
import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionClaims
import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- All normal outcomes of the existing hook observer, from its actual entry.
Missing records and arm/guard failures remain Stops of the original operation. -/
theorem projected_session_derived_all_modes (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observed (liftWG (timersSessionDerived pid))
      (liftWG (callerJiffies .timerJiffiesSessionDerived)))
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if d.running && !p.isDead then
        peerTimerArmEffect entry.toSnapshot pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS final.wg
        else final.wg = entry.wg) := by
  apply observed_effect
  intro initial result final pre run
  obtain ⟨rfl,device⟩ := pre
  change (((timersSessionDerived pid).run initial.wg).run initial.ambient >>= _) = _ at run
  cases native : ((timersSessionDerived pid).run initial.wg).run initial.ambient with
  | error stop => rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value,current⟩,inputs⟩ := pair
    rw [native] at run
    cases run
    exact timersSessionDerived_effect pid d p resident (Campaign2.snapshot initial.wg initial.ambient)
      initial.wg initial.ambient _ _ _ ⟨rfl,device⟩ native

/-- The two original callers differ only in this branch's recorded decision.
This factors their existing observer definitions, not a replacement execution. -/
def sessionPrefixAt (decision : Decision) (pid : PeerId) : Leanux.M ResponseSessionCut := do
  let beforeSession ← Campaign2.Product.read
  let begun ← liftWG (beginSession pid)
  let afterSession ← Campaign2.Product.read
  let reached ← branch decision begun
  let beforeArm ← Campaign2.Product.read
  let arm ← if reached then do
      let value ← observed (liftWG (timersSessionDerived pid)) (liftWG (callerJiffies .timerJiffiesSessionDerived))
      let afterArm ← Campaign2.Product.read
      pure (some ⟨value.1,afterArm⟩)
    else pure none
  return ⟨beforeSession,begun,afterSession,beforeArm,arm⟩

/-- Attach the all-mode actual hook effect to the allocation serial already
established by the original session prefix. -/
theorem sessionPrefix_event (decision : Decision) (pid : PeerId)
    (facts : Noise.Product.Ensures (sessionPrefixAt decision pid) (fun _ => True)
      (fun cut _ => ResponseSessionFacts pid cut)) :
    Noise.Product.Ensures (sessionPrefixAt decision pid) (fun _ => True)
      (fun cut _ => SessionArmEvent pid cut) := by
  intro initial cut final pre run
  have base := facts initial cut final pre run
  refine ⟨base,?_⟩
  change ((liftWG (beginSession pid)).run initial >>= _) = _ at run
  cases session : (liftWG (beginSession pid)).run initial with
  | error stop => rw [session] at run; cases run
  | ok pair =>
    obtain ⟨begun,afterSession⟩ := pair
    rw [session] at run
    cases begun with
    | false =>
      cases run
      intro arm impossible
      cases impossible
    | true =>
      let before : World := {afterSession with ambient := {afterSession.ambient with steps := afterSession.ambient.steps.push { decision := decision, outcome := true, netRx := afterSession.ambient.netRxSection }}}
      change ((observed (liftWG (timersSessionDerived pid))
        (liftWG (callerJiffies .timerJiffiesSessionDerived))).run before >>= fun out =>
        .ok (⟨Campaign2.Product.snapshot initial,true,Campaign2.Product.snapshot afterSession,
          Campaign2.Product.snapshot before,some ⟨out.1.1,Campaign2.Product.snapshot out.2⟩⟩,out.2)) = .ok (cut,final) at run
      cases hook : (observed (liftWG (timersSessionDerived pid))
          (liftWG (callerJiffies .timerJiffiesSessionDerived))).run before with
      | error stop => rw [hook] at run; cases run
      | ok pair =>
        obtain ⟨value,afterArm⟩ := pair
        rw [hook] at run
        cases run
        intro arm same
        cases same
        obtain ⟨d,p,next,_,_,_,_,beforeDevice,_,_,armFacts⟩ := base
        obtain ⟨serial,q,resident,alive,_⟩ := armFacts _ rfl
        have effect := projected_session_derived_all_modes pid next q resident
          (Campaign2.Product.snapshot before) before value afterArm ⟨rfl,beforeDevice⟩ hook
        simp only [alive,Bool.not_false,Bool.and_true] at effect
        refine ⟨next,q,beforeDevice,resident,alive,?_,effect,?_⟩
        · cases running : next.running with
          | false =>
            simp only [running,Bool.false_eq_true,ite_false] at effect
            exact (congrArg (fun s : Campaign2.State => s.keypairCounter) effect).trans serial
          | true =>
            simp only [running,ite_true] at effect
            exact (peerTimerArmEffect_counters _ pid q _ _ _ effect).1.trans serial
        · cases running : next.running with
          | false =>
            simp only [running,Bool.false_eq_true,ite_false] at effect
            exact Or.inl (congrArg (fun s : Campaign2.State => s.timerEnqueues) effect)
          | true =>
            simp only [running,ite_true] at effect
            exact (peerTimerArmEffect_counters _ pid q _ _ _ effect).2

/-- The response prefix actually reaching a session receives its allocation
serial and guarded hook effect, without assuming consumer/session success. -/
theorem responseSessionCallPrefix_event (msg : List UInt8) (src : SkbSource) :
    Noise.Product.Ensures (responseSessionCallPrefix msg src) (fun _ => True)
      (fun candidate _ => ∀ cut, candidate = some cut →
        SessionArmEvent cut.response.consumed.input.pid cut.session) := by
  have keep {α : Type} (action : Leanux.M α) :
      Noise.Product.Ensures action (fun _ => True) (fun _ _ => True) := by
    intro initial result final pre run
    trivial
  unfold responseSessionCallPrefix
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro candidate
  cases candidate with
  | none => intro initial out final pre run cut impossible; cases run; cases impossible
  | some cut =>
    refine Noise.Product.ensures_bind _ _ (keep _) ?_
    intro ignored
    have session : Noise.Product.Ensures (responseSessionPrefix cut.consumed.input.pid)
        (fun _ => True) (fun seen _ => SessionArmEvent cut.consumed.input.pid seen) := by
      apply sessionPrefix_event .hsRespSessionBegun
      intro initial seen final pre run
      exact (responseSessionPrefix_facts _ initial seen final pre run).1
    refine Noise.Product.ensures_bind _ _ session ?_
    intro seen initial out final facts run other same
    cases run
    cases same
    exact facts

/-- The sender prefix actually reaching a session carries the same all-mode
serial-indexed event, after its own successful response creation. -/
theorem outgoingResponseSessionPrefix_event (pid : PeerId) :
    Noise.Product.Ensures (outgoingResponseSessionPrefix pid) (fun _ => True)
      (fun candidate _ => ∀ cut, candidate = some cut → SessionArmEvent pid cut.session) := by
  have keep {α : Type} (action : Leanux.M α) :
      Noise.Product.Ensures action (fun _ => True) (fun _ _ => True) := by
    intro initial result final pre run
    trivial
  unfold outgoingResponseSessionPrefix
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro now
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro peer
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro ignored
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro created
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro accepted
  cases accepted with
  | false => intro initial out final pre run cut impossible; cases run; cases impossible
  | true =>
    cases created with
    | none => intro initial out final pre run; cases run
    | some msg =>
      refine Noise.Product.ensures_bind _ _ (keep _) ?_
      intro message
      have session : Noise.Product.Ensures (outgoingSessionPrefix pid) (fun _ => True)
          (fun cut _ => SessionArmEvent pid cut) := by
        apply sessionPrefix_event .respSessionBegun
        intro initial cut final pre run
        exact (outgoingSessionPrefix_facts pid initial cut final pre run).1
      refine Noise.Product.ensures_bind _ _ session ?_
      intro seen initial out final facts run cut same
      cases run
      cases same
      exact facts

end Leanux.Proofs.WG.TimerDiscipline
