import Leanux.Proofs.WG.TimerDiscipline.SessionOriginFrames
import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Std.Do

/-- The original outgoing prefix reaches its session cut without changing the
allocation serial before `beginSession`. No successful creation is assumed. -/
theorem outgoingResponseSessionPrefix_counter_origin (pid : PeerId) (counter : Nat) :
    Noise.Product.Ensures (outgoingResponseSessionPrefix pid)
      (fun g => g.wg.keypairCounter = counter)
      (fun candidate _ => ∀ cut, candidate = some cut →
        cut.session.beforeSession.wg.keypairCounter = counter) := by
  let P : World → Prop := fun g => g.wg.keypairCounter = counter
  have hpure {α : Type} (x : α) : Noise.Product.Ensures (pure x : Leanux.M α) P (fun _ => P) := by
    intro g value final pre run; cases run; exact pre
  have hlift {α : Type} (action : WG.M α)
      (frame : Noise.Ensures action (fun g => g.keypairCounter = counter)
        (fun _ g => g.keypairCounter = counter)) :
      Noise.Product.Ensures (liftWG action) P (fun _ => P) := by
    intro g value final pre run
    change ((action.run g.wg).run g.ambient >>= _) = _ at run
    cases actual : (action.run g.wg).run g.ambient with
    | error stop => rw [actual] at run; cases run
    | ok pair =>
      obtain ⟨⟨returned,current⟩,inputs⟩ := pair
      rw [actual] at run
      cases run
      exact frame g.wg g.ambient _ _ _ pre actual
  have hclock : Noise.Product.Ensures (liftWG (hiddenClock64 .respLastSent)) P (fun _ => P) :=
    hlift _ ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
      (AmbientM.hiddenClock64 .respLastSent) (fun g : WGWorld => g.keypairCounter = counter)))
  have hread : Noise.Product.Ensures (liftWG (getPeer pid)) P (fun _ => P) := by
    apply hlift
    intro g ambient value final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (fun g => g.keypairCounter = counter))
      g ambient value final after pre run).1
  have hset (p : Peer) : Noise.Product.Ensures (liftWG (setPeer pid p)) P (fun _ => P) := by
    apply hlift
    intro g ambient value final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Noise.Product.Ensures (branch site value : Leanux.M Bool) P (fun _ => P) := by
    intro g result final pre run; cases run; exact pre
  have hsession : Noise.Product.Ensures (outgoingSessionPrefix pid) P
      (fun cut _ => cut.beforeSession.wg.keypairCounter = counter) := by
    intro initial cut final pre run
    change ((liftWG (beginSession pid)).run initial >>= _) = _ at run
    cases session : (liftWG (beginSession pid)).run initial with
    | error stop => rw [session] at run; cases run
    | ok pair =>
      obtain ⟨begun,afterSession⟩ := pair
      rw [session] at run
      cases begun with
      | false => cases run; exact pre
      | true =>
        let before : World := {afterSession with ambient := {afterSession.ambient with steps := afterSession.ambient.steps.push {decision := .respSessionBegun, outcome := true, netRx := afterSession.ambient.netRxSection}}}
        change ((observed (liftWG (timersSessionDerived pid))
          (liftWG (callerJiffies .timerJiffiesSessionDerived))).run before >>= fun out =>
          .ok (⟨Campaign2.Product.snapshot initial,true,Campaign2.Product.snapshot afterSession,
            Campaign2.Product.snapshot before,some ⟨out.1.1,Campaign2.Product.snapshot out.2⟩⟩,out.2)) = .ok (cut,final) at run
        cases hook : (observed (liftWG (timersSessionDerived pid))
            (liftWG (callerJiffies .timerJiffiesSessionDerived))).run before with
        | error stop => rw [hook] at run; cases run
        | ok pair => rw [hook] at run; cases run; exact pre
  unfold outgoingResponseSessionPrefix
  refine Noise.Product.ensures_bind _ _ hclock ?_
  intro now
  refine Noise.Product.ensures_bind _ _ hread ?_
  intro peer
  refine Noise.Product.ensures_bind _ _ (hset _) ?_
  intro _
  refine Noise.Product.ensures_bind _ _ (hlift _ (createResponse_spec_counter_variant pid counter)) ?_
  intro created
  refine Noise.Product.ensures_bind _ _ (hbranch _ _) ?_
  intro accepted
  cases accepted with
  | false => intro initial out final pre run cut impossible; cases run; cases impossible
  | true =>
    cases created with
    | none => intro initial out final pre run; cases run
    | some message =>
      refine Noise.Product.ensures_bind _ _ (hlift _ (addMacToPacket_spec_counter_variant pid message counter)) ?_
      intro packet
      refine Noise.Product.ensures_bind _ _ hsession ?_
      intro session initial out final origin run cut same
      cases run
      cases same
      exact origin

end Leanux.Proofs.WG.TimerDiscipline
