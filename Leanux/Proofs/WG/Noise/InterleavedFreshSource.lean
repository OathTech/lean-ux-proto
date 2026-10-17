import Leanux.Proofs.WG.Noise.InterleavedFreshEffects
import Leanux.Proofs.WG.Noise.FreshHistorySource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Execute the existing native operation for each supplied actor, in order.
Every original Stop propagates before any later operation is evaluated. -/
def runInterleavedFreshSequence : List InterleavedFreshOperation → WG.M (List FreshReturn)
  | [] => pure []
  | (actor,operation) :: operations => do
    let result ← runFreshOperation actor operation
    let results ← runInterleavedFreshSequence operations
    return result :: results

/-- The existing whole-operation receipt is retained with its actual actor. -/
def observedInterleavedFreshSequence : List InterleavedFreshOperation → WG.M (List InterleavedFreshReceipt)
  | [] => pure []
  | (actor,operation) :: operations => do
    let receipt ← observedFreshOperation actor operation
    let receipts ← observedInterleavedFreshSequence operations
    return ⟨actor,receipt⟩ :: receipts

/-- Erasure keeps the exact original native results, concrete states and first
Stop. Observation introduces no successful-prefix premise. -/
theorem observedInterleavedFreshSequence_erase (operations : List InterleavedFreshOperation) :
    (do let receipts ← observedInterleavedFreshSequence operations
        pure (receipts.map fun receipt => receipt.call.result)) = runInterleavedFreshSequence operations := by
  induction operations with
  | nil => rfl
  | cons operation operations ih =>
    obtain ⟨actor,operation⟩ := operation
    rw [runInterleavedFreshSequence,← observedFreshOperation_erase actor operation,← ih]
    simp only [observedInterleavedFreshSequence,bind_assoc,pure_bind,List.map_cons]

/-- Every actor executes the original operation. Foreign session allocation is
the only new tracked-view transition; other foreign calls preserve its view.
Reference/slot aliases and all normal-refusal and Stop branches are retained. -/
theorem runFreshOperation_interleaved_effect (tracked actor : PeerId) (operation : FreshOperation)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (runFreshOperation actor operation) (fun s => s = entry)
      (fun result after => InterleavedFreshStep (freshInstallView tracked entry.wg.device)
        (InterleavedFreshReceipt.confirmed tracked ⟨actor,⟨operation,entry,result,after⟩⟩)
        (freshInstallView tracked after.wg.device)) := by
  by_cases same : actor = tracked
  · subst actor
    intro g ambient result final after pre run
    simpa only [InterleavedFreshReceipt.confirmed,ite_true] using
      InterleavedFreshStep.localStep (runFreshOperation_effect tracked operation entry
        g ambient result final after pre run)
  simp only [InterleavedFreshReceipt.confirmed,ite_eq_right same]
  have mapped {α : Type} (action : WG.M α) (wrap : α → FreshReturn)
      (fact : Campaign2.Ensures action (fun s => s = entry)
        (fun _ after => InterleavedFreshStep (freshInstallView tracked entry.wg.device) none
          (freshInstallView tracked after.wg.device))) :
      Campaign2.Ensures (do let x ← action; pure (wrap x)) (fun s => s = entry)
        (fun _ after => InterleavedFreshStep (freshInstallView tracked entry.wg.device) none
          (freshInstallView tracked after.wg.device)) := by
    intro g ambient result final after pre run
    change ((action.run g).run ambient >>= fun ((x,next),inputs) =>
      Except.ok ((wrap x,next),inputs)) = _ at run
    cases actual : (action.run g).run ambient with
    | error stop => rw [actual] at run; cases run
    | ok out =>
      obtain ⟨⟨x,next⟩,inputs⟩ := out
      rw [actual] at run
      cases run
      exact fact g ambient x _ _ pre actual
  have unchanged {α : Type} (action : WG.M α)
      (frame : Ensures action (FreshTransport tracked entry.wg.device)
        (fun _ => FreshTransport tracked entry.wg.device)) :
      Campaign2.Ensures action (fun s => s = entry)
        (fun _ after => InterleavedFreshStep (freshInstallView tracked entry.wg.device) none
          (freshInstallView tracked after.wg.device)) := by
    intro g ambient result final after pre run
    subst entry
    have view := frame g ambient result final after rfl run
    change freshInstallView tracked final.dev = freshInstallView tracked g.dev at view
    change InterleavedFreshStep _ none (freshInstallView tracked final.dev)
    rw [view]
    exact .localStep (.same _)
  cases operation with
  | consume message => exact mapped _ _ (unchanged _
      (consumeInitiation_spec_freshTransport_variant message tracked entry.wg.device))
  | respond => exact mapped _ _ (unchanged _
      (createResponse_spec_freshTransport_variant actor tracked entry.wg.device))
  | createInitiation => exact mapped _ _ (unchanged _
      (createInitiation_spec_freshTransport_variant actor tracked entry.wg.device))
  | consumeResponse message => exact mapped _ _ (unchanged _
      (consumeResponse_spec_freshTransport_variant message tracked entry.wg.device))
  | handshakeClear => exact mapped _ _ (unchanged _
      (handshakeClear_freshTransport actor tracked entry.wg.device))
  | expireCurrentPeerKeypairs => exact mapped _ _ (unchanged _
      (expireCurrentPeerKeypairs_freshTransport actor tracked entry.wg.device))
  | beginSession =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    cases device : g.dev with
    | none =>
      simp [Leanux.WG.beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[actor]? with
      | none =>
        simp [Leanux.WG.beginSession,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        obtain ⟨last,finalDevice,effect⟩ := beginSession_effect actor d p g.keypairCounter resident
          g ambient result final after ⟨device,rfl⟩ run
        change InterleavedFreshStep (freshInstallView tracked g.dev) none (freshInstallView tracked final.dev)
        rw [device,finalDevice]
        exact sessionEffect_other_freshView actor tracked same d p g.keypairCounter result last final.keypairCounter effect
  | confirm id =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    cases device : g.dev with
    | none =>
      simp [receivedWithKeypair,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[actor]? with
      | none =>
        simp [receivedWithKeypair,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        obtain ⟨last,finalDevice,effect⟩ := receivedWithKeypair_effect actor id d p resident
          g ambient result final after device run
        have view : freshInstallView tracked (some last) = freshInstallView tracked (some d) := by
          by_cases matched : p.keypairNext = some id
          · simp only [ConfirmationEffect,matched,ite_true] at effect
            obtain ⟨rfl,steps⟩ := effect
            have peer := rotationRun_other_peer same steps
            have cursor := Index.rotationRun_allocation_cursor steps
            simp [freshInstallView,peer,cursor]
          · simp only [ConfirmationEffect,matched,ite_false] at effect
            obtain ⟨_,rfl⟩ := effect
            rfl
        change InterleavedFreshStep (freshInstallView tracked g.dev) none (freshInstallView tracked final.dev)
        rw [device,finalDevice,view]
        exact .localStep (.same _)
  | keypairsClear =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    cases device : g.dev with
    | none =>
      simp [keypairsClear,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[actor]? with
      | none =>
        simp [keypairsClear,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        obtain ⟨last,finalDevice,steps⟩ := keypairsClear_effect actor d p resident
          g ambient result final after device run
        have peer := clearRun_other_peer same steps
        have cursor := clearRun_allocation_cursor steps
        change InterleavedFreshStep (freshInstallView tracked g.dev) none (freshInstallView tracked final.dev)
        rw [device,finalDevice]
        simp only [freshInstallView,Option.map_some,Option.bind_some,peer,cursor]
        exact .localStep (.same _)

end Leanux.Proofs.WG.Noise
