import Leanux.Proofs.WG.Noise.FreshHistoryEffects
import Leanux.Proofs.WG.Noise.FreshLifecycleSource
import Leanux.Proofs.WG.Noise.FreshInstallSource
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Noise.RotationSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG


/-- Dispatch to the original nine native calls with their complete returns. -/
def runFreshOperation (pid : PeerId) : FreshOperation → WG.M FreshReturn
  | .consume message => do return .consumed (← consumeInitiation message)
  | .respond => do return .created (← createResponse pid)
  | .beginSession => do return .begun (← beginSession pid)
  | .confirm id => do return .confirmed (← receivedWithKeypair pid id)
  | .createInitiation => do return .created (← createInitiation pid)
  | .consumeResponse message => do return .consumed (← consumeResponse message)
  | .handshakeClear => do handshakeClear pid; return .cleared
  | .expireCurrentPeerKeypairs => do expireCurrentPeerKeypairs pid; return .cleared
  | .keypairsClear => do keypairsClear pid; return .cleared

/-- Bind retains the original first Stop and does not execute later calls. -/
def runFreshSequence (pid : PeerId) : List FreshOperation → WG.M (List FreshReturn)
  | [] => pure []
  | operation :: operations => do
    let result ← runFreshOperation pid operation
    let results ← runFreshSequence pid operations
    return result :: results

/-- Actual projected reads around one original call. -/
def observedFreshOperation (pid : PeerId) (operation : FreshOperation) : WG.M FreshReceipt := do
  let before ← Campaign2.read
  let result ← runFreshOperation pid operation
  let after ← Campaign2.read
  return ⟨operation,before,result,after⟩

/-- A first Stop propagates unchanged; no successful partial receipt list is
manufactured for an interrupted execution. -/
def observedFreshSequence (pid : PeerId) : List FreshOperation → WG.M (List FreshReceipt)
  | [] => pure []
  | operation :: operations => do
    let receipt ← observedFreshOperation pid operation
    let receipts ← observedFreshSequence pid operations
    return receipt :: receipts

/-- Exact native computation equality, including full concrete final states
and every original failure. -/
theorem observedFreshOperation_erase (pid : PeerId) (operation : FreshOperation) :
    (do let receipt ← observedFreshOperation pid operation; pure receipt.result) =
      runFreshOperation pid operation := by
  simp only [observedFreshOperation,bind_assoc,pure_bind]
  funext g ambient
  change (runFreshOperation pid operation g ambient >>= fun ((result,after),inputs) =>
    Except.ok ((result,after),inputs)) = runFreshOperation pid operation g ambient
  cases runFreshOperation pid operation g ambient <;> rfl

/-- Receipt erasure preserves the full original result list, concrete state and
first Stop of the actual finite sequence. -/
theorem observedFreshSequence_erase (pid : PeerId) (operations : List FreshOperation) :
    (do let receipts ← observedFreshSequence pid operations; pure (receipts.map FreshReceipt.result)) =
      runFreshSequence pid operations := by
  induction operations with
  | nil => rfl
  | cons operation operations ih =>
    rw [runFreshSequence, ← observedFreshOperation_erase pid operation, ← ih]
    simp only [observedFreshSequence,bind_assoc,pure_bind,List.map_cons]

/-- Each original call supplies the cursor/next effect on its actual normal
return. Missing Devices/peers and all source failures retain their original
outcomes; no successful-prefix premise is supplied. -/
theorem runFreshOperation_effect (pid : PeerId) (operation : FreshOperation)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (runFreshOperation pid operation) (fun s => s = entry)
      (fun result after => FreshViewStep (freshInstallView pid entry.wg.device)
        (FreshReceipt.confirmed ⟨operation,entry,result,after⟩)
        (freshInstallView pid after.wg.device)) := by
  have mapped {α : Type} (action : WG.M α) (wrap : α → FreshReturn)
      (Q : FreshReturn → Campaign2.Snapshot → Prop)
      (fact : Campaign2.Ensures action (fun s => s = entry) (fun x s => Q (wrap x) s)) :
      Campaign2.Ensures (do let x ← action; pure (wrap x)) (fun s => s = entry) Q := by
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
  cases operation with
  | consume message =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    have preserved := consumeInitiation_spec_freshTransport_variant message pid g.dev
      g ambient result final after rfl run
    change FreshViewStep (freshInstallView pid g.dev) none (freshInstallView pid final.dev)
    rw [preserved]
    exact .same _
  | respond =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    have preserved := createResponse_spec_freshTransport_variant pid pid g.dev
      g ambient result final after rfl run
    change FreshViewStep (freshInstallView pid g.dev) none (freshInstallView pid final.dev)
    rw [preserved]
    exact .same _
  | beginSession =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    cases device : g.dev with
    | none =>
      simp [Leanux.WG.beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [Leanux.WG.beginSession,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        obtain ⟨last,finalDevice,effect⟩ := beginSession_effect pid d p g.keypairCounter resident
          g ambient result final after ⟨device,rfl⟩ run
        change FreshViewStep (freshInstallView pid g.dev) none (freshInstallView pid final.dev)
        rw [device,finalDevice]
        exact sessionEffect_freshView pid d p g.keypairCounter result last final.keypairCounter resident effect
  | confirm id =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    cases device : g.dev with
    | none =>
      simp [receivedWithKeypair,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [receivedWithKeypair,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        obtain ⟨last,finalDevice,effect⟩ := receivedWithKeypair_effect pid id d p resident
          g ambient result final after device run
        have summary := confirmationEffect_freshView pid id d p result last resident effect
        cases result <;> change FreshViewStep (freshInstallView pid g.dev) _ (freshInstallView pid final.dev)
        all_goals simpa [FreshReceipt.confirmed,device,finalDevice] using summary
  | createInitiation =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    have preserved := createInitiation_spec_freshTransport_variant pid pid g.dev
      g ambient result final after rfl run
    change FreshViewStep (freshInstallView pid g.dev) none (freshInstallView pid final.dev)
    rw [preserved]
    exact .same _
  | consumeResponse message =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    have preserved := consumeResponse_spec_freshTransport_variant message pid g.dev
      g ambient result final after rfl run
    change FreshViewStep (freshInstallView pid g.dev) none (freshInstallView pid final.dev)
    rw [preserved]
    exact .same _
  | handshakeClear =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    have preserved := handshakeClear_freshTransport pid pid g.dev
      g ambient result final after rfl run
    change FreshViewStep (freshInstallView pid g.dev) none (freshInstallView pid final.dev)
    rw [preserved]
    exact .same _
  | expireCurrentPeerKeypairs =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    have preserved := expireCurrentPeerKeypairs_freshTransport pid pid g.dev
      g ambient result final after rfl run
    change FreshViewStep (freshInstallView pid g.dev) none (freshInstallView pid final.dev)
    rw [preserved]
    exact .same _
  | keypairsClear =>
    apply mapped
    intro g ambient result final after pre run
    subst entry
    exact keypairsClear_freshView pid g.dev g ambient result final after rfl run

end Leanux.Proofs.WG.Noise
