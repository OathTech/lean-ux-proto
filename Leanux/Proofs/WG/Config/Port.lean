import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.Validation
import Leanux.Proofs.WG.Roaming.Basic

set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

theorem setPort_down (port old : Nat) (sock4 sock6 : Option Nat) :
    Ensures (setPort port)
      (fun g => portState g = some (old, sock4, sock6, false))
      (fun ret g => ret = 0 ∧ portState g = some (port, sock4, sock6, false)) := by
  let Q : WGWorld → Prop := fun g => portState g = some (old, sock4, sock6, false)
  let body := fun (pid : PeerId) (_ : Unit) => do
    _ ← branch .setPortPeerIter true
    clearPeerEndpointSrc pid
    pure (ForInStep.yield ())
  have loop (pids : List PeerId) : Ensures (forIn pids () body) Q (fun _ => Q) := by
    induction pids with
    | nil =>
      intro g ambient result final after pre run
      cases run
      exact pre
    | cons pid rest ih =>
      simp only [List.forIn_cons, body, bind_assoc]
      refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
      · exact (ensures_iff _ _ _).mpr
          (hoare_liftAmbient_variant (AmbientM.branch .setPortPeerIter true) Q)
      · intro _
        refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
        · exact (ensures_iff _ _ _).mpr (clearPeerEndpointSrc_port_spec pid _)
        · intro _
          exact ih
  intro g ambient result final after pre run
  cases device : g.dev with
  | none => simp [portState, device] at pre
  | some d =>
    have fields : d.incomingPort = old ∧ d.sock4 = sock4 ∧ d.sock6 = sock6 ∧ d.running = false := by
      simpa [portState, device] using pre
    by_cases same : d.incomingPort = port
    · simp [setPort, getDev, device, branch, AmbientM.branch, same] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, by simpa [← same, fields.1] using pre⟩
    · let tail : WG.M Int := do
        let _ ← forIn d.peerList () body
        _ ← branch .setPortPeerIter false
        _ ← branch .setPortNotRunning true
        modifyDev fun d => {d with incomingPort := port}
        pure 0
      have contract : Ensures tail Q
          (fun ret g => ret = 0 ∧ portState g = some (port, sock4, sock6, false)) := by
        unfold tail
        refine ensures_bind (Q := fun _ => Q) _ _ (loop d.peerList) ?_
        intro _
        refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
        · exact (ensures_iff _ _ _).mpr
            (hoare_liftAmbient_variant (AmbientM.branch .setPortPeerIter false) Q)
        · intro _
          refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
          · exact (ensures_iff _ _ _).mpr
              (hoare_liftAmbient_variant (AmbientM.branch .setPortNotRunning true) Q)
          · intro _ g ambient result final after pre run
            simp [modifyDev] at run
            rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
            refine ⟨rfl, ?_⟩
            cases hd : g.dev with
            | none => simp [Q, portState, hd] at pre
            | some d =>
              have parts : d.incomingPort = old ∧ d.sock4 = sock4 ∧ d.sock6 = sock6 ∧ d.running = false := by
                simpa [Q, portState, hd] using pre
              simp [portState, parts.2]
      let before := {ambient with steps := ambient.steps.push {
        decision := .setPortSame, outcome := false, netRx := ambient.netRxSection}}
      have sameB : (d.incomingPort == port) = false := by simp [same]
      have source : ((setPort port).run g).run ambient = (tail.run g).run before := by
        simp [setPort, getDev, device, branch, AmbientM.branch, same, sameB, fields.2.2.2,
          tail, body, before]
      exact contract g before result final after pre (source.symm.trans run)

end Leanux.Proofs.WG.Config
