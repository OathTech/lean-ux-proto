import Leanux.Proofs.WG.Roaming.InitiationCryptoEffects

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original consumer's exit helper, including its failed reference put. -/
def initiationOut (peer ret : Option PeerId) : WG.M (Option PeerId) := do
  if ← branch .consumeFailedPut ret.isNone then peerPut peer
  return ret

theorem initiationOut_effect (peer ret : Option PeerId) (P : WGWorld → Prop) :
    Ensures (initiationOut peer ret) P
      (fun result g => result = ret ∧ (ret.isSome = true → P g)) := by
  intro g ambient result final after pre run
  cases ret with
  | none =>
    let marked := {ambient with steps := ambient.steps.push {
      decision := .consumeFailedPut, outcome := true, netRx := ambient.netRxSection}}
    change (((peerPut peer).run g).run marked >>= fun ((_, current), last) =>
      Except.ok ((none, current), last)) = .ok ((result, final), after) at run
    cases put : ((peerPut peer).run g).run marked with
    | error err => rw [put] at run; cases run
    | ok pair =>
      rcases pair with ⟨⟨value, current⟩, last⟩
      rw [put] at run
      cases run
      exact ⟨rfl, by simp⟩
  | some pid =>
    simp [initiationOut, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, fun _ => pre⟩

namespace Product

/-- Retain arbitrary relations across every former Kernel owner. A successful
exit preserves them; a rejected exit keeps its original reference put. -/
theorem initiationOut_effect (peer ret : Option PeerId)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Noise.Product.Ensures (liftWG (Roaming.initiationOut peer ret))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun result w => result = ret ∧ (ret.isSome = true → P w.wg w.fs w.tasks w.seccomp)) := by
  intro w result final pre run
  dsimp only [liftWG, StateT.run, Bind.bind, Pure.pure, Except.bind, Except.pure] at run
  cases native : ((Roaming.initiationOut peer ret).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at native; rw [native] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨value, current⟩, after⟩
    simp only [StateT.run] at native
    rw [native] at run
    cases run
    exact Roaming.initiationOut_effect peer ret (fun g => P g w.fs w.tasks w.seccomp)
      w.wg w.ambient value current after pre native

end Product
end Leanux.Proofs.WG.Roaming
