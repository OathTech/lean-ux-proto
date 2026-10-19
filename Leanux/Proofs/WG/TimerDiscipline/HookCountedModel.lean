import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerClaims
import Leanux.Proofs.WG.TimerDiscipline.SessionEnqueueEffects

/-! Allocation-relative counts use the persistent session stamp. Completed
enqueue totals include only session-derived hooks with normal exits; stopped
hooks have no final wheel state, and give-up cleanup is a separate cause. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG HandshakeJournal

def CountedFacts (history : List Event) : Prop :=
  Facts history ∧ Ordered history ∧ (sessionIds history).Nodup ∧
    ∀ serial,history.countP (fun e=>e.sessionId==some serial)≤1 ∧
      history.countP (fun e=>e.derivedId==some serial)≤1 ∧
      completedSessionEnqueues history serial≤1

def CountedResult {ε α : Type}
    (result : Except ε (α × Campaign2.Product.Snapshot) × List Event) : Prop :=
  CountedFacts result.2 ∧
    match result.1 with
    | .error _ => True
    | .ok (_,last) => Frontier result.2 last.wg.keypairCounter

end Leanux.Proofs.WG.TimerDiscipline.HookCommon

