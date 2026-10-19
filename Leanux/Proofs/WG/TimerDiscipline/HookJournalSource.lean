import Leanux.Proofs.WG.TimerDiscipline.HookJournalBridge
import Leanux.Proofs.Logged.WGPrefix

/-! Execute the original hook once and append its exact result on either success or Stop. Earlier history is retained. This leaf adapter introduces no caller or scheduler traversal. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal
open Leanux Leanux.WG Leanux.Proofs.Logged

def observed (hook : Hook) (pid : PeerId) : WGPrefix Receipt Unit :=
  fun g ambient => ExceptT.mk fun history =>
    let outcome := ((action hook pid).run g).run ambient
    (outcome,history ++ [⟨hook,pid,Campaign2.snapshot g ambient,
      Campaign2.observeResult outcome⟩])

theorem observed_exact (hook : Hook) (pid : PeerId) (g : WGWorld)
    (ambient : Ambient) (history : List Receipt) :
    runWGPrefix (observed hook pid) g ambient history =
      (((action hook pid).run g).run ambient,
       history ++ [⟨hook,pid,Campaign2.snapshot g ambient,
        Campaign2.observeResult (((action hook pid).run g).run ambient)⟩]) := rfl

theorem observed_erases (hook : Hook) (pid : PeerId) :
    ErasesStatePrefix (observed hook pid) (action hook pid) := by
  intro g ambient history
  rfl

theorem observed_appends (hook : Hook) (pid : PeerId) :
    StateAppends (observed hook pid) := by
  intro g ambient history
  exact ⟨[_],rfl⟩

theorem observed_preserves (hook : Hook) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (observed hook pid) := by
  intro g ambient history prior
  have valid := prior.snoc (fresh_valid hook pid g ambient)
  refine ⟨[_],rfl,valid,?_⟩
  dsimp only [runPrefix,observed,StateT.run,ExceptT.run,ExceptT.mk]
  cases hr : action hook pid g ambient with
  | error _ => trivial
  | ok out => rcases out with ⟨⟨value,current⟩,inputs⟩; simpa only [StateT.run,hr] using valid

end Leanux.Proofs.WG.TimerDiscipline.HookJournal
