import Leanux.Proofs.WG.TimerDiscipline.EpisodeJournalBridge
import Leanux.Proofs.WG.Noise.DriverTagDeferredSource

/-! Execute the existing exact episode observer once and append its outcome on either success or Stop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
def call (bound : UInt64) : PrefixM Receipt Bool :=
  fun entry => ExceptT.mk fun history =>
    let out := (observedRunTimersEpisode bound).run entry
    (out.map (fun (result,final)=>(result.2,final)),
      history ++ [⟨bound,Campaign2.Product.snapshot entry,Campaign2.Product.observeResult out⟩])

theorem call_exact (bound : UInt64) (entry : World) (history : List Receipt) :
    runPrefix (call bound) entry history =
      ((Env.runTimers bound).run entry,
       history ++ [⟨bound,Campaign2.Product.snapshot entry,
         Campaign2.Product.observeResult ((observedRunTimersEpisode bound).run entry)⟩]) := by
  change (((observedRunTimersEpisode bound).run entry).map
    (fun (out : (OuterTimerEpisodeReceipt × Bool) × World)=>(out.1.2,out.2)),_) = _
  have eq := congrArg (fun (a : Leanux.M Bool)=>a.run entry) (observedRunTimersEpisode_erase bound)
  rw [←eq,StateT.run_bind]
  cases (observedRunTimersEpisode bound).run entry <;> rfl

theorem call_erases (bound : UInt64) : ErasesPrefix (call bound) (Env.runTimers bound) := by
  intro entry history
  exact congrArg Prod.fst (call_exact bound entry history)

theorem fresh_valid (bound : UInt64) (entry : World) :
    Valid ⟨bound,Campaign2.Product.snapshot entry,
      Campaign2.Product.observeResult ((observedRunTimersEpisode bound).run entry)⟩ := by
  refine ⟨⟨entry,rfl,rfl⟩,?_⟩
  cases actual : (observedRunTimersEpisode bound).run entry with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨episode,result⟩,final⟩:=out
    exact runTimers_episode_receipt bound (Campaign2.Product.snapshot entry)
      entry (episode,result) final rfl actual

theorem call_preserves (bound : UInt64) :
    PrefixPreserves (fun history _=>ValidHistory history) ValidHistory (call bound) := by
  intro entry history prior
  let receipt : Receipt := ⟨bound,Campaign2.Product.snapshot entry,
    Campaign2.Product.observeResult ((observedRunTimersEpisode bound).run entry)⟩
  have valid : ValidHistory (history++[receipt]) := by
    intro r member
    rcases List.mem_append.mp member with old | fresh
    · exact prior r old
    · simp only [List.mem_singleton] at fresh
      subst r
      exact fresh_valid bound entry
  refine ⟨[receipt],?_,?_,?_⟩
  · rw [call_exact]
  · rw [call_exact]; exact valid
  · rw [call_exact]
    cases (Env.runTimers bound).run entry with
    | error stop => trivial
    | ok out => exact valid

end Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
