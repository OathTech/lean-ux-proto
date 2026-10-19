import Leanux.Proofs.WG.RetirementSecurity.TxWorkRunner

/-! Normal returned-world TX service follows from the original initialized
runner prefix, operation loop and finish guards. Acceptance supplies these
source facts; no caller invariant or fair-drain assumption remains. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork.Runner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem prefill_source {E α : Type} (count : Nat) (w : World) (next : World→PrefixOuter E α) {h k : List E} {result : α}
    (run : runPrefixOuter (ConservationRunner.prefillWith count w next) h=(.ok result,k)) :
    ∃v,runPrefixOuter (ConservationRunner.prefillWith count w (pure : World→PrefixOuter E World)) h=(.ok v,h) ∧
      runPrefixOuter (next v) h=(.ok result,k) := by
  unfold ConservationRunner.prefillWith at run
  split at run
  · rename_i positive
    split at run
    · rename_i out actual
      exact ⟨_,by simp only [ConservationRunner.prefillWith,positive,↓reduceIte,actual]; rfl,run⟩
    · cases run
  · rename_i negative
    exact ⟨w,by simp only [ConservationRunner.prefillWith,negative,↓reduceIte]; rfl,run⟩

theorem boot_source {E α : Type} (net foreign : Bool) (w : World) (next : World→PrefixOuter E α) {h k : List E} {result : α}
    (run : runPrefixOuter (ConservationRunner.bootWith net foreign w next) h=(.ok result,k)) :
    ∃v,runPrefixOuter (ConservationRunner.bootWith net foreign w (pure : World→PrefixOuter E World)) h=(.ok v,h) ∧
      runPrefixOuter (next v) h=(.ok result,k) := by
  unfold ConservationRunner.bootWith at run
  split at run
  · rename_i enabled
    split at run
    · rename_i out actual
      exact ⟨_,by simp only [ConservationRunner.bootWith,enabled,↓reduceIte,actual]; rfl,run⟩
    · cases run
  · rename_i disabled
    exact ⟨w,by simp only [ConservationRunner.bootWith,disabled]; rfl,run⟩

theorem finish_world {E : Type} (trace : Trace) (state : RunnerOperation.State) {h k : List E} {result : Lean.Json} {w : World}
    (run : runPrefixOuter (RunnerOperation.finishWith (fun j v=>(j,v)) trace state) (h : List E)=
      (.ok (result,w),k)) : w=state.1 := by
  unfold RunnerOperation.finishWith at run
  dsimp only at run
  split at run
  · cases run
  · split at run
    · cases run
    · cases run
      rfl

theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) : Inv w := by
  unfold RunnerAccount.observed at run
  rw [ConservationRunner.initialized_factor] at run
  obtain ⟨u,prefill,rest⟩:=prefill_source trace.seccompPrefill (ConservationRunner.fixture trace placeholders) _ run
  obtain ⟨v,boot,tail⟩:=boot_source trace.net trace.foreign u _ rest
  rw [RunnerOperation.tail_factor] at tail
  obtain ⟨state,j,loop,finished⟩:=RunnerOperation.bind_normal tail
  rw [←Array.forIn_toList] at loop
  have ready:=list trace trace.ops.toList (v,#[],#[],#[],#[],#[])
    (initial trace placeholders prefill boot) loop
  exact (finish_world trace state finished).symm ▸ ready

/-- Successful executable acceptance supplies queue-only service at the
returned world and the actual empty suspended list, including an empty trace. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h,runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h) ∧ Inv w := by
  obtain ⟨w,h,_,source,_,_⟩:=RunnerAccount.accepted trace placeholders run
  exact ⟨w,h,source,normal trace placeholders source⟩

end Leanux.Proofs.WG.RetirementSecurity.TxWork.Runner
