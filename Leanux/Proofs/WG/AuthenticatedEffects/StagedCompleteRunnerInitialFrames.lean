import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerFrames

/-! Initialization factors are the original prefill and routing boot.
They change no event history, including when their actual native guard stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits RetirementSecurity
variable {E α : Type}

theorem prefill_factor (count : Nat) (w : World) (next : World → PrefixOuter E α) :
    ConservationRunner.prefillWith count w next =
      (ConservationRunner.prefillWith count w (pure : World → PrefixOuter E World) >>= next) := by
  unfold ConservationRunner.prefillWith
  split
  · split <;> rfl
  · rfl

theorem boot_factor (net foreign : Bool) (w : World) (next : World → PrefixOuter E α) :
    ConservationRunner.bootWith net foreign w next =
      (ConservationRunner.bootWith net foreign w (pure : World → PrefixOuter E World) >>= next) := by
  unfold ConservationRunner.bootWith
  split
  · split <;> rfl
  · rfl

theorem prefill_quiet (count : Nat) (w : World) :
    Quiet (ConservationRunner.prefillWith count w (pure : World → PrefixOuter E World)) := by
  unfold ConservationRunner.prefillWith
  split
  · split <;> intro h <;> rfl
  · intro h; rfl

theorem boot_quiet (net foreign : Bool) (w : World) :
    Quiet (ConservationRunner.bootWith net foreign w (pure : World → PrefixOuter E World)) := by
  unfold ConservationRunner.bootWith
  split
  · split <;> intro h <;> rfl
  · intro h; rfl

theorem prefill_store (count : Nat) (w v : World) {h : List E}
    (run : runPrefixOuter (ConservationRunner.prefillWith count w
      (pure : World → PrefixOuter E World)) h=(.ok v,h)) :
    wgStoreView v.wg=wgStoreView w.wg := by
  unfold ConservationRunner.prefillWith at run
  split at run
  · split at run
    · cases run; rfl
    · cases run
  · cases run; rfl

theorem boot_store (net foreign : Bool) (w v : World) {h : List E}
    (run : runPrefixOuter (ConservationRunner.bootWith net foreign w
      (pure : World → PrefixOuter E World)) h=(.ok v,h)) :
    wgStoreView v.wg=wgStoreView w.wg := by
  unfold ConservationRunner.bootWith at run
  split at run
  · split at run
    · rename_i result actual
      cases run
      exact (ProjectedAction.iff_run _ _ _).mp
        ((pinned_const _private.Leanux.Proofs.WG.Queues.ConservationRunner.«0».Leanux.Proofs.WG.Queues.RxCredits.ConservationRunner.boot_store) foreign)
        w _ result actual
    · cases run
  · cases run; rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
