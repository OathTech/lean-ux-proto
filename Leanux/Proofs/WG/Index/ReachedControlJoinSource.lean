import Leanux.Proofs.WG.Index.ReachedControlBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedControls
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem entry_pair {α : Type} (action : RxHistory.Obs α)
    (cs : Ledger) (loans : Reservations)
    (account : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe action)
    (normal : ∀w h,Reached.Entry cs loans h w → ∀ result v,
      (runPrefix action w h).1=.ok (result,v) → Reached.Core v.wg) :
    PrefixPreserves (Reached.Entry cs loans) OwnerChecks.Safe action := by
  intro w h pre
  obtain ⟨suffix,history,safe,post⟩ := account w h pre.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error stop => trivial
  | ok pair =>
    rw [run] at post
    exact ⟨post,normal w h pre pair.1 pair.2 run⟩

theorem any_entry {α : Type} (action : RxHistory.Obs α)
    (each : ∀cs,PrefixPreserves (Reached.Entry cs []) OwnerChecks.Safe action) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe action := by
  intro w h pre
  obtain ⟨cs,pre⟩ := pre
  obtain ⟨suffix,history,safe,post⟩ := each cs w h pre
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error stop => trivial
  | ok pair =>
    rw [run] at post
    exact ⟨cs,post⟩

theorem original_pair {α : Type} (action : RxHistory.Obs α) (original : Leanux.M α)
    (erase : ErasesPrefix action original)
    (account : ∀cs,PrefixPreserves (HolderEntry.Inv cs []) OwnerChecks.Safe action)
    (normal : ∀cs w h,Reached.Entry cs [] h w → ∀ result v,
      original.run w=.ok (result,v) → Reached.Core v.wg) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe action := by
  apply any_entry action
  intro cs
  apply entry_pair action cs [] (account cs)
  intro w h pre result v run
  exact normal cs w h pre result v ((erase w h).symm.trans run)

theorem configuration_pair {α : Type} (action : RxHistory.Obs α) (original : Leanux.M α)
    (erase : ErasesPrefix action original)
    (account : ∀cs,PrefixPreserves (HolderEntry.Inv cs []) OwnerChecks.Safe action)
    (keeps : ∀cs,Preserves (fun w : World=>ConfigurationIndex.Entry cs [] w.wg) original) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe action :=
  original_pair action original erase account (fun cs w _ pre result v run=>
    ((hoare_iff_run _ _ _).mp (keeps cs) w result v (entry_configuration pre) run).2.2)

end Leanux.Proofs.WG.Index.ReachedControls
