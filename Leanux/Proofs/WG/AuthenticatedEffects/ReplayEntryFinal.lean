import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryOuter
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! Initialized refusal of an actual final-journal replay check. Coherence is
derived at that check's own native entry, including runs that stop later. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged
open Keypairs TransmitSecurity Lifetimes

theorem journal_safe (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (Journal.execute trace placeholders) []).2.filterMap Journal.replay?) := by
  have history := congrArg Prod.snd (execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [← history]
  exact initialized trace placeholders

theorem final_entry (trace : Runner.Trace) (placeholders : Bool)
    (before after : List CausalJournal.Event) (receipt : Event)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      before ++ .old (.replay receipt) :: after) :
    Inv receipt.run.before.wg ∧ receipt.Valid := by
  have projected := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at projected
  have safe := journal_safe trace placeholders
  rw [projected,position] at safe
  apply safe receipt
  simp only [List.filterMap_append,List.filterMap_cons,CausalJournal.old?,Journal.replay?]
  simp

theorem receipt_refusal (receipt : Event) (coherent : Inv receipt.run.before.wg)
    (valid : receipt.Valid) (refused : receipt.run.value = false) :
    ReplayRefusal.view receipt.run.after.wg = ReplayRefusal.view receipt.run.before.wg := by
  change (liftWG (counterValidate receipt.packet.keypair receipt.packet.nonce)).run receipt.run.before =
    .ok (receipt.run.value,receipt.run.after) at valid
  rw [refused,Framing.liftWG_run] at valid
  cases native : ((counterValidate receipt.packet.keypair receipt.packet.nonce).run receipt.run.before.wg).run receipt.run.before.ambient with
  | error stop => simp only [native,Except.map] at valid; cases valid
  | ok result =>
    obtain ⟨⟨value,v⟩,ambient⟩ := result
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    obtain ⟨rfl,after⟩ := valid
    cases device : receipt.run.before.wg.dev with
    | none =>
      simp [counterValidate,getKeypair,getDev,device,invariant,AmbientM.invariant] at native
      cases native
    | some d =>
      cases resident : d.keypairs[receipt.packet.keypair]? with
      | none =>
        simp [counterValidate,getKeypair,getDev,device,resident,invariant,AmbientM.invariant] at native
        cases native
      | some key =>
        have counter := coherent receipt.packet.keypair (cell key)
          (snapshot_lookup _ d _ key device resident)
        have same := ReplayRefusal.native_refusal _ v _ ambient _ _ d key device resident counter native
        rw [← after]
        exact same

theorem final_refusal (trace : Runner.Trace) (placeholders : Bool)
    (before after : List CausalJournal.Event) (receipt : Event)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      before ++ .old (.replay receipt) :: after) (refused : receipt.run.value = false) :
    ReplayRefusal.view receipt.run.after.wg = ReplayRefusal.view receipt.run.before.wg :=
  receipt_refusal receipt (final_entry trace placeholders before after receipt position).1
    (final_entry trace placeholders before after receipt position).2 refused

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
