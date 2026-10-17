import Leanux.Proofs.WG.Queues.InjectAccount
import Leanux.Proofs.WG.Queues.HolderEntry
import Leanux.Proofs.WG.Queues.BaseCoherenceCalls

/-! Complete traffic normal endpoints become the next outer entry using their
actual selected ledger. Structural coherence is transported independently from
the original source; it is not inferred from configured identity. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderTrafficEntry
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

theorem at_cut (hi : HolderAuxiliary.Inv cs loans h h w) (base : BaseCoherence.Inv w.wg) :
    HolderEntry.Inv cs loans h w := by
  obtain ⟨suffix,hist,entry⟩ := HolderEntry.of_aux hi base
  have empty : suffix=[] := List.append_cancel_left (hist.symm.trans (List.append_nil h).symm)
  have unchanged : remaining cs (NapiCarrier.removedPackets [])=cs :=
    List.filter_eq_self.mpr (fun _ _=>rfl)
  simpa only [empty,unchanged] using entry

theorem structure_normal {E α : Type} {action : PrefixM E α}
    {w v : World} {h k : List E} {result : α}
    (frame : ∀ initial, PrefixPreserves (fun _ w=>BaseCoherence.view w.wg=initial) (fun _=>True) action)
    (base : BaseCoherence.Inv w.wg) (run : runPrefix action w h=(.ok (result,v),k)) :
    BaseCoherence.Inv v.wg := by
  have post := (BaseCoherence.coherence_of_structure frame w h base).choose_spec.2.2
  simpa only [run] using post

/-- Inject's admission ledger remains in its source outcome; the next outer
entry uses the empty ledger established by the actual final drain guard. -/
theorem inject_normal (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k)) :
    ∃ admitted,InjectAccount.Outcome cs admitted family port msg tos ll dest w v h k result ∧
      HolderEntry.Inv [] loans k v ∧ result=(msg.length : Int) ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket),v.wg.dev=some d→d.rxSkbs[id]?≠some packet) := by
  obtain ⟨admitted,outcome,account,length,empty⟩ :=
    InjectAccount.normal hi.1.1.1 hi.1.2.1 hi.2 hi.1.2.2 run
  have base := structure_normal (fun initial=>BaseCoherence.inject_structure initial family port msg tos ll dest)
    hi.1.1.2.1 run
  exact ⟨admitted,outcome,at_cut account base,length,empty⟩

theorem flood_normal (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix (RxHistory.flood count port family input) w h=(.ok (result,v),k)) :
    ∃ next,FloodAccount.Outcome cs next count port family input w v h k result ∧
      HolderEntry.Inv next loans k v := by
  obtain ⟨next,outcome,account⟩ := FloodAccount.normal hi.1.1.1 hi.1.2.1 hi.2 hi.1.2.2 run
  have base := structure_normal (fun initial=>BaseCoherence.flood_structure initial count port family input)
    hi.1.1.2.1 run
  exact ⟨next,outcome,at_cut account base⟩

theorem batch_normal (entries : List Env.BatchItem) (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix (RxHistory.batch entries) w h=(.ok (result,v),k)) :
    ∃ next,BatchAccount.Outcome cs next entries w v h k result ∧ HolderEntry.Inv next loans k v := by
  obtain ⟨next,outcome,account⟩ := BatchAccount.normal hi.1.1.1 hi.1.2.1 hi.2 hi.1.2.2 run
  have base := structure_normal (fun initial=>BaseCoherence.batch_structure initial entries) hi.1.1.2.1 run
  exact ⟨next,outcome,at_cut account base⟩

/-- A fixed-cut call returns exactly the ledger remaining after its actual
fresh removal suffix. Its source structural frame supplies the next entry. -/
theorem auxiliary_normal {action : RxHistory.Obs α}
    (account : ∀ initial loans before,PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe action)
    (structural : ∀ initial,PrefixPreserves (fun _ w=>BaseCoherence.view w.wg=initial) (fun _=>True) action)
    (hi : HolderEntry.Inv cs loans h w) (present : w.wg.dev.isSome=true)
    (run : runPrefix action w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v := by
  have post := (account cs loans h w h (HolderEntry.to_aux hi present)).choose_spec.2.2
  rw [run] at post
  exact HolderEntry.of_aux post (structure_normal structural hi.1.1.2.1 run)

end Leanux.Proofs.WG.Queues.RxCredits.HolderTrafficEntry
