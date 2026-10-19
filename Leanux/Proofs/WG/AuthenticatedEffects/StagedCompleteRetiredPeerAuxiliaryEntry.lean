import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeferredTimers
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollHistoryFrames
import Leanux.Proofs.WG.Queues.HolderTrafficEntry

/-! Outer normal entries retain the original holder/owner entry and the
exact account for identical RX carriers. A fixed-cut scheduler returns to
this boundary only through its own actual removal suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits DurableHolders

def Inv (cs : Ledger) (loans : Reservations) (h : List RxHistory.Event) (w : World) : Prop :=
  HolderEntry.Inv cs loans h w ∧ ExactBoundary cs loans w.wg

/-- Hiding history and carriers is permitted only after the paired entry
has been obtained on a native normal endpoint. -/
def Boundary (w : World) : Prop := ∃ h cs, Inv cs [] h w

theorem Inv.safe (hi : Inv cs loans h w) : OwnerChecks.Safe h := hi.1.2.safe

theorem initialized (net bare : Bool) (w : World)
    (same : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) : Inv [] [] [] w := by
  obtain ⟨holders,funded,stable⟩ := boundary_initial net bare
  have upper : Upper holders [] [] (Runner.initialWG net bare) := by
    intro owner
    cases net <;> cases bare <;> simp [balance,resident,Runner.initialWG]
  exact ⟨HolderEntry.initialized net bare w same,
    ExactBoundary.store ⟨holders,funded,upper,stable⟩ same⟩

theorem store (hi : Inv cs loans h w)
    (same : productStoreView v = productStoreView w) : Inv cs loans h v :=
  ⟨HolderEntry.store hi.1 same,
    hi.2.store (congrArg (fun p : ProductStore43 => p.2.2.2) same)⟩

theorem to_aux (hi : Inv cs loans h w) (present : w.wg.dev.isSome = true) :
    Auxiliary.Inv cs loans h h w :=
  ⟨HolderEntry.to_aux hi.1 present,ExactAt.start hi.2 h⟩

theorem of_aux (hi : Auxiliary.Inv initial loans before h w)
    (base : BaseCoherence.Inv w.wg) :
    ∃ suffix, h = before ++ suffix ∧ Inv (remaining initial (NapiCarrier.removedPackets suffix)) loans h w := by
  obtain ⟨suffix,history,entry⟩ := HolderEntry.of_aux hi.1 base
  exact ⟨suffix,history,entry,hi.residual history⟩

theorem at_cut (hi : Auxiliary.Inv cs loans h h w) (base : BaseCoherence.Inv w.wg) :
    Inv cs loans h w := by
  obtain ⟨suffix,history,entry⟩ := of_aux hi base
  have empty : suffix=[] := List.append_cancel_left (history.symm.trans (List.append_nil h).symm)
  have unchanged : remaining cs (NapiCarrier.removedPackets [])=cs :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simpa only [empty,unchanged] using entry

/-- Only the two actual crypt actors remain open. The NAPI and receive/TX
contracts are concrete native-source results. -/
def Crypt (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) : Prop :=
  Auxiliary.ExactPost initial loans before RxHistory.encryptIteration ∧
  Auxiliary.ExactPost initial loans before RxHistory.decryptIteration

theorem Crypt.actors (crypt : Crypt initial loans before) : Scheduler.Actors initial loans before :=
  ⟨crypt.1,crypt.2,Auxiliary.exact_post (ExactAt.softirq_preserves initial loans before)⟩

theorem auxiliary_normal {action : RxHistory.Obs α}
    (account : PrefixPreserves (Auxiliary.Inv cs loans h) OwnerChecks.Safe action)
    (structural : ∀ initial,PrefixPreserves (fun _ w => BaseCoherence.view w.wg=initial) (fun _ => True) action)
    (hi : Inv cs loans h w) (present : w.wg.dev.isSome=true)
    (run : runPrefix action w h=(.ok (result,v),k)) :
    ∃ suffix, k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v := by
  have post := (account w h (to_aux hi present)).choose_spec.2.2
  rw [run] at post
  exact of_aux post (HolderTrafficEntry.structure_normal structural hi.1.1.1.2.1 run)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
