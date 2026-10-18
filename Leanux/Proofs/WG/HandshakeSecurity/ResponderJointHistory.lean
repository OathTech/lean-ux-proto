import Leanux.Proofs.WG.HandshakeSecurity.ResponderEncryptHistory
import Leanux.Proofs.WG.Packets.PublicationRunner

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Joint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- Reuse C1's completed owner/publication invariant for actual configured
identity. Responder chronology remains an independent, same-run conjunct. -/
def Inv (h : List RxHistory.Event) (w : World) : Prop :=
  PublicationJoint.Inv h w ∧ Global.Inv h w

def Safe (h : List RxHistory.Event) : Prop := PublicationJoint.Safe h ∧ Global.Safe h
abbrev Preserves (g : RxHistory.Obs α) := PrefixPreserves Inv Safe g

theorem Inv.safe (hi : Inv h w) : Safe h := ⟨hi.1.safe, hi.2.2⟩

theorem Inv.configured (hi : Inv h w) : ConfiguredIdentity.Inv w.wg :=
  hi.1.1.current.2.1.1

theorem combine (g : RxHistory.Obs α) (inherited : PublicationJoint.Preserves g)
    (chronology : PrefixEnsures Inv Global.Safe g (fun _ => Global.Inv)) : Preserves g := by
  intro w h hi
  obtain ⟨suffix, appends, oldSafe, oldNormal⟩ := inherited w h hi.1
  obtain ⟨_, _, safe, normal⟩ := chronology w h hi
  refine ⟨suffix, appends, ⟨oldSafe, safe⟩, ?_⟩
  cases run : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [run] using oldNormal, by simpa only [run] using normal⟩

theorem from_global (g : RxHistory.Obs α) (inherited : PublicationJoint.Preserves g)
    (chronology : Global.Preserves g) : Preserves g :=
  combine g inherited (fun w h hi => chronology w h hi.2)

theorem store (h : List RxHistory.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : Inv h w) : Inv h v :=
  ⟨PublicationJoint.store h w v same hi.1, Global.store h w v same hi.2⟩

theorem initial (net bare : Bool) (w : World)
    (same : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) : Inv [] w :=
  ⟨PublicationJoint.initial net bare w same, Global.initial net bare w same⟩

theorem session_native (H1 : H1ResponderCurrentEdges) (pid : PeerId) (confirmed : List Nat) :
    Hoare (beginSession pid)
      (fun w => ConfiguredIdentity.Inv w ∧ History.Native confirmed w)
      (fun _ w => History.Native confirmed w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  exact ⟨session_authorized H1 pid confirmed w v a b result entry.2.1 entry.2.2 run,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.beginSession_preserves pid)
      w a result v b ⟨entry.2.2, entry.1⟩ run⟩

/-- The native session uses the C1 configured self-word invariant at its actual
entry. Only an initiator allocation may newly become current under H1. -/
theorem session (H1 : H1ResponderCurrentEdges) (pid : PeerId) :
    Preserves (Origins.HistoryAdapters.session pid) := by
  have inherited : PublicationJoint.Preserves (Origins.HistoryAdapters.session pid) :=
    PublicationJoint.quiet _ _ (OwnerChecks.session pid) (Appends.focus _ _ _)
      (Origins.HistoryAdapters.session_erases pid)
      (Origins.HistoryAdapters.focus_other PublicationChecks.sensitive (by intro e; cases e <;> rfl) _)
      (fun h => PublicationPoll.native_product _ _ (PublicationFrontier.beginSession_preserves pid h))
  apply combine _ inherited
  intro w h hi
  obtain ⟨suffix, appends⟩ := (Appends.focus Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode
    (liftWGObserver (Origins.localSession pid))) w h
  change (runPrefix (Origins.HistoryAdapters.session pid) w h).2 = h ++ suffix at appends
  have frame : HistoryFrame Global.consumer (Origins.HistoryAdapters.session pid) :=
    Origins.HistoryAdapters.focus_other Global.consumer (by intro e; cases e <;> rfl) _
  have empty : suffix.filterMap Global.consumer = [] := by
    have same := frame w h
    rw [appends, List.filterMap_append] at same
    simpa using same
  have safe : Global.Safe (runPrefix (Origins.HistoryAdapters.session pid) w h).2 :=
    appends ▸ hi.2.2.quiet empty
  have labels : Confirmation.completedLabels (runPrefix (Origins.HistoryAdapters.session pid) w h).2 =
      Confirmation.completedLabels h := by
    rw [Global.labels_consumer, Global.labels_consumer, frame w h]
  refine ⟨suffix, appends, safe, ?_⟩
  cases run : (runPrefix (Origins.HistoryAdapters.session pid) w h).1 with
  | error stop => trivial
  | ok out =>
    refine ⟨?_, safe⟩
    rw [labels]
    have native := (Origins.HistoryAdapters.session_erases pid w h).symm.trans run
    rw [liftWG_run] at native
    cases source : ((beginSession pid).run w.wg).run w.ambient with
    | error stop => simp [source, Except.map] at native
    | ok returned =>
      rcases returned with ⟨⟨value, world⟩, ambient⟩
      simp only [source, Except.map, Except.ok.injEq] at native
      obtain ⟨rfl, rfl⟩ := native
      exact (hoare_iff_run_ambient _ _ _).mp (session_native H1 pid _)
        w.wg w.ambient value world ambient ⟨hi.configured, hi.2.1⟩ source

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Joint
