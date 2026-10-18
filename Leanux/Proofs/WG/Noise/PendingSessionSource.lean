import Leanux.Proofs.WG.Noise.ConfirmationLabelSource
import Leanux.Proofs.WG.Noise.PendingTicketCallClaims
import Leanux.Proofs.WG.Origins.CurrentSessionPrefix

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

def NativeInv (w : WGWorld) (seen : List Nat) : Prop :=
  ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w ∧
    PendingTickets.Inv (PendingTickets.view w) seen

theorem native (pid : PeerId) (seen : List Nat) :
    Ensures (beginSession pid) (fun w => NativeInv w seen)
      (fun _ w => NativeInv w seen) := by
  intro w ambient result final after hi run
  have configured := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ConfiguredMaintenance.beginSession_view pid) w ambient result final after run
  have slots := (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.beginSession_preserves pid)
    w ambient result final after ⟨hi.2.1,hi.1⟩ run
  have step := PendingTickets.session_step pid (Campaign2.snapshot w ambient)
    w ambient result final after
    ⟨rfl,fun d hd => PendingTickets.nextBound w d hd hi.2.1⟩ run
  have pending := step.preserves hi.2.2
  refine ⟨?_,slots,pending⟩
  intro s hs
  exact hi.1 s (configured.symm.trans hs)

theorem observed (pid : PeerId) (seen : List Nat) :
    StatePrefixPreserves (fun _ w _ => NativeInv w seen) (fun _ => True)
      (SessionOrigin.observed pid) := by
  intro w ambient h hi
  obtain ⟨s,hs⟩ := Origins.sessionSource_appends pid w ambient h
  refine ⟨s,hs,True.intro,?_⟩
  cases hr : runPrefix ((SessionOrigin.observed pid).run w) ambient h with
  | mk result history =>
    cases result with
    | error e => trivial
    | ok out =>
      rcases out with ⟨⟨result,v⟩,ambient'⟩
      have original := (SessionOrigin.observed_erases pid w ambient h).symm.trans
        (congrArg Prod.fst hr)
      exact native pid seen w ambient result v ambient' hi original

theorem localSession (pid : PeerId) (seen : List Nat) :
    StatePrefixPreserves (fun _ w _ => NativeInv w seen) (fun _ => True)
      (Origins.localSession pid) := by
  have proof := StatePrefixEnsures.focus Origins.sessionEncode Origins.sessionDecode
    (by intro e; cases e <;> rfl) (observed pid seen)
  simpa only [Origins.localSession] using proof

theorem session_fixed (pid : PeerId) (seen : List Nat) :
    PrefixPreserves (fun _ w => NativeInv w.wg seen) (fun _ => True)
      (Origins.HistoryAdapters.session pid) := by
  have proof := PrefixEnsures.focus Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode
    Origins.HistoryAdapters.decode_encode (localSession pid seen).liftWGObserver
  simpa only [PrefixEnsures,PrefixPreserves,Origins.HistoryAdapters.session,
    Origins.HistoryAdapters.focus] using proof

theorem session_labels (pid : PeerId) (w : World) (h : List RxHistory.Event) :
    CounterConsume.confirmationLabels
      (runPrefix (Origins.HistoryAdapters.session pid) w h).2 =
    CounterConsume.confirmationLabels h := by
  exact Origins.HistoryAdapters.focus_other CounterConsume.eventLabel
    (by intro e; cases e <;> rfl) (liftWGObserver (Origins.localSession pid)) w h

def StateInv (h : List RxHistory.Event) (w : World) : Prop :=
  NativeInv w.wg (CounterConsume.confirmationLabels h).reverse

def HistorySafe (h : List RxHistory.Event) : Prop :=
  (CounterConsume.confirmationLabels h).reverse.Nodup

/-- Session receipt and lifetime events add no confirmation labels, including
on Stop. A normal endpoint retains configured identity, slot bounds and the
supplied pending-ticket invariant. This is local transport, not an initialized-run proof. -/
theorem session (pid : PeerId) :
    PrefixPreserves StateInv HistorySafe (Origins.HistoryAdapters.session pid) := by
  intro w h hi
  obtain ⟨suffix,appended,safe,normal⟩ :=
    session_fixed pid (CounterConsume.confirmationLabels h).reverse w h hi
  have labels := session_labels pid w h
  refine ⟨suffix,appended,?_,?_⟩
  · change (CounterConsume.confirmationLabels
      (runPrefix (Origins.HistoryAdapters.session pid) w h).2).reverse.Nodup
    rw [labels]
    exact hi.2.2.distinct
  · cases hr : (runPrefix (Origins.HistoryAdapters.session pid) w h).1 with
    | error e => trivial
    | ok out =>
      rw [hr] at normal
      change NativeInv out.2.wg
        (CounterConsume.confirmationLabels
          (runPrefix (Origins.HistoryAdapters.session pid) w h).2).reverse
      rw [labels]
      exact normal

end Leanux.Proofs.WG.Noise.PendingSession
