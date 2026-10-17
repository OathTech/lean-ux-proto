import Leanux.Proofs.WG.Queues.AdmissionCaller
import Leanux.Proofs.WG.Queues.HolderInitial
import Leanux.Proofs.WG.Origins.OwnerReceive

/-! Rebase the actual admission endpoint for the already closed scheduler.
The new ledger is selected by source execution; owner history, slots and the
physical ring are joined at those identical endpoints. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionAuxiliary
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open DurableHolders AdmissionCaller

/-- Interpret the existing physical-ring observer on the same native call. -/
theorem consume_physical (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (run : ((consumeData msg src ds).run w).run a=.ok (((),v),b)) :
    ∃ nextHistory, NativeRxInv epoch (PtrRing.init n) nextHistory v := by
  let before : World := {wg:=w,ambient:=a,tasks:=Runner.initialTasks 0,fs:={}}
  let after : World := {before with wg:=v,ambient:=b}
  have lifted : (liftWG (consumeData msg src ds)).run before=.ok ((),after) := by
    rw [liftWG_run]
    simp only [before,run,Except.map]
    rfl
  have checked := consume_ring_normal (w:=before) (v:=after) physical lifted
  exact ⟨_,checked.2.2.2⟩

/-- A physical witness follows the exact selected branch, independently of
which ledger accounting is later attached to it. -/
theorem outcome_physical (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (outcome : AdmissionReceive.Outcome cs next msg src w v a b) :
    ∃ nextHistory, NativeRxInv epoch (PtrRing.init n) nextHistory v := by
  obtain ⟨choice,u,c,frontRun,tail⟩ := outcome
  have atCut := AdmissionReceive.front_physical physical frontRun
  cases choice with
  | none => obtain ⟨_,rfl,_⟩ := tail; exact ⟨history,atCut⟩
  | some ds =>
    obtain ⟨receipt,certificate⟩ := tail
    exact consume_physical atCut (AdmissionOutcome.source certificate)

/-- The original receive occurrence establishes its own next account and all
facts needed to resume the concrete scheduler at the unchanged final journal. -/
theorem receive_normal (account : Boundary cs loans w.wg)
    (physical : DecryptIteration.Physical w) (owner : OwnerChecks.Inv h w)
    (slots : CurrentSlots.Inv w.wg)
    (run : runPrefix (receive msg src) w h=(.ok ((),v),k)) :
    ∃ next, AdmissionCaller.Step cs next msg src w v h k ∧ HolderAuxiliary.Inv next loans k k v := by
  obtain ⟨epoch,n,history,ring⟩ := physical
  obtain ⟨next,step,accountOut⟩ := receive_step account (HolderAuxiliary.owner_packets owner) ring run
  obtain ⟨nextHistory,physicalOut⟩ := outcome_physical ring step.2
  have ownerOut := (OwnerReceive.wgReceive_checked msg src w h owner).choose_spec.2.2
  have ownerRun : runPrefix (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) w h=
      (.ok ((),v),k) := run
  rw [ownerRun] at ownerOut
  have native := DecryptIteration.native_normal (receive_erases msg src) run
  have slotsOut := (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.wgReceive_preserves msg src)
    w.wg w.ambient () v.wg v.ambient slots native
  exact ⟨next,step,HolderInitial.at_cut accountOut ⟨epoch,n,nextHistory,physicalOut⟩ ownerOut slotsOut⟩

/-- First apply only the old accounting cut's committed removals, then the
actual new admission. This does not assume the incoming cut is empty. -/
theorem receive_rebase (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : runPrefix (receive msg src) w h=(.ok ((),v),k)) :
    ∃ prior next, h=before++prior ∧
      AdmissionCaller.Step (remaining initial (NapiCarrier.removedPackets prior)) next msg src w v h k ∧
      HolderAuxiliary.Inv next loans k k v := by
  obtain ⟨prior,history,account⟩ := hi.1.1
  obtain ⟨next,step,after⟩ := receive_normal account hi.1.2 hi.2.1 hi.2.2 run
  exact ⟨prior,next,history,step,after⟩

/-- Stops retain the original owner's safe journal; only actual normal
returns establish a rebased dynamic funded account. -/
theorem receive_ensures (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (msg src) :
    PrefixEnsures (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (receive msg src)
      (fun _ k v => ∃ prior next, ∃ w h,
        h=before++prior ∧
        AdmissionCaller.Step (remaining initial (NapiCarrier.removedPackets prior)) next msg src w v h k ∧
        HolderAuxiliary.Inv next loans k k v) := by
  intro w h hi
  obtain ⟨suffix,history,safe,_⟩ := OwnerReceive.wgReceive_checked msg src w h hi.2.1
  refine ⟨suffix,history,safe,?_⟩
  cases actual : (runPrefix (receive msg src) w h).1 with
  | error e => trivial
  | ok out =>
    rcases out with ⟨⟨⟩,v⟩
    obtain ⟨prior,next,old,step,after⟩ := receive_rebase hi (Prod.ext actual rfl)
    exact ⟨prior,next,w,h,old,step,after⟩

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionAuxiliary
