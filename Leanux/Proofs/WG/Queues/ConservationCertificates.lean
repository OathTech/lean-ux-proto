import Leanux.Proofs.WG.Queues.ConservationSource
import Leanux.Proofs.WG.Queues.HolderEntry

/-! Concrete input-to-certificate adapters. The source relation is constructed
from the actual normal run, independently of any funded-output premise. These
local adapters do not yet establish a whole initialized Runner relation. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ConservationCertificates
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open DurableHolders

/-- A real physical witness is needed at this unguarded native receive cut. -/
theorem receive (hi : HolderEntry.Inv cs loans h w) (physical : DecryptIteration.Physical w)
    (run : runPrefix (AdmissionCaller.receive msg src) w h=(.ok ((),v),k)) :
    ∃ next,(ConservationSource.receive msg src).relation cs w h () v k next ∧
      HolderAuxiliary.Inv next loans k k v := by
  obtain ⟨next,step,after⟩ := AdmissionAuxiliary.receive_normal
    hi.1.1.1 physical hi.2 hi.1.2.2 run
  exact ⟨next,⟨rfl,step⟩,after⟩

/-- A poll's ledger is determined without an accounting premise. -/
theorem poll (run : runPrefix (RxHistory.observePoll pid budget) w h=(.ok (count,v),k)) :
    ∃ next,(ConservationSource.poll pid budget).relation cs w h count v k next := by
  obtain ⟨suffix,hist⟩ := RxHistory.observePoll_appends pid budget w h
  exact ⟨_,run,suffix,by simpa only [run] using hist,rfl⟩

/-- Flood uses its own device guard, so optional physical absence is allowed
at the incoming boundary. Its actual residual ledger is retained. -/
theorem flood (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix (RxHistory.flood count port family messages) w h=(.ok (result,v),k)) :
    ∃ next,(ConservationSource.flood count port family messages).relation cs w h result v k next ∧
      HolderAuxiliary.Inv next loans k k v := by
  exact FloodAccount.normal hi.1.1.1 hi.1.2.1 hi.2 hi.1.2.2 run

private theorem finish_preserves (msg : List UInt8) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (InjectAccount.finish msg) := by
  unfold InjectAccount.finish
  apply PrefixPreserves.bind (HolderAuxDeferred.crypt initial loans before)
  intro _
  apply PrefixPreserves.bind
    (viewLiftPrefix_preserves productStoreView (I:=HolderAuxiliary.Inv initial loans before) (S:=OwnerChecks.Safe) (fun _ _ hi => hi.2.1.safe)
      (fun _ _ _ same hi => HolderAuxiliary.store hi same)
      (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  apply PrefixPreserves.bind (HolderAuxDeferred.drained initial loans before _ _)
  intro _
  exact PrefixPreserves.pure (fun _ _ hi => hi.2.1.safe) _

/-- The output ledger is the admission ledger minus exactly this finish's
fresh removal suffix. It is not the intermediate `next` of InjectAccount. -/
theorem inject (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k)) :
    ∃ next,(ConservationSource.inject family port msg tos ll dest).relation cs w h result v k next ∧
      HolderAuxiliary.Inv next loans k k v := by
  obtain ⟨admitted,outcome,_,_,_⟩ := InjectAccount.normal
    hi.1.1.1 hi.1.2.1 hi.2 hi.1.2.2 run
  obtain ⟨src,u,t,j,start,step,done⟩ := outcome
  have store := InjectAccount.front_store start
  have dev : u.wg.dev=w.wg.dev := congrArg (fun p : ProductStore43=>p.2.2.2.dev) store
  have physical : HolderDeviceCreate.OptionalPhysical u.wg := by
    simpa only [HolderDeviceCreate.OptionalPhysical,NativeRxInv,RxRing.nativeCell,dev] using hi.1.2.1
  have slots := CurrentSlots.fields_transport hi.1.2.2
    (congrArg (fun d : Option Device=>CurrentSlots.fields {dev:=d}) dev)
  have entry := HolderInitial.at_cut
    (HolderInitial.store hi.1.1.1 (congrArg (fun p : ProductStore43=>p.2.2.2) store))
    (HolderInitial.physical_present physical (InjectAccount.front_present start))
    (OwnerWorkers.store h w u store hi.2) slots
  obtain ⟨prior,derived,old,other,after⟩ := AdmissionSection.normal entry step.source
  have noPrior : prior=[] := by
    have length := congrArg List.length old
    simp only [List.length_append] at length
    cases prior with
    | nil => rfl
    | cons x xs => simp only [List.length_cons] at length; omega
  have sameInitial : remaining cs (NapiCarrier.removedPackets prior)=cs := by
    subst prior
    exact List.filter_eq_self.mpr (fun _ _=>rfl)
  rw [sameInitial] at other
  have sameLedger := step.unique other
  subst derived
  have final := (finish_preserves msg t j after).choose_spec.2.2
  rw [done] at final
  obtain ⟨suffix,hist,rebase⟩ := HolderInitial.rebase final
  exact ⟨_,⟨src,u,t,j,admitted,suffix,start,step,done,hist,rfl⟩,rebase⟩

/-- Each actual batch item contributes its own ordered source certificate;
the complete original observer chooses the residual ledger. -/
theorem batch (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix (RxHistory.batch entries) w h=(.ok (result,v),k)) :
    ∃ next,(ConservationSource.batch entries).relation cs w h result v k next ∧
      HolderAuxiliary.Inv next loans k k v :=
  BatchAccount.normal hi.1.1.1 hi.1.2.1 hi.2 hi.1.2.2 run

/-- Crypt's live accounting cut selects precisely the fresh removals and
rebases at the original final history. No receive callback premise remains. -/
theorem crypt (hi : HolderAuxiliary.Inv cs loans h h w)
    (run : runPrefix RxHistory.runCryptWorkers w h=(.ok ((),v),k)) :
    ∃ next,ConservationSource.crypt.relation cs w h () v k next ∧
      HolderAuxiliary.Inv next loans k k v := by
  have post := (HolderAuxDeferred.crypt cs loans h w h hi).choose_spec.2.2
  rw [run] at post
  obtain ⟨suffix,hist,after⟩ := HolderInitial.rebase post
  exact ⟨_,⟨run,suffix,hist,rfl⟩,after⟩

/-- Both recorded and placeholder paths retain their actual residual ledger.
Normal placeholder completion is not silently equated with an empty account. -/
theorem afterBatch (hi : HolderAuxiliary.Inv cs loans h h w)
    (run : runPrefix RxHistory.afterBatch w h=(.ok ((),v),k)) :
    ∃ next,ConservationSource.afterBatch.relation cs w h () v k next ∧
      HolderAuxiliary.Inv next loans k k v := by
  have post := (HolderAfterBatch.afterBatch cs loans h w h hi).choose_spec.2.2
  rw [run] at post
  obtain ⟨suffix,hist,after⟩ := HolderInitial.rebase post
  exact ⟨_,⟨run,suffix,hist,rfl⟩,after⟩

private theorem empty_inventory (inventory : Inventory cs w)
    (empty : ∀ (d : Device) (id : SkbId) (packet : RxPacket),w.dev=some d → d.rxSkbs[id]?≠some packet) : cs=[] := by
  cases cs with
  | nil => rfl
  | cons c tail =>
    obtain ⟨_,pkt,found,_⟩ := inventory.present c (List.mem_cons_self ..)
    cases hd:w.dev with
    | none => simp [packetAt,hd] at found
    | some d =>
      simp only [packetAt,hd] at found
      change (if d.ifindex != c.packet.epoch then none else d.rxSkbs[c.packet.slot]?)=some pkt at found
      split at found
      · contradiction
      · exact False.elim (empty d c.packet.slot pkt hd found)

/-- Inject's actual normal guard discharges this certificate's final ledger.
The empty result is derived from the real run, unlike placeholder afterBatch. -/
theorem inject_empty (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k)) :
    (ConservationSource.inject family port msg tos ll dest).relation cs w h result v k [] ∧
      HolderAuxiliary.Inv [] loans k k v := by
  obtain ⟨next,certificate,post⟩ := inject hi run
  obtain ⟨_,_,_,_,empty⟩ := InjectAccount.normal hi.1.1.1 hi.1.2.1 hi.2 hi.1.2.2 run
  obtain ⟨suffix,hist,holders,funded,_⟩ := post.1.1
  have noSuffix : suffix=[] := List.append_cancel_left (by simpa only [List.append_nil] using hist.symm)
  have remainingEq : remaining next (NapiCarrier.removedPackets suffix)=next := by
    subst suffix
    exact List.filter_eq_self.mpr (fun _ _=>rfl)
  have noNext := empty_inventory (remainingEq ▸ funded.carriers.inventory) empty
  exact noNext ▸ ⟨certificate,post⟩

end Leanux.Proofs.WG.Queues.RxCredits.ConservationCertificates
