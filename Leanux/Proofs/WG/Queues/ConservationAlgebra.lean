import Leanux.Proofs.WG.Queues.AdmissionPath

/-! Local conservation algebra for the existing source-indexed admission path.
The occurrence is specified by its actual receipt and journal cut. This proves
pending-or-removed membership, not a global multiplicity or initialized-run
claim. The separate poll disposition results classify those removals. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ConservationAlgebra
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- Admission retains every earlier ledger entry, including an ordinary
rejection or either queue-full return. -/
theorem admission_retains
    (outcome : AdmissionOutcome.Outcome cs next msg src ds w v a b r)
    (member : c ∈ cs) : c ∈ next := by
  have rest := outcome.2.2.2
  cases value:r.value with
  | none =>
    simp only [value] at rest
    simpa only [rest.2.2] using member
  | some ctx =>
    simp only [value] at rest
    obtain ⟨added,ret,middle,clock,_,_,_,_,ledger⟩ := rest
    rw [ledger]
    split
    · exact member
    · exact List.mem_cons_of_mem _ member

/-- A newly present entry can only be the carrier selected from the actual
admission endpoint; existing entries are neither rewritten nor replaced. -/
theorem admission_origin
    (outcome : AdmissionOutcome.Outcome cs next msg src ds w v a b r)
    (member : c ∈ next) : c ∈ cs ∨
      ∃ ctx added,r.value=some ctx ∧ AdmissionOutcome.carrier r.after ctx=some added ∧
        c=enqueued added := by
  have rest := outcome.2.2.2
  cases value:r.value with
  | none =>
    simp only [value] at rest
    exact Or.inl (by simpa only [rest.2.2] using member)
  | some ctx =>
    simp only [value] at rest
    obtain ⟨added,ret,middle,clock,selected,_,_,_,ledger⟩ := rest
    rw [ledger] at member
    split at member
    · exact Or.inl member
    · rcases List.mem_cons.mp member with same | old
      · exact Or.inr ⟨ctx,added,rfl,selected,same⟩
      · exact Or.inl old

/-- Removing exactly the logged packet identities leaves every other entry. -/
theorem pending_or_removed (member : c ∈ cs) :
    c ∈ remaining cs removed ∨ c.packet ∈ removed := by
  by_cases gone : c.packet ∈ removed
  · exact Or.inr gone
  · exact Or.inl (by simp [remaining,member,gone])

theorem step_pending_or_removed (step : AdmissionPath.Step cs w h next v k)
    (member : c ∈ cs) :
    ∃ suffix,k=h++suffix ∧ (c ∈ next ∨ c.packet ∈ NapiCarrier.removedPackets suffix) := by
  cases step with
  | admission run outcome =>
    obtain ⟨suffix,hist⟩ := AdmissionPath.step_appends (.admission run outcome)
    exact ⟨suffix,hist,Or.inl (admission_retains outcome member)⟩
  | poll run suffix hist => exact ⟨suffix,hist,pending_or_removed member⟩

/-- An entry can disappear from this finite actual path only at a removal
in its precise fresh suffix. Incoming old removals cannot justify its loss. -/
theorem path_pending_or_removed (path : AdmissionPath.Path cs w h next v k)
    (member : c ∈ cs) :
    ∃ suffix,k=h++suffix ∧ (c ∈ next ∨ c.packet ∈ NapiCarrier.removedPackets suffix) := by
  induction path with
  | refl => exact ⟨[],by simp,Or.inl member⟩
  | cons step tail ih =>
    obtain ⟨front,hfront,effect⟩ := step_pending_or_removed step member
    rcases effect with pending | removed
    · obtain ⟨back,hback,rest⟩ := ih pending
      refine ⟨front++back,by rw [hback,hfront,List.append_assoc],?_⟩
      rcases rest with pending | removed
      · exact Or.inl pending
      · exact Or.inr (by simpa [NapiCarrier.removedPackets,List.filterMap_append] using
          (List.mem_append_right (NapiCarrier.removedPackets front) removed))
    · obtain ⟨back,hback⟩ := AdmissionPath.path_appends tail
      refine ⟨front++back,by rw [hback,hfront,List.append_assoc],Or.inr ?_⟩
      simpa [NapiCarrier.removedPackets,List.filterMap_append] using
        (List.mem_append_left (NapiCarrier.removedPackets back) removed)

/-- A completed accepted admission inserts precisely its captured carrier.
The enqueue result is an actual source run, not an accounting assumption. -/
theorem admitted_ledger
    (outcome : AdmissionOutcome.Outcome cs next msg src ds w v a b r)
    (value : r.value=some ctx)
    (selected : AdmissionOutcome.carrier r.after ctx=some c)
    (enqueue : ((enqueuePerDeviceAndPeerRx ctx.slot).run r.after).run r.ambientAfter=
      .ok ((ret,middle),clock))
    (accepted : ret ≠ -ENOSPC) : next=enqueued c::cs := by
  have rest := outcome.2.2.2
  simp only [value] at rest
  obtain ⟨actual,result,other,time,found,run,_,_,ledger⟩ := rest
  have same := Option.some.inj (found.symm.trans selected)
  subst actual
  have resultSame := congrArg (fun x => x.1.1) (Except.ok.inj (run.symm.trans enqueue))
  change result=ret at resultSame
  subst result
  simpa only [accepted,ite_false] using ledger

theorem admitted_member
    (outcome : AdmissionOutcome.Outcome cs next msg src ds w v a b r)
    (value : r.value=some ctx)
    (selected : AdmissionOutcome.carrier r.after ctx=some c)
    (enqueue : ((enqueuePerDeviceAndPeerRx ctx.slot).run r.after).run r.ambientAfter=
      .ok ((ret,middle),clock))
    (accepted : ret ≠ -ENOSPC) : enqueued c ∈ next := by
  rw [admitted_ledger outcome value selected enqueue accepted]
  exact List.mem_cons_self

/-- At an established input boundary, the actual accepted packet identity is
fresh relative to every pending carrier. This follows from the output inventory
derived for this same source execution, not from an assumed funded output. -/
theorem admitted_fresh
    (hi : DurableHolders.Boundary cs loans w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (outcome : AdmissionOutcome.Outcome cs next msg src ds w v a b r)
    (value : r.value=some ctx)
    (selected : AdmissionOutcome.carrier r.after ctx=some c)
    (enqueue : ((enqueuePerDeviceAndPeerRx ctx.slot).run r.after).run r.ambientAfter=
      .ok ((ret,middle),clock))
    (accepted : ret ≠ -ENOSPC) :
    c.packet ∉ cs.map Carrier.packet ∧ (next.map Carrier.packet).Nodup := by
  obtain ⟨holders,funded,_⟩ := AdmissionOutcome.boundary hi fresh physical outcome
  have distinct := funded.carriers.inventory.distinct
  refine ⟨?_,distinct⟩
  rw [admitted_ledger outcome value selected enqueue accepted] at distinct
  exact (List.nodup_cons.mp distinct).1

/-- At this specified accepted admission occurrence, the fresh carrier is
either pending after the supplied actual continuation or has a removal in that
continuation's exact journal suffix. The continuation begins at the same World
and history returned by this admission. -/
theorem admitted_fate
    (run : runPrefix (AdmissionPath.consume msg src ds) w h=(.ok ((),v),k))
    (outcome : AdmissionOutcome.Outcome cs next msg src ds
      w.wg v.wg w.ambient v.ambient r)
    (value : r.value=some ctx)
    (selected : AdmissionOutcome.carrier r.after ctx=some c)
    (enqueue : ((enqueuePerDeviceAndPeerRx ctx.slot).run r.after).run r.ambientAfter=
      .ok ((ret,middle),clock))
    (accepted : ret ≠ -ENOSPC)
    (tail : AdmissionPath.Path next v k final z l) :
    AdmissionPath.Step cs w h next v k ∧
      ∃ suffix,l=k++suffix ∧
        (enqueued c ∈ final ∨ c.packet ∈ NapiCarrier.removedPackets suffix) := by
  refine ⟨.admission run outcome,?_⟩
  exact path_pending_or_removed tail (admitted_member outcome value selected enqueue accepted)

end Leanux.Proofs.WG.Queues.RxCredits.ConservationAlgebra
