import Leanux.Proofs.WG.Queues.HolderAdmission

/-! The new ledger at admission is selected by the actual source receipt and
its enqueue result. The receipt relation contains no credit or stable-boundary
conclusion; those are derived separately from the supplied complete account. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionOutcome
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

/-- Read the allocation identity at the captured admission endpoint. -/
def carrier (w : WGWorld) (ctx : RxOrigin.Admission) : Option Carrier := do
  let d ← w.dev
  let p ← d.peers[ctx.packet.peer]?
  return ⟨⟨d.ifindex,ctx.slot⟩,⟨d.ifindex,ctx.packet.peer,p.internalId⟩,.unpublished⟩

/-- Every ledger choice is fixed by the actual source cuts, including rejection
before admission and disposal on the full peer-queue (-ENOSPC) return.
Decrypt-ring full (-EPIPE) retains the queued DEAD carrier. -/
def Outcome (cs next : Ledger) (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (w v : WGWorld) (a b : Ambient) (r : WGRunWitness (Option RxOrigin.Admission)) : Prop :=
  r.before=w ∧ r.ambientBefore=a ∧ r.Valid (RxOrigin.admitSource msg src ds) ∧
  match r.value with
  | none => r.after=v ∧ r.ambientAfter=b ∧ next=cs
  | some ctx => ∃ c ret middle clock,
      carrier r.after ctx=some c ∧
      ((enqueuePerDeviceAndPeerRx ctx.slot).run r.after).run r.ambientAfter=.ok ((ret,middle),clock) ∧
      ((finishAfter ctx ret).run middle).run clock=.ok (((),v),b) ∧
      (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
      next=(if ret = -ENOSPC then cs else enqueued c::cs)

private theorem witness_unique {r s : WGRunWitness α} (action : WG.M α)
    (rb : r.before=w) (sb : s.before=w) (ra : r.ambientBefore=a) (sa : s.ambientBefore=a)
    (rv : r.Valid action) (sv : s.Valid action) : r=s := by
  cases r
  cases s
  simp only [WGRunWitness.Valid] at rv sv
  simp_all only [Except.ok.injEq,Prod.mk.injEq]

/-- The actual front run fixes the receipt and the enqueue run fixes the
ledger. No choice of reference-count slack can affect this result. -/
theorem unique (left : Outcome cs xs msg src ds w v a b r)
    (right : Outcome cs ys msg src ds w v a b s) : r=s ∧ xs=ys := by
  have same := witness_unique _ left.1 right.1 left.2.1 right.2.1 left.2.2.1 right.2.2.1
  subst s
  refine ⟨rfl,?_⟩
  have hl := left.2.2.2
  have hr := right.2.2.2
  cases value:r.value with
  | none => simp only [value] at hl hr; exact hl.2.2.trans hr.2.2.symm
  | some ctx =>
    simp only [value] at hl hr
    obtain ⟨c,ret,middle,clock,hc,he,_,_,hx⟩ := hl
    obtain ⟨d,result,other,time,hd,hf,_,_,hy⟩ := hr
    have carrierSame := Option.some.inj (hc.symm.trans hd)
    have resultSame := congrArg (fun x => x.1.1) (Except.ok.inj (he.symm.trans hf))
    subst d
    change ret=result at resultSame
    subst result
    exact hx.trans hy.symm

/-- The receipt relation reconstructs the original whole consumeData call. -/
theorem source (outcome : Outcome cs next msg src ds w v a b r) :
    ((consumeData msg src ds).run w).run a=.ok (((),v),b) := by
  obtain ⟨before,ambient,valid,rest⟩ := outcome
  have front : ((RxOrigin.admitSource msg src ds).run w).run a=
      .ok ((r.value,r.after),r.ambientAfter) := by
    simpa only [WGRunWitness.Valid,before,ambient] using valid
  rw [←RxOrigin.consumeSource_eq]
  change ((do
    let result ← RxOrigin.admitSource msg src ds
    match result with
    | none => pure ()
    | some ctx => finishSource ctx).run w).run a = _
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨r.value,r.after,r.ambientAfter,front,?_⟩
  cases value:r.value with
  | none =>
    simp only [value] at rest ⊢
    rcases rest with ⟨after,clock,_⟩
    simp [after,clock]
  | some ctx =>
    simp only [value] at rest ⊢
    obtain ⟨_,ret,middle,clock,_,enqueue,finish,_,_⟩ := rest
    rw [finish_factor]
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨ret,middle,clock,enqueue,finish⟩

theorem carrier_at (ctx : RxOrigin.Admission) (o : Owner)
    (hi : CarrierState (⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩::cs) loans w)
    (owner : o.slot=ctx.packet.peer) :
    carrier w ctx=some ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩ := by
  have positive : 0 < demand (⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩::cs) loans o := by
    simp only [demand,charges_cons,Phase.charged,
      and_self,ite_true]
    omega
  obtain ⟨p,res,_⟩ := protected_resident hi.funded positive
  obtain ⟨d,hd,epoch,hp,stamp⟩ := resident_fields res
  cases o
  simp [carrier,hd,←owner,hp,epoch,stamp]

theorem extract (hi : StableConsumption cs loans msg src ds w v a b r) :
    ∃ next, Outcome cs next msg src ds w v a b r ∧
      CarrierState next loans v ∧ StableRx next v := by
  obtain ⟨before,ambient,valid,rest⟩ := hi
  cases value:r.value with
  | none =>
    simp only [value] at rest
    exact ⟨cs,⟨before,ambient,valid,by simp only [value]; exact ⟨rest.1,rest.2.1,True.intro⟩⟩,rest.2.2⟩
  | some ctx =>
    simp only [value] at rest
    obtain ⟨o,funded,owner,_,_,ret,middle,clock,enqueue,finish,choices,endpoint⟩ := rest
    let c : Carrier := ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩
    have selected : carrier r.after ctx=some c := carrier_at ctx o funded owner
    refine ⟨if ret = -ENOSPC then cs else enqueued c::cs,
      ⟨before,ambient,valid,?_⟩,?_⟩
    · simp only [value]
      exact ⟨c,ret,middle,clock,selected,enqueue,finish,choices,rfl⟩
    · by_cases full : ret = -ENOSPC
      · simp only [full,ite_true] at endpoint ⊢
        exact ⟨endpoint.1,endpoint.2.1⟩
      · simpa only [full,ite_false] using endpoint

/-- All durable holders remain in the same budget; only the source-selected
receive ledger changes. This is a normal source contract, not initialization. -/
theorem consume {h : DurableHolders} (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (fresh : Packets.Inv w) (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (a b : Ambient)
    (run : ((consumeData msg src ds).run w).run a=.ok (((),v),b)) :
    ∃ r next, Outcome cs next msg src ds w v a b r ∧ h.Funded next loans v ∧ StableRx next v := by
  obtain ⟨aligned,r,receipt⟩ := HolderAdmission.consume_funded hi stable fresh physical a b run
  obtain ⟨next,outcome,funded,stableOut⟩ := extract receipt
  exact ⟨r,next,outcome,⟨aligned,funded⟩,stableOut⟩

/-- A source certificate chooses the ledger independently; uniqueness joins
it to the account derived from that exact original execution. -/
theorem restore {h : DurableHolders} (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (fresh : Packets.Inv w) (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (outcome : Outcome cs next msg src ds w v a b r) :
    h.Funded next loans v ∧ StableRx next v := by
  obtain ⟨actual,derived,other,funded,stableOut⟩ := consume hi stable fresh physical a b (source outcome)
  have same := (unique outcome other).2
  exact same ▸ ⟨funded,stableOut⟩

theorem boundary (hi : Boundary cs loans w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (outcome : Outcome cs next msg src ds w v a b r) : Boundary next loans v := by
  obtain ⟨h,funded,stable⟩ := hi
  obtain ⟨after,stableOut⟩ := restore funded stable fresh physical outcome
  exact ⟨h,after,stableOut⟩

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionOutcome
