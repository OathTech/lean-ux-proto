import Leanux.Proofs.WG.Queues.FloodAccount
import Leanux.Proofs.WG.Queues.HolderXmit
import Leanux.Proofs.WG.Lifetimes.BatchItemSource

/-! Ordered batch occurrences retain their actual admission and removal
ledgers, CQEs and deferred suffix. No source relation contains funding. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BatchAccount
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def injectFront (d : Device) (family port : Nat) : RxHistory.Obs SkbSource := do
  if port != d.incomingPort then liftPrefix (unsupported "a batch datagram to a port other than wg0's")
  liftPrefix fixtureSend
  let src ← liftPrefix (senderSource family 0)
  if family == 4 then
    match ← liftPrefix (Net.routeOutput4 0 src.daddr) with
    | .error _ => liftPrefix (invariant "wg_batch: the datagram to wg0's port has no route")
    | .ok r =>
      if r.dev != LO_IFINDEX || r.src != src.saddr then
        liftPrefix (invariant "wg_batch: the route disagrees with the sender source")
      liftPrefix (Net.neighbourClassify LO_IFINDEX)
  return src

theorem inject_factor (d cqes family port msg) :
    RxHistory.batchItem d cqes (.inject family port msg) = (do
      let src ← injectFront d family port
      FloodSection.action msg src
      return .yield (cqes ++ [(msg.length : Int)])) := by
  by_cases guard : (port != d.incomingPort)=true
  · simp only [RxHistory.batchItem,injectFront,ite_eq_left guard,bind_assoc]
    rfl
  · simp only [RxHistory.batchItem,injectFront,ite_eq_right guard,bind_assoc]
    apply bind_congr_source (m:=RxHistory.Obs)
    intro ignored
    apply bind_congr_source (m:=RxHistory.Obs)
    intro src
    by_cases family4 : (family==4)=true
    · simp only [ite_eq_left family4,bind_assoc]
      apply bind_congr_source (m:=RxHistory.Obs)
      intro route
      cases route with
      | error e => rfl
      | ok r =>
        by_cases wrong : (r.dev != LO_IFINDEX || r.src != src.saddr)=true
        · simp only [ite_eq_left wrong,bind_assoc]
          rfl
        · simp only [ite_eq_right wrong,bind_assoc,pure_bind]
          rfl
    · simp only [ite_eq_right family4,pure_bind]
      rfl

theorem injectFront_preserves : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
    (injectFront d family port) := by
  have safe : ∀ h w,HolderAuxiliary.Inv initial loans before h w → OwnerChecks.Safe h := fun _ _ hi=>hi.2.1.safe
  have store : ∀ h w v, productStoreView v=productStoreView w → HolderAuxiliary.Inv initial loans before h w → HolderAuxiliary.Inv initial loans before h v := fun _ _ _ same hi=>HolderAuxiliary.store hi same
  unfold injectFront
  repeat' traffic_preserve_source safe using store

theorem injectFront_history (w : World) (h : List RxHistory.Event) :
    (runPrefix (injectFront d family port) w h).2=h := by
  have frame : HistoryFrame some (injectFront d family port) := by
    unfold injectFront
    repeat' first
      | exact HistoryFrame.lift _ _
      | exact HistoryFrame.pure _ _
      | apply HistoryFrame.bind
      | maintenance_intro
      | dsimp only
      | split
  simpa only [List.filterMap_some] using frame w h

private theorem multicast_store (family addr : Nat) : SameProductStore (Env.xmitMulticastLoop family addr) := by
  unfold Env.xmitMulticastLoop
  split
  · exact liftWG_sameProductStore _ (loopbackSend_kernel _ _)
  · split
    · intro initial
      exact productAmbient_spec _ _ (fun _ _ hi=>hi)
    · exact SameView.pure _ _

theorem multicast (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (family addr : Nat) : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit (xmitMulticastLoopAudit family addr)) := by
  apply HolderAuxiliary.pair
  · apply HolderDeferred.audit_preserves _ (Env.xmitMulticastLoop family addr)
      (xmitMulticastLoopAudit_erases family addr)
    · intro cs
      exact HolderEncrypt.product_store_boundary (multicast_store family addr)
    · exact (multicast_store family addr).of_factor (fun p : ProductStore43 => p.2.2.2.dev.map fun d => (d.ifindex,d.decryptQueue)) RxRing.cell (fun _=>rfl)
  · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerTraffic.«0».Leanux.Proofs.WG.OwnerTraffic.multicast) family addr
  · intro w h hi result v run
    have actual := ((RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr)) w h).symm.trans run
    have same := (ProjectedAction.iff_run _ _ _).mp (multicast_store family addr) w result v actual
    exact CurrentSlots.fields_transport hi.2.2
      (congrArg (fun p : ProductStore43=>CurrentSlots.fields {dev:=p.2.2.2.dev}) same)

theorem xmit_preserves (d : Device) (cqes : List Int) (family addr : Nat)
    (payload : List UInt8) (opts : XmitOpts) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.batchItem d cqes (.xmit family addr payload opts)) := by
  have safe : ∀ h w,HolderAuxiliary.Inv initial loans before h w → OwnerChecks.Safe h := fun _ _ hi=>hi.2.1.safe
  have store : ∀ h w v,productStoreView v=productStoreView w → HolderAuxiliary.Inv initial loans before h w → HolderAuxiliary.Inv initial loans before h v := fun _ _ _ same hi=>HolderAuxiliary.store hi same
  unfold RxHistory.batchItem
  repeat' first
    | (environment_at "xmitMulticastLoopAudit"; exact multicast initial loans before _ _)
    | (current_env_at wgXmitPrefix; exact HolderXmit.mixed initial loans before _ _ _ _)
    | (traffic_head xmitPackets; exact viewLiftPrefix_preserves productStoreView safe store (xmitPackets_sameKernel _ _ _ _))
    | traffic_preserve_source safe using store

/-- A receive occurrence records the actual rxStep's selected ledger. A TX
occurrence records the exact original run and its fresh removal suffix. -/
def Step (d : Device) (cqes : List Int) (item : BatchItem) (out : ForInStep (List Int))
    (cs next : Ledger) (w v : World) (h k : List RxHistory.Event) : Prop :=
  match item with
  | .inject family port msg => ∃ src u,
      runPrefix (injectFront d family port) w h=(.ok (src,u),h) ∧
      FloodSection.Step cs next msg src u v h k ∧ out=.yield (cqes++[(msg.length : Int)])
  | .xmit _ _ _ _ => runPrefix (RxHistory.batchItem d cqes item) w h=(.ok (out,v),k) ∧
      ∃ suffix,k=h++suffix ∧ next=remaining cs (NapiCarrier.removedPackets suffix)

theorem Step.source (step : Step d cqes item out cs next w v h k) :
    runPrefix (RxHistory.batchItem d cqes item) w h=(.ok (out,v),k) := by
  cases item with
  | inject family port msg =>
    obtain ⟨src,u,start,rxStep,rfl⟩ := step
    rw [inject_factor]
    simp only [runPrefix_bind,start,rxStep.source,runPrefix_pure]
  | xmit family addr payload opts => exact step.1

theorem Step.unique (left : Step d cqes item out cs next w v h k)
    (right : Step d cqes item out cs other w v h k) : next=other := by
  cases item with
  | inject family port msg =>
    obtain ⟨src,u,start,rxStep,_⟩ := left
    obtain ⟨src',u',start',rxStep',_⟩ := right
    rw [start] at start'
    obtain ⟨⟨rfl,rfl⟩,_⟩ := start'
    exact rxStep.unique rxStep'
  | xmit family addr payload opts =>
    obtain ⟨_,suffix,hist,ledger⟩ := left
    obtain ⟨_,suffix',hist',ledger'⟩ := right
    have same := List.append_cancel_left (hist.symm.trans hist')
    exact ledger.trans (same ▸ ledger').symm

theorem item_normal (hi : HolderAuxiliary.Inv cs loans h h w)
    (run : runPrefix (RxHistory.batchItem d cqes item) w h=(.ok (out,v),k)) :
    ∃ next,Step d cqes item out cs next w v h k ∧ HolderAuxiliary.Inv next loans k k v := by
  cases item with
  | inject family port msg =>
    rw [inject_factor] at run
    obtain ⟨src,u,j,start,rest⟩ := DecryptIteration.bind_normal run
    have hist : j=h := by simpa only [start] using injectFront_history (d:=d) (family:=family) (port:=port) w h
    subst j
    have entry := (injectFront_preserves (d:=d) (family:=family) (port:=port) w h hi).choose_spec.2.2
    rw [start] at entry
    obtain ⟨x,t,l,rxStep,done⟩ := DecryptIteration.bind_normal rest
    cases x
    simp only [runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at done
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := done
    obtain ⟨next,step,post⟩ := FloodSection.normal entry rxStep
    exact ⟨next,⟨src,u,start,step,rfl⟩,post⟩
  | xmit family addr payload opts =>
    have post := (xmit_preserves (initial:=cs) (loans:=loans) (before:=h) d cqes family addr payload opts w h hi).choose_spec.2.2
    rw [run] at post
    obtain ⟨suffix,hist,post⟩ := HolderInitial.rebase post
    exact ⟨_,⟨run,suffix,hist,rfl⟩,post⟩

def loop (d : Device) (entries : List BatchItem) (cqes : List Int) : RxHistory.Obs (List Int) :=
  forIn entries cqes (fun item qs=>RxHistory.batchItem d qs item)

theorem loop_nil (d cqes) : loop d [] cqes=pure cqes := rfl

theorem loop_cons (d item entries cqes) : loop d (item::entries) cqes = (do
    let out ← RxHistory.batchItem d cqes item
    match out with
    | .done qs => pure qs
    | .yield qs => loop d entries qs) := by
  simp only [loop,List.forIn_cons]
  apply bind_congr_source (m:=RxHistory.Obs)
  intro step
  cases step <;> rfl

/-- The constructors follow the actual for-in outcome. Even a done arm must
carry the original item's execution; no synthetic early completion is allowed. -/
inductive Path (d : Device) : List BatchItem → List Int → Ledger → World → List RxHistory.Event →
    List Int → Ledger → World → List RxHistory.Event → Prop
  | nil : Path d [] cqes cs w h cqes cs w h
  | done (step : Step d cqes item (.done out) cs next w v h k) :
      Path d (item::entries) cqes cs w h out next v k
  | yield (step : Step d cqes item (.yield qs) cs middle w u h j)
      (tail : Path d entries qs middle u j out next v k) :
      Path d (item::entries) cqes cs w h out next v k

theorem Path.source (path : Path d entries cqes cs w h out next v k) :
    runPrefix (loop d entries cqes) w h=(.ok (out,v),k) := by
  induction path with
  | nil => rfl
  | done step => simp only [loop_cons,runPrefix_bind,step.source,runPrefix_pure]
  | yield step tail ih => simp only [loop_cons,runPrefix_bind,step.source,ih]

theorem loop_normal (hi : HolderAuxiliary.Inv cs loans h h w)
    (run : runPrefix (loop d entries cqes) w h=(.ok (out,v),k)) :
    ∃ next,Path d entries cqes cs w h out next v k ∧ HolderAuxiliary.Inv next loans k k v := by
  induction entries generalizing cqes cs w h with
  | nil =>
    simp only [loop_nil,runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact ⟨cs,.nil,hi⟩
  | cons item entries ih =>
    rw [loop_cons] at run
    obtain ⟨result,u,j,first,rest⟩ := DecryptIteration.bind_normal run
    obtain ⟨middle,step,post⟩ := item_normal hi first
    cases result with
    | done qs =>
      simp only [runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at rest
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := rest
      exact ⟨middle,.done step,post⟩
    | yield qs =>
      obtain ⟨next,path,final⟩ := ih post rest
      exact ⟨next,.yield step path,final⟩

theorem Path.unique (left : Path d entries cqes cs w h out next v k)
    (right : Path d entries cqes cs w h out other v k) : next=other := by
  induction left generalizing other with
  | nil => cases right; rfl
  | done step =>
    cases right with
    | done step' => exact step.unique step'
    | yield step' tail' =>
      have impossible := step.source.symm.trans step'.source
      cases impossible
  | yield step tail ih =>
    cases right with
    | done step' =>
      have impossible := step.source.symm.trans step'.source
      cases impossible
    | yield step' tail' =>
      have same := step.source.symm.trans step'.source
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := same
      have ledger := step.unique step'
      subst ledger
      exact ih tail'

def front : RxHistory.Obs Device := do
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a batch without wg0")
  if !d.running then liftPrefix (unsupported "a batch with wg0 down")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "a batch while a handshake is queued"))
  return d

def finish (entries : List BatchItem) (cqes : List Int) : RxHistory.Obs Int := do
  liftPrefix (modifyAmbient fun w=>{w with extraOut:=[("cqes",Lean.toJson cqes)]})
  RxHistory.afterBatch
  return entries.length

theorem source_factor (entries : List BatchItem) : RxHistory.batch entries = (do
    let d ← front
    let cqes ← loop d entries []
    finish entries cqes) := by
  unfold RxHistory.batch front finish loop
  simp only [bind_assoc]
  apply bind_congr_source (m:=RxHistory.Obs)
  intro state
  cases state.dev with
  | none => rfl
  | some d =>
    by_cases down : (!d.running)=true
    · simp only [ite_eq_left down,bind_assoc]
      rfl
    · simp only [ite_eq_right down,bind_assoc]
      apply bind_congr_source (m:=RxHistory.Obs)
      intro ignored
      simp only [pure_bind]

theorem front_preserves {I : List RxHistory.Event → World → Prop} {S : List RxHistory.Event → Prop}
    (safe : ∀ h w,I h w→S h)
    (store : ∀ h w v,productStoreView v=productStoreView w→I h w→I h v) :
    PrefixPreserves I S front := by
  unfold front
  repeat' traffic_preserve_source safe using store

theorem front_history (w : World) (h : List RxHistory.Event) : (runPrefix front w h).2=h := by
  have frame : HistoryFrame some front := by
    unfold front
    repeat' first
      | exact HistoryFrame.lift _ _
      | exact HistoryFrame.pure _ _
      | apply HistoryFrame.bind
      | apply HistoryFrame.forIn
      | maintenance_intro
      | dsimp only
      | split
  simpa only [List.filterMap_some] using frame w h

theorem front_store (run : runPrefix front w h=(.ok (d,v),k)) :
    productStoreView v=productStoreView w := by
  have kept := (front_preserves (I:=fun _ v=>productStoreView v=productStoreView w)
    (S:=fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ same hi=>same.trans hi) w h rfl).choose_spec.2.2
  simpa only [run] using kept

theorem front_present (run : runPrefix front w h=(.ok (d,v),k)) : v.wg.dev.isSome=true := by
  have same : v.wg.dev=w.wg.dev := congrArg (fun p : ProductStore43=>p.2.2.2.dev) (front_store run)
  rw [same]
  unfold front at run
  have read : runPrefix (liftPrefix (getWG : Leanux.M WGWorld) : RxHistory.Obs WGWorld) w h =
      (.ok (w.wg,w),h) := rfl
  rw [runPrefix_bind,read] at run
  cases dev : w.wg.dev with
  | none =>
    simp only [dev] at run
    have impossible := congrArg Prod.fst run
    change (Except.error _ : Except Stop (Device × World))=.ok (d,v) at impossible
    cases impossible
  | some d => rfl

theorem finish_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (entries : List BatchItem) (cqes : List Int) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (finish entries cqes) := by
  have safe : ∀ h w,HolderAuxiliary.Inv initial loans before h w→OwnerChecks.Safe h := fun _ _ hi=>hi.2.1.safe
  have store : ∀ h w v,productStoreView v=productStoreView w→HolderAuxiliary.Inv initial loans before h w→HolderAuxiliary.Inv initial loans before h v := fun _ _ _ same hi=>HolderAuxiliary.store hi same
  unfold finish
  repeat' first
    | (traffic_head RxHistory.afterBatch; exact HolderAfterBatch.afterBatch initial loans before)
    | traffic_preserve_source safe using store

theorem finish_normal (hi : HolderAuxiliary.Inv cs loans h h w)
    (run : runPrefix (finish entries cqes) w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ HolderAuxiliary.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k k v := by
  have post := (finish_preserves cs loans h entries cqes w h hi).choose_spec.2.2
  rw [run] at post
  exact HolderInitial.rebase post

/-- The saved device, ordered item path and exact deferred suffix determine
the final ledger. The relation does not assume an empty completion or funding. -/
def Outcome (cs next : Ledger) (entries : List BatchItem)
    (w v : World) (h k : List RxHistory.Event) (result : Int) : Prop :=
  ∃ d cqes u t j middle suffix,
    runPrefix front w h=(.ok (d,u),h) ∧
    Path d entries [] cs u h cqes middle t j ∧
    runPrefix (finish entries cqes) t j=(.ok (result,v),k) ∧
    k=j++suffix ∧ next=remaining middle (NapiCarrier.removedPackets suffix)

theorem Outcome.source (outcome : Outcome cs next entries w v h k result) :
    runPrefix (RxHistory.batch entries) w h=(.ok (result,v),k) := by
  obtain ⟨d,cqes,u,t,j,middle,suffix,start,path,done,_,_⟩ := outcome
  rw [source_factor]
  simp only [runPrefix_bind,start,path.source,done]

theorem Outcome.unique (left : Outcome cs next entries w v h k result)
    (right : Outcome cs other entries w v h k result) : next=other := by
  obtain ⟨d,cqes,u,t,j,middle,suffix,start,path,done,hist,ledger⟩ := left
  obtain ⟨d',cqes',u',t',j',middle',suffix',start',path',done',hist',ledger'⟩ := right
  rw [start] at start'
  obtain ⟨⟨rfl,rfl⟩,_⟩ := start'
  have same := path.source.symm.trans path'.source
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := same
  have mids := path.unique path'
  have tails := List.append_cancel_left (hist.symm.trans hist')
  rw [mids,tails] at ledger
  exact ledger.trans ledger'.symm

theorem normal (account : Boundary cs loans w.wg)
    (physical : HolderDeviceCreate.OptionalPhysical w.wg)
    (owners : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg)
    (run : runPrefix (RxHistory.batch entries) w h=(.ok (result,v),k)) :
    ∃ next,Outcome cs next entries w v h k result ∧ HolderAuxiliary.Inv next loans k k v := by
  rw [source_factor] at run
  obtain ⟨d,u,j,start,rest⟩ := DecryptIteration.bind_normal run
  have hist : j=h := by simpa only [start] using front_history w h
  subst j
  have same := front_store start
  have dev : u.wg.dev=w.wg.dev := congrArg (fun p : ProductStore43=>p.2.2.2.dev) same
  have physical' : HolderDeviceCreate.OptionalPhysical u.wg := by
    simpa only [HolderDeviceCreate.OptionalPhysical,NativeRxInv,RxRing.nativeCell,dev] using physical
  have slots' : CurrentSlots.Inv u.wg := CurrentSlots.fields_transport slots
    (congrArg (fun d : Option Device=>CurrentSlots.fields {dev:=d}) dev)
  have entry := HolderInitial.at_cut
    (HolderInitial.store account (congrArg (fun p : ProductStore43=>p.2.2.2) same))
    (HolderInitial.physical_present physical' (front_present start))
    (OwnerWorkers.store h w u same owners) slots'
  obtain ⟨cqes,t,j,loopRun,done⟩ := DecryptIteration.bind_normal rest
  obtain ⟨middle,path,atTail⟩ := loop_normal entry loopRun
  obtain ⟨suffix,tailEq,post⟩ := finish_normal atTail done
  exact ⟨_,⟨d,cqes,u,t,j,middle,suffix,start,path,done,tailEq,rfl⟩,post⟩

theorem Outcome.restore (outcome : Outcome cs next entries w v h k result)
    (account : Boundary cs loans w.wg) (physical : HolderDeviceCreate.OptionalPhysical w.wg)
    (owners : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg) :
    HolderAuxiliary.Inv next loans k k v := by
  obtain ⟨other,derived,post⟩ := normal account physical owners slots outcome.source
  exact (outcome.unique derived) ▸ post

theorem native_normal (account : Boundary cs loans w.wg)
    (physical : HolderDeviceCreate.OptionalPhysical w.wg)
    (owners : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg)
    (run : (Env.batch entries).run w=.ok (result,v)) :
    let k := (runPrefix (RxHistory.batch entries) w h).2
    ∃ next,Outcome cs next entries w v h k result ∧ HolderAuxiliary.Inv next loans k k v := by
  have actual := (RxHistory.batch_erases entries w h).trans run
  exact normal account physical owners slots (Prod.ext actual rfl)

/-- Stop prefixes retain the existing owner safety. Dynamic account outcomes
are concluded at actual normal endpoints, including errno CQE entries. -/
theorem ensures (cs : Ledger) (loans : Reservations) (entries : List BatchItem) :
    PrefixEnsures (fun h w=>Boundary cs loans w.wg ∧ HolderDeviceCreate.OptionalPhysical w.wg ∧
      OwnerChecks.Inv h w ∧ CurrentSlots.Inv w.wg) OwnerChecks.Safe
      (RxHistory.batch entries)
      (fun result k v=>∃ w h next,Outcome cs next entries w v h k result ∧
        HolderAuxiliary.Inv next loans k k v) := by
  intro w h hi
  obtain ⟨suffix,hist,safe,_⟩ := OwnerTraffic.batch entries w h hi.2.2.1
  refine ⟨suffix,hist,safe,?_⟩
  cases actual : (runPrefix (RxHistory.batch entries) w h).1 with
  | error e => trivial
  | ok out =>
    obtain ⟨next,path,post⟩ := normal hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 (Prod.ext actual rfl)
    exact ⟨w,h,next,path,post⟩

end Leanux.Proofs.WG.Queues.RxCredits.BatchAccount


