import Leanux.Proofs.WG.Queues.AdmissionSection
import Leanux.Proofs.WG.Queues.HolderAuxDeferred
import Leanux.Proofs.WG.Origins.OwnerTraffic
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! The actual datagram caller, with its source-selected admission ledger and
its original crypt-wait removal suffix. Normal completion is established from
the input account and optional physical ring, never an output account premise. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.InjectAccount
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open DurableHolders

def precheck (dest : Nat) : RxHistory.Obs Unit := do
  if (← liftPrefix getRouting).foreignCreator then
    if (← liftPrefix getEnv).netnsCHolders.isEmpty then liftPrefix (unsupported "wg_inject after wg_netns_close (no socket in the creating namespace)")
    if dest == 1 then liftPrefix (unsupported "wg_inject to wg0's address from the creating namespace (unroutable)")

def prepare (d : Device) (family port tos : Nat) (ll : Bool) (dest : Nat) : RxHistory.Obs SkbSource := do
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a datagram to a port other than wg0's")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "receiving while a handshake is queued"))
  liftPrefix fixtureSend
  let src ← liftPrefix (senderSource family dest tos ll)
  if family == 4 then
    match ← liftPrefix (Net.Fib.inSocketNs (Net.routeOutput4 0 src.daddr)) with
    | .error _ => liftPrefix (invariant "wg_inject: the injector's datagram has no route")
    | .ok r =>
      if r.dev != LO_IFINDEX || r.src != src.saddr then
        liftPrefix (invariant "wg_inject: the route disagrees with the sender source")
      liftPrefix (Net.Fib.inSocketNs (Net.neighbourClassify LO_IFINDEX))
  return src

private def prepareWith {α : Type} (d : Device) (family port tos : Nat) (ll : Bool) (dest : Nat) (next : SkbSource → RxHistory.Obs α) : RxHistory.Obs α := do
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a datagram to a port other than wg0's")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "receiving while a handshake is queued"))
  liftPrefix fixtureSend
  let src ← liftPrefix (senderSource family dest tos ll)
  if family == 4 then
    match ← liftPrefix (Net.Fib.inSocketNs (Net.routeOutput4 0 src.daddr)) with
    | .error _ => liftPrefix (invariant "wg_inject: the injector's datagram has no route")
    | .ok r =>
      if r.dev != LO_IFINDEX || r.src != src.saddr then
        liftPrefix (invariant "wg_inject: the route disagrees with the sender source")
      liftPrefix (Net.Fib.inSocketNs (Net.neighbourClassify LO_IFINDEX))
  next src

private theorem prepareWith_factor (d family port tos ll dest) (next : SkbSource → RxHistory.Obs α) :
    prepareWith d family port tos ll dest next = (prepare d family port tos ll dest >>= next) := by
  by_cases guard : (!d.running || port != d.incomingPort)=true
  · simp only [prepareWith,prepare,ite_eq_left guard,bind_assoc]
    rfl
  · simp only [prepareWith,prepare,ite_eq_right guard,bind_assoc]
    apply bind_congr_source (m:=RxHistory.Obs)
    intro ignored
    apply bind_congr_source (m:=RxHistory.Obs)
    intro sent
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
    · simp only [ite_eq_right family4,pure_bind]

def front (family port tos : Nat) (ll : Bool) (dest : Nat) : RxHistory.Obs SkbSource := do
  precheck dest
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a datagram to a port other than wg0's (no wg0)")
  prepare d family port tos ll dest

def finish (msg : List UInt8) : RxHistory.Obs Int := do
  RxHistory.runCryptWorkers
  let d ← liftPrefix (liftWG getDev)
  RxHistory.mixed (requireDrainedPrefix "the datagram queued"
    [!d.handshakeQueue.empty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  return msg.length

theorem source_factor (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    RxHistory.inject family port msg tos ll dest = (do
      let src ← front family port tos ll dest
      runWorkerPrefix .netRx (AdmissionCaller.receive msg src)
      finish msg) := by
  rw [AdmissionCaller.inject_source]
  change (do
    if (← liftPrefix getRouting).foreignCreator then
      if (← liftPrefix getEnv).netnsCHolders.isEmpty then liftPrefix (unsupported "wg_inject after wg_netns_close (no socket in the creating namespace)")
      if dest == 1 then liftPrefix (unsupported "wg_inject to wg0's address from the creating namespace (unroutable)")
    let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a datagram to a port other than wg0's (no wg0)")
    prepareWith d family port tos ll dest (fun src => do
      runWorkerPrefix .netRx (AdmissionCaller.receive msg src)
      finish msg)) = _
  have stopped {α β : Type} (why : String) (next : α → RxHistory.Obs β) :
      ((liftPrefix (unsupported why) : RxHistory.Obs α) >>= next) =
        (liftPrefix (unsupported why) : RxHistory.Obs β) := rfl
  simp only [prepareWith_factor,front,precheck,bind_assoc,bind_if_source,pure_bind,stopped]
  repeat' first
    | rfl
    | (apply bind_congr_source (m:=RxHistory.Obs); intro x)
    | simp only [bind_assoc,bind_if_source,pure_bind,stopped]
    | (split <;> try simp_all)


private theorem precheck_preserves {I : List RxHistory.Event → World → Prop} {S : List RxHistory.Event → Prop}
    (safe : ∀ h w,I h w → S h)
    (store : ∀ h w v,productStoreView v=productStoreView w → I h w → I h v) :
    PrefixPreserves I S (precheck dest) := by
  unfold precheck
  repeat' traffic_preserve_source safe using store

private theorem prepare_preserves {I : List RxHistory.Event → World → Prop} {S : List RxHistory.Event → Prop}
    (safe : ∀ h w,I h w → S h)
    (store : ∀ h w v,productStoreView v=productStoreView w → I h w → I h v) :
    PrefixPreserves I S (prepare d family port tos ll dest) := by
  unfold prepare
  repeat' traffic_preserve_source safe using store

theorem front_preserves {I : List RxHistory.Event → World → Prop} {S : List RxHistory.Event → Prop}
    (safe : ∀ h w,I h w → S h)
    (store : ∀ h w v,productStoreView v=productStoreView w → I h w → I h v) :
    PrefixPreserves I S (front family port tos ll dest) := by
  unfold front
  apply PrefixPreserves.bind (precheck_preserves safe store)
  intro x
  repeat' first
    | exact prepare_preserves safe store
    | traffic_preserve_source safe using store

theorem front_history (w : World) (h : List RxHistory.Event) :
    (runPrefix (front family port tos ll dest) w h).2=h := by
  have frame : HistoryFrame some (front family port tos ll dest) := by
    unfold front precheck prepare
    repeat' first
      | exact HistoryFrame.lift _ _
      | exact HistoryFrame.pure _ _
      | apply HistoryFrame.bind
      | apply HistoryFrame.forIn
      | maintenance_intro
      | dsimp only
      | split
  simpa only [List.filterMap_some] using frame w h

/-- A normal front has passed the actual present-device guard. -/
theorem front_present
    (run : runPrefix (front family port tos ll dest) w h=(.ok (src,v),k)) : v.wg.dev.isSome=true := by
  unfold front at run
  obtain ⟨x,u,j,start,rest⟩ := DecryptIteration.bind_normal run
  cases x
  have read : runPrefix (liftPrefix (getWG : Leanux.M WGWorld) : RxHistory.Obs WGWorld) u j =
      (.ok (u.wg,u),j) := rfl
  simp only [runPrefix_bind,read] at rest
  cases dev : u.wg.dev with
  | none =>
    simp only [dev] at rest
    have impossible := congrArg Prod.fst rest
    change (Except.error _ : Except Stop (SkbSource × World)) = .ok (src,v) at impossible
    cases impossible
  | some d =>
    simp only [dev] at rest
    have kept := (prepare_preserves (d:=d) (family:=family) (port:=port) (tos:=tos) (ll:=ll) (dest:=dest) (I:=fun _ w => productStoreView w=productStoreView u)
      (S:=fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ same hi=>same.trans hi) u j rfl).choose_spec.2.2
    rw [rest] at kept
    have same := congrArg (fun p : ProductStore43 => p.2.2.2.dev) kept
    change v.wg.dev=u.wg.dev at same
    rw [same,dev]
    rfl

theorem front_store (run : runPrefix (front family port tos ll dest) w h=(.ok (src,v),k)) :
    productStoreView v=productStoreView w := by
  have kept := (front_preserves (family:=family) (port:=port) (tos:=tos) (ll:=ll) (dest:=dest)
    (I:=fun _ v=>productStoreView v=productStoreView w) (S:=fun _=>True)
    (fun _ _ _=>True.intro) (fun _ _ _ same hi=>same.trans hi) w h rfl).choose_spec.2.2
  simpa only [run] using kept

private theorem optional_store (hi : HolderDeviceCreate.OptionalPhysical w.wg)
    (same : productStoreView v=productStoreView w) : HolderDeviceCreate.OptionalPhysical v.wg := by
  have dev : v.wg.dev=w.wg.dev := congrArg (fun p : ProductStore43=>p.2.2.2.dev) same
  simpa only [HolderDeviceCreate.OptionalPhysical,NativeRxInv,RxRing.nativeCell,dev] using hi

private theorem slots_store (hi : CurrentSlots.Inv w.wg)
    (same : productStoreView v=productStoreView w) : CurrentSlots.Inv v.wg := by
  apply CurrentSlots.fields_transport hi
  have dev : v.wg.dev=w.wg.dev := congrArg (fun p : ProductStore43=>p.2.2.2.dev) same
  exact congrArg (fun d : Option Device=>CurrentSlots.fields {dev:=d}) dev

/-- The original guard after the actual crypt wait empties precisely its
current removal-adjusted ledger. It does not assume a successful callback. -/
theorem finish_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : runPrefix (finish msg) w h=(.ok (result,v),k)) :
    ∃ u j suffix, runPrefix RxHistory.runCryptWorkers w h=(.ok ((),u),j) ∧
      j=before++suffix ∧ remaining initial (NapiCarrier.removedPackets suffix)=[] ∧
      HolderAuxiliary.Inv [] loans k k v ∧ result=(msg.length : Int) ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket), v.wg.dev=some d → d.rxSkbs[id]?≠some packet) := by
  unfold finish at run
  obtain ⟨x,u,j,crypt,tail⟩ := DecryptIteration.bind_normal run
  cases x
  have after := (HolderAuxDeferred.crypt initial loans before w h hi).choose_spec.2.2
  rw [crypt] at after
  have read : (liftWG getDev).run u =
      match u.wg.dev with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d => .ok (d,u) := by
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.RxDrainBoundary.«0».Leanux.Proofs.WG.Queues.RxCredits.readDev) u
  rw [runPrefix_bind,runPrefix_lift,read] at tail
  cases hd : u.wg.dev with
  | none => simp only [hd] at tail; cases tail
  | some d =>
    simp only [hd] at tail
    obtain ⟨x,t,l,drain,done⟩ := DecryptIteration.bind_normal tail
    cases x
    simp only [runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at done
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := done
    have membership : ∀ d',u.wg.dev=some d' → (!d'.decryptQueue.empty)∈
        [!d.handshakeQueue.empty,!d.decryptQueue.empty,!d.encryptQueue.empty,!d.txWorkQueue.isEmpty] := by
      intro d' eq
      have same := hd.symm.trans eq
      cases same
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    obtain ⟨suffix,hist,empty,noPackets,post⟩ := HolderAuxDeferred.drained_empty after membership drain
    have actual := (RxHistory.mixed_erases (requireDrainedPrefix_erases _ _) u j).symm.trans (congrArg Prod.fst drain)
    have same := (requireDrained_normal _ _ u t actual).1
    have account : Boundary [] loans u.wg := by
      obtain ⟨prior,priorEq,boundary⟩ := after.1.1
      have samePrior : prior=suffix := List.append_cancel_left (priorEq.symm.trans hist)
      simpa only [samePrior,empty] using boundary
    have finalAccount : Boundary [] loans t.wg := by simpa only [same] using account
    exact ⟨u,j,suffix,crypt,hist,empty,
      HolderInitial.at_cut finalAccount post.1.2 post.2.1 post.2.2,rfl,noPackets⟩

/-- This relation keeps the original source executions and the unique admission
ledger. No funding or completion property is a field of the relation. -/
def Outcome (cs next : Ledger) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) (w v : World)
    (h k : List RxHistory.Event) (result : Int) : Prop :=
  ∃ src u t j,
    runPrefix (front family port tos ll dest) w h=(.ok (src,u),h) ∧
    AdmissionSection.Step cs next msg src u t h j ∧
    runPrefix (finish msg) t j=(.ok (result,v),k)

theorem Outcome.source (outcome : Outcome cs next family port msg tos ll dest w v h k result) :
    runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k) := by
  obtain ⟨src,u,t,j,start,step,done⟩ := outcome
  rw [source_factor]
  simp only [runPrefix_bind,start,step.source,done]

theorem Outcome.unique (left : Outcome cs next family port msg tos ll dest w v h k result)
    (right : Outcome cs other family port msg tos ll dest w v h k result) : next=other := by
  obtain ⟨src,u,t,j,start,step,_⟩ := left
  obtain ⟨src',u',t',j',start',step',_⟩ := right
  rw [start] at start'
  obtain ⟨⟨rfl,rfl⟩,_⟩ := start'
  have same := step.source.symm.trans step'.source
  obtain ⟨⟨_,rfl⟩,rfl⟩ := same
  exact step.unique step'

/-- Original inject selects a real admission cut, then waits and checks its
actual queues. Optional absence is resolved by its own present-device guard. -/
theorem normal (account : Boundary cs loans w.wg)
    (physical : HolderDeviceCreate.OptionalPhysical w.wg)
    (owners : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg)
    (run : runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k)) :
    ∃ next, Outcome cs next family port msg tos ll dest w v h k result ∧
      HolderAuxiliary.Inv [] loans k k v ∧ result=(msg.length : Int) ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket), v.wg.dev=some d → d.rxSkbs[id]?≠some packet) := by
  rw [source_factor] at run
  obtain ⟨src,u,j,start,tail⟩ := DecryptIteration.bind_normal run
  have hist : j=h := by simpa only [start] using front_history (family:=family) (port:=port) (tos:=tos) (ll:=ll) (dest:=dest) w h
  subst j
  have same := front_store start
  have entry := HolderInitial.at_cut
    (HolderInitial.store account (congrArg (fun p : ProductStore43=>p.2.2.2) same))
    (HolderInitial.physical_present (optional_store physical same) (front_present start))
    (OwnerWorkers.store h w u same owners) (slots_store slots same)
  obtain ⟨x,t,j,sectionRun,done⟩ := DecryptIteration.bind_normal tail
  cases x
  obtain ⟨prior,next,priorEq,step,after⟩ := AdmissionSection.normal entry sectionRun
  have priorNil : prior=[] := by
    have len := congrArg List.length priorEq
    simp only [List.length_append] at len
    cases prior with
    | nil => rfl
    | cons x xs => simp only [List.length_cons] at len; omega
  have initial : remaining cs (NapiCarrier.removedPackets prior)=cs := by
    subst prior
    exact List.filter_eq_self.mpr (fun _ _=>rfl)
  rw [initial] at step
  obtain ⟨_,_,_,_,_,_,post,length,empty⟩ := finish_normal after done
  exact ⟨next,⟨src,u,t,j,start,step,done⟩,post,length,empty⟩

/-- Every Stop keeps the actual owner-safe journal. A normal result also
carries its source-selected admission outcome and complete empty RX account. -/
theorem ensures (cs : Ledger) (loans : Reservations) (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixEnsures (fun h w=>Boundary cs loans w.wg ∧ HolderDeviceCreate.OptionalPhysical w.wg ∧
      OwnerChecks.Inv h w ∧ CurrentSlots.Inv w.wg) OwnerChecks.Safe
      (RxHistory.inject family port msg tos ll dest)
      (fun result k v=>∃ w h next,Outcome cs next family port msg tos ll dest w v h k result ∧
        HolderAuxiliary.Inv [] loans k k v ∧ result=(msg.length : Int) ∧
        (∀ (d : Device) (id : SkbId) (packet : RxPacket), v.wg.dev=some d → d.rxSkbs[id]?≠some packet)) := by
  intro w h hi
  obtain ⟨suffix,hist,safe,_⟩ := OwnerTraffic.inject family port msg tos ll dest w h hi.2.2.1
  refine ⟨suffix,hist,safe,?_⟩
  cases actual : (runPrefix (RxHistory.inject family port msg tos ll dest) w h).1 with
  | error e => trivial
  | ok out =>
    obtain ⟨next,step,post,length,empty⟩ := normal hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 (Prod.ext actual rfl)
    exact ⟨w,h,next,step,post,length,empty⟩

end Leanux.Proofs.WG.Queues.RxCredits.InjectAccount
