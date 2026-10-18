import Leanux.Proofs.WG.Queues.FloodLoop
import Leanux.Proofs.WG.Queues.HolderAuxDeferred
import Leanux.Proofs.WG.Origins.OwnerTraffic

/-! The original flood traverses its actual finite message list, with a
source-selected ledger at each NET_RX return. Its tail retains the remaining
ledger on both modes. Empty completion for placeholder scheduling is not
assumed or claimed here. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.FloodAccount
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open DurableHolders

def messages (count : Nat) (input : List (List UInt8)) : List (List UInt8) :=
  input ++ List.replicate count ([1] ++ List.replicate 115 0 ++ List.replicate 16 0xff ++ List.replicate 16 0)

def prepare (d : Device) (family port : Nat) : RxHistory.Obs SkbSource := do
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a flood to a port other than wg0's")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "a flood while a handshake is queued"))
  liftPrefix (senderSource family 0)

def front (family port : Nat) : RxHistory.Obs SkbSource := do
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a flood to a port other than wg0's (no wg0)")
  prepare d family port

def finish : RxHistory.Obs Int := do
  RxHistory.afterBatch
  let d ← liftPrefix (liftWG getDev)
  RxHistory.mixed (requireDrainedPrefix "the flood queued" [!d.handshakeQueue.empty,d.handshakeQueueLen != 0])
  return 0

theorem source_factor (count port family input) : RxHistory.flood count port family input = (do
    let src ← front family port
    FloodLoop.loop family src (messages count input)
    finish) := by
  rw [AdmissionCaller.flood_source]
  have stopped {α β : Type} (why : String) (next : α → RxHistory.Obs β) :
      ((liftPrefix (unsupported why) : RxHistory.Obs α) >>= next)=
        (liftPrefix (unsupported why) : RxHistory.Obs β) := rfl
  simp only [TrafficSource.floodWith,front,prepare,FloodLoop.loop,FloodLoop.one_factor,
    FloodSection.action,messages,finish,bind_assoc,bind_if_source,pure_bind,stopped]
  apply bind_congr_source (m:=RxHistory.Obs)
  intro state
  cases state.dev with
  | none => rfl
  | some d =>
    by_cases guard : (!d.running || port != d.incomingPort)=true
    · simp only [ite_eq_left guard,stopped]
    · simp only [ite_eq_right guard,bind_assoc]
      apply bind_congr_source (m:=RxHistory.Obs)
      intro ignored
      apply bind_congr_source (m:=RxHistory.Obs)
      intro src
      apply congrArg (fun a : RxHistory.Obs PUnit => a >>= fun _ => finish)
      congr 1
      funext msg ignored
      by_cases family4 : (family==4)=true
      · simp only [ite_eq_left family4]
        apply bind_congr_source (m:=RxHistory.Obs)
        intro route
        cases route with
        | error e => rfl
        | ok r =>
          by_cases wrong : (r.dev != LO_IFINDEX || r.src != src.saddr)=true
          · simp only [ite_eq_left wrong,bind_assoc]
          · simp only [ite_eq_right wrong,bind_assoc]
      · simp only [ite_eq_right family4]

private theorem prepare_preserves {I : List RxHistory.Event → World → Prop} {S : List RxHistory.Event → Prop}
    (safe : ∀ h w,I h w → S h)
    (store : ∀ h w v,productStoreView v=productStoreView w → I h w → I h v) :
    PrefixPreserves I S (prepare d family port) := by
  unfold prepare
  repeat' traffic_preserve_source safe using store

theorem front_preserves {I : List RxHistory.Event → World → Prop} {S : List RxHistory.Event → Prop}
    (safe : ∀ h w,I h w → S h)
    (store : ∀ h w v,productStoreView v=productStoreView w → I h w → I h v) :
    PrefixPreserves I S (front family port) := by
  unfold front
  repeat' first
    | exact prepare_preserves safe store
    | traffic_preserve_source safe using store

theorem front_history (w : World) (h : List RxHistory.Event) :
    (runPrefix (front family port) w h).2=h := by
  have frame : HistoryFrame some (front family port) := by
    unfold front prepare
    repeat' first
      | exact HistoryFrame.lift _ _
      | exact HistoryFrame.pure _ _
      | apply HistoryFrame.bind
      | apply HistoryFrame.forIn
      | maintenance_intro
      | dsimp only
      | split
  simpa only [List.filterMap_some] using frame w h

theorem front_store (run : runPrefix (front family port) w h=(.ok (src,v),k)) :
    productStoreView v=productStoreView w := by
  have kept := (front_preserves (family:=family) (port:=port)
    (I:=fun _ v=>productStoreView v=productStoreView w) (S:=fun _=>True)
    (fun _ _ _=>True.intro) (fun _ _ _ same hi=>same.trans hi) w h rfl).choose_spec.2.2
  simpa only [run] using kept

theorem front_present (run : runPrefix (front family port) w h=(.ok (src,v),k)) : v.wg.dev.isSome=true := by
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
    change (Except.error _ : Except Stop (SkbSource × World))=.ok (src,v) at impossible
    cases impossible
  | some d => rfl

theorem finish_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe finish := by
  have safe : ∀ h w,HolderAuxiliary.Inv initial loans before h w → OwnerChecks.Safe h := fun _ _ hi=>hi.2.1.safe
  have store : ∀ h w v,productStoreView v=productStoreView w → HolderAuxiliary.Inv initial loans before h w → HolderAuxiliary.Inv initial loans before h v := fun _ _ _ same hi=>HolderAuxiliary.store hi same
  unfold finish
  apply PrefixPreserves.bind (HolderAfterBatch.afterBatch initial loans before)
  intro x
  repeat' first
    | exact HolderAuxDeferred.drained initial loans before _ _
    | traffic_preserve_source safe using store

/-- Normal tails choose the exact fresh removal suffix. This conclusion does
not imply the suffix removes every packet in placeholder mode. -/
theorem finish_normal (hi : HolderAuxiliary.Inv cs loans h h w)
    (run : runPrefix finish w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ HolderAuxiliary.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k k v := by
  have post := (finish_preserves cs loans h w h hi).choose_spec.2.2
  rw [run] at post
  exact HolderInitial.rebase post

/-- Exact front, finite occurrence path, and actual final removal suffix.
Neither funding nor an empty endpoint is a field of this source relation. -/
def Outcome (cs next : Ledger) (count port family : Nat) (input : List (List UInt8))
    (w v : World) (h k : List RxHistory.Event) (result : Int) : Prop :=
  ∃ src u t j middle suffix,
    runPrefix (front family port) w h=(.ok (src,u),h) ∧
    FloodLoop.Path family src (messages count input) cs u h middle t j ∧
    runPrefix finish t j=(.ok (result,v),k) ∧
    k=j++suffix ∧ next=remaining middle (NapiCarrier.removedPackets suffix)

theorem Outcome.source (outcome : Outcome cs next count port family input w v h k result) :
    runPrefix (RxHistory.flood count port family input) w h=(.ok (result,v),k) := by
  obtain ⟨src,u,t,j,middle,suffix,start,path,done,_,_⟩ := outcome
  rw [source_factor]
  simp only [runPrefix_bind,start,path.source,done]

theorem Outcome.unique (left : Outcome cs next count port family input w v h k result)
    (right : Outcome cs other count port family input w v h k result) : next=other := by
  obtain ⟨src,u,t,j,middle,suffix,start,path,done,hist,ledger⟩ := left
  obtain ⟨src',u',t',j',middle',suffix',start',path',done',hist',ledger'⟩ := right
  rw [start] at start'
  obtain ⟨⟨rfl,rfl⟩,_⟩ := start'
  have same := path.source.symm.trans path'.source
  obtain ⟨⟨_,rfl⟩,rfl⟩ := same
  have mids := path.unique path'
  have tails := List.append_cancel_left (hist.symm.trans hist')
  rw [mids,tails] at ledger
  exact ledger.trans ledger'.symm

theorem normal (account : Boundary cs loans w.wg)
    (physical : HolderDeviceCreate.OptionalPhysical w.wg)
    (owners : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg)
    (run : runPrefix (RxHistory.flood count port family input) w h=(.ok (result,v),k)) :
    ∃ next,Outcome cs next count port family input w v h k result ∧ HolderAuxiliary.Inv next loans k k v := by
  rw [source_factor] at run
  obtain ⟨src,u,j,start,rest⟩ := DecryptIteration.bind_normal run
  have hist : j=h := by simpa only [start] using front_history (family:=family) (port:=port) w h
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
  obtain ⟨x,t,j,loopRun,done⟩ := DecryptIteration.bind_normal rest
  cases x
  obtain ⟨middle,path,atTail⟩ := FloodLoop.loop_normal entry loopRun
  obtain ⟨suffix,tailEq,post⟩ := finish_normal atTail done
  exact ⟨_,⟨src,u,t,j,middle,suffix,start,path,done,tailEq,rfl⟩,post⟩

/-- Replaying an independently supplied source outcome recovers precisely
its ledger, by same-execution uniqueness rather than an account field. -/
theorem Outcome.restore (outcome : Outcome cs next count port family input w v h k result)
    (account : Boundary cs loans w.wg) (physical : HolderDeviceCreate.OptionalPhysical w.wg)
    (owners : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg) :
    HolderAuxiliary.Inv next loans k k v := by
  obtain ⟨other,derived,post⟩ := normal account physical owners slots outcome.source
  exact (outcome.unique derived) ▸ post

/-- The native caller and original observer have the same execution; the
journal in this result is the original observer's output on that run. -/
theorem native_normal (account : Boundary cs loans w.wg)
    (physical : HolderDeviceCreate.OptionalPhysical w.wg)
    (owners : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg)
    (run : (Env.flood count port family input).run w=.ok (result,v)) :
    let k := (runPrefix (RxHistory.flood count port family input) w h).2
    ∃ next,Outcome cs next count port family input w v h k result ∧ HolderAuxiliary.Inv next loans k k v := by
  have actual := (RxHistory.flood_erases count port family input w h).trans run
  exact normal account physical owners slots (Prod.ext actual rfl)

/-- The same original Stop journals remain owner-safe. Dynamic ledger
certificates are asserted only for actual normal source endpoints. -/
theorem ensures (cs : Ledger) (loans : Reservations) (count port family : Nat) (input : List (List UInt8)) :
    PrefixEnsures (fun h w=>Boundary cs loans w.wg ∧ HolderDeviceCreate.OptionalPhysical w.wg ∧
      OwnerChecks.Inv h w ∧ CurrentSlots.Inv w.wg) OwnerChecks.Safe
      (RxHistory.flood count port family input)
      (fun result k v=>∃ w h next,Outcome cs next count port family input w v h k result ∧
        HolderAuxiliary.Inv next loans k k v) := by
  intro w h hi
  obtain ⟨suffix,hist,safe,_⟩ := OwnerTraffic.flood count port family input w h hi.2.2.1
  refine ⟨suffix,hist,safe,?_⟩
  cases actual : (runPrefix (RxHistory.flood count port family input) w h).1 with
  | error e => trivial
  | ok out =>
    obtain ⟨next,path,post⟩ := normal hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 (Prod.ext actual rfl)
    exact ⟨w,h,next,path,post⟩

end Leanux.Proofs.WG.Queues.RxCredits.FloodAccount
