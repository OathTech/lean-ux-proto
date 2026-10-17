import Leanux.Proofs.WG.Queues.FloodSection
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! Ordered flood occurrences follow the actual per-message route, fixture
send, receive and inline poll. A finite path records source executions and
ledger changes, with no account certificate embedded in its constructors. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.FloodLoop
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open DurableHolders

def route (family : Nat) (src : SkbSource) : RxHistory.Obs Unit := do
  if family == 4 then
    match ← liftPrefix (Net.routeOutput4 0 src.daddr) with
    | .error _ => liftPrefix (invariant "wg_flood: the datagram to wg0's port has no route")
    | .ok r =>
      if r.dev != LO_IFINDEX || r.src != src.saddr then
        liftPrefix (invariant "wg_flood: the route disagrees with the sender source")
      liftPrefix (Net.neighbourClassify LO_IFINDEX)
  liftPrefix fixtureSend

def one (family : Nat) (src : SkbSource) (msg : List UInt8) : RxHistory.Obs Unit := do
  route family src
  FloodSection.action msg src

theorem one_factor (family src msg) : one family src msg = (do
    if family == 4 then
      match ← liftPrefix (Net.routeOutput4 0 src.daddr) with
      | .error _ => liftPrefix (invariant "wg_flood: the datagram to wg0's port has no route")
      | .ok r =>
        if r.dev != LO_IFINDEX || r.src != src.saddr then
          liftPrefix (invariant "wg_flood: the route disagrees with the sender source")
        liftPrefix (Net.neighbourClassify LO_IFINDEX)
    liftPrefix fixtureSend
    FloodSection.action msg src) := by
  unfold one route
  by_cases family4 : (family==4)=true
  · simp only [ite_eq_left family4,bind_assoc]
    apply bind_congr_source (m:=RxHistory.Obs)
    intro r
    cases r with
    | error e => rfl
    | ok r =>
      by_cases wrong : (r.dev != LO_IFINDEX || r.src != src.saddr)=true
      · simp only [ite_eq_left wrong,bind_assoc]
      · simp only [ite_eq_right wrong,bind_assoc]
  · simp only [ite_eq_right family4]

theorem route_preserves : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
    (route family src) := by
  have safe : ∀ h w,HolderAuxiliary.Inv initial loans before h w → OwnerChecks.Safe h := fun _ _ hi=>hi.2.1.safe
  have store : ∀ h w v, productStoreView v=productStoreView w → HolderAuxiliary.Inv initial loans before h w → HolderAuxiliary.Inv initial loans before h v := fun _ _ _ same hi=>HolderAuxiliary.store hi same
  unfold route
  repeat' traffic_preserve_source safe using store

theorem route_history (w : World) (h : List RxHistory.Event) :
    (runPrefix (route family src) w h).2=h := by
  have frame : HistoryFrame some (route family src) := by
    unfold route
    repeat' first
      | exact HistoryFrame.lift _ _
      | exact HistoryFrame.pure _ _
      | apply HistoryFrame.bind
      | maintenance_intro
      | dsimp only
      | split
  simpa only [List.filterMap_some] using frame w h

def Step (family : Nat) (src : SkbSource) (msg : List UInt8)
    (cs next : Ledger) (w v : World) (h k : List RxHistory.Event) : Prop :=
  ∃ u, runPrefix (route family src) w h=(.ok ((),u),h) ∧
    FloodSection.Step cs next msg src u v h k

theorem Step.source (step : Step family src msg cs next w v h k) :
    runPrefix (one family src msg) w h=(.ok ((),v),k) := by
  obtain ⟨u,start,step⟩ := step
  simp only [one,runPrefix_bind,start,step.source]

theorem Step.unique (left : Step family src msg cs next w v h k)
    (right : Step family src msg cs other w v h k) : next=other := by
  obtain ⟨u,start,step⟩ := left
  obtain ⟨u',start',step'⟩ := right
  rw [start] at start'
  obtain ⟨⟨_,rfl⟩,_⟩ := start'
  exact step.unique step'

theorem one_normal (hi : HolderAuxiliary.Inv cs loans h h w)
    (run : runPrefix (one family src msg) w h=(.ok ((),v),k)) :
    ∃ next,Step family src msg cs next w v h k ∧ HolderAuxiliary.Inv next loans k k v := by
  obtain ⟨x,u,j,start,body⟩ := DecryptIteration.bind_normal run
  cases x
  have same : j=h := by simpa only [start] using route_history (family:=family) (src:=src) w h
  subst j
  have entry := (route_preserves (family:=family) (src:=src) w h hi).choose_spec.2.2
  rw [start] at entry
  obtain ⟨next,step,post⟩ := FloodSection.normal entry body
  exact ⟨next,⟨u,start,step⟩,post⟩

def loop (family : Nat) (src : SkbSource) (messages : List (List UInt8)) : RxHistory.Obs Unit := do
  for msg in messages do one family src msg

theorem loop_nil (family src) : loop family src [] = pure () := rfl

theorem loop_cons (family src msg messages) : loop family src (msg::messages) = (do
    one family src msg
    loop family src messages) := by
  simp only [loop,List.forIn_cons,bind_assoc,pure_bind]

inductive Path (family : Nat) (src : SkbSource) : List (List UInt8) →
    Ledger → World → List RxHistory.Event → Ledger → World → List RxHistory.Event → Prop
  | nil : Path family src [] cs w h cs w h
  | cons (step : Step family src msg cs middle w u h j)
      (tail : Path family src messages middle u j next v k) :
      Path family src (msg::messages) cs w h next v k

theorem Path.source (path : Path family src messages cs w h next v k) :
    runPrefix (loop family src messages) w h=(.ok ((),v),k) := by
  induction path with
  | nil => rfl
  | cons step tail ih => simp only [loop_cons,runPrefix_bind,step.source,ih]

theorem Path.appends (path : Path family src messages cs w h next v k) : ∃ suffix,k=h++suffix := by
  induction path with
  | nil => exact ⟨[],by simp⟩
  | cons step tail ih =>
    obtain ⟨u,_,step⟩ := step
    obtain ⟨a,ha⟩ := step.appends
    obtain ⟨b,hb⟩ := ih
    exact ⟨a++b,by rw [hb,ha,List.append_assoc]⟩

/-- Induction follows the actual ordered list, not membership. Each source
occurrence chooses its own ledger before the following occurrence begins. -/
theorem loop_normal (hi : HolderAuxiliary.Inv cs loans h h w)
    (run : runPrefix (loop family src messages) w h=(.ok ((),v),k)) :
    ∃ next,Path family src messages cs w h next v k ∧ HolderAuxiliary.Inv next loans k k v := by
  induction messages generalizing cs w h with
  | nil =>
    simp only [loop_nil,runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at run
    obtain ⟨⟨_,rfl⟩,rfl⟩ := run
    exact ⟨cs,.nil,hi⟩
  | cons msg messages ih =>
    rw [loop_cons] at run
    obtain ⟨x,u,j,first,tail⟩ := DecryptIteration.bind_normal run
    cases x
    obtain ⟨middle,step,atNext⟩ := one_normal hi first
    obtain ⟨next,path,post⟩ := ih atNext tail
    exact ⟨next,.cons step path,post⟩

theorem Path.unique (left : Path family src messages cs w h next v k)
    (right : Path family src messages cs w h other v k) : next=other := by
  induction left generalizing other with
  | nil => cases right; rfl
  | cons step tail ih =>
    cases right with
    | cons step' tail' =>
      have same := step.source.symm.trans step'.source
      obtain ⟨⟨_,rfl⟩,rfl⟩ := same
      have ledger := step.unique step'
      subst ledger
      exact ih tail'

end Leanux.Proofs.WG.Queues.RxCredits.FloodLoop
