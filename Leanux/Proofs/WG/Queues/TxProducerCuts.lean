import Leanux.Proofs.WG.Queues.BatchAccount
import Leanux.Proofs.WG.Environment.BatchSource

/-! Original outbound batch source cuts. Ordinary routing/packet errors remain
normal CQEs; a reached WG call is recorded with its actual input and output.
These relations contain no success, singleton, ring-full or funding premise. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.ProducerCuts
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes

/-- Literal original xmit-item prefix, stopping immediately before wgXmit. -/
def xmitFront (d : Device) (family addr : Nat) (payload : List UInt8)
    (opts : XmitOpts) : Leanux.M (Except Int (List Packet × Nat)) := do
  match ← Net.routeLookup family 0 addr with
  | .error err => return .error err
  | .ok r =>
    if r.dev != WG0_IFINDEX then unsupported "a batch transmit to a local address (not into wg0)"
    if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
      unsupported "a transmit after an MTU change took the family's routes into wg0 down"
    fixtureSend
    let opts := { opts with routeMtu := opts.routeMtu <|> (if r.mtu != 0 then some r.mtu else none) }
    match ← xmitPackets family addr payload opts with
    | .error e => return .error e
    | .ok (pkts, mtu) =>
      xmitMulticastLoop family addr
      if family == 4 then Net.neighbourClassify WG0_IFINDEX
      return .ok (pkts, mtu)

/-- Equality holds for every source outcome, including all Stop arms. -/
theorem xmit_factor (d cqes family addr payload opts) :
    Environment.batchItemSource d cqes (.xmit family addr payload opts) = (do
      let prepared ← xmitFront d family addr payload opts
      match prepared with
      | .error err => return .yield (cqes ++ [err])
      | .ok (packets, mtu) =>
        let ret ← WG.wgXmit family addr packets mtu
        return .yield (cqes ++ [if ret == 0 then (payload.length : Int) else ret])) := by
  unfold Environment.batchItemSource xmitFront
  simp only [bind_assoc]
  apply RxCredits.bind_congr_source (m:=Leanux.M)
  intro route
  cases route with
  | error err => rfl
  | ok r =>
    by_cases localRoute : (r.dev != WG0_IFINDEX)=true
    · simp only [ite_eq_left localRoute,bind_assoc]
      rfl
    · simp only [ite_eq_right localRoute]
      by_cases unavailable : ((family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev))=true
      · simp only [ite_eq_left unavailable,bind_assoc]
        rfl
      · simp only [ite_eq_right unavailable,bind_assoc]
        apply RxCredits.bind_congr_source (m:=Leanux.M)
        intro sent
        apply RxCredits.bind_congr_source (m:=Leanux.M)
        intro prepared
        cases prepared with
        | error err => rfl
        | ok pair =>
          rcases pair with ⟨packets,mtu⟩
          dsimp only
          simp only [bind_assoc]
          apply RxCredits.bind_congr_source (m:=Leanux.M)
          intro multicast
          by_cases ipv4 : (family==4)=true
          · simp only [ite_eq_left ipv4,bind_assoc,pure_bind]
          · simp only [ite_eq_right ipv4,pure_bind]

/-- Source-selected outcome of one xmit occurrence, including ordinary errno. -/
inductive Cut (d : Device) (family addr : Nat) (payload : List UInt8)
    (opts : XmitOpts) (cqes : List Int) : List Int → World → World → Prop
  | rejected (front : (xmitFront d family addr payload opts).run w=.ok (.error err,v)) :
      Cut d family addr payload opts cqes (cqes++[err]) w v
  | reached (front : (xmitFront d family addr payload opts).run w=.ok (.ok (packets,mtu),u))
      (source : (liftWG (WG.wgXmit family addr packets mtu)).run u=.ok (ret,v)) :
      Cut d family addr payload opts cqes
        (cqes++[if ret==0 then (payload.length : Int) else ret]) w v

theorem Cut.source (cut : Cut d family addr payload opts cqes out w v) :
    (Environment.batchItemSource d cqes (.xmit family addr payload opts)).run w=
      .ok (.yield out,v) := by
  rw [xmit_factor]
  cases cut with
  | rejected front =>
    change ((xmitFront d family addr payload opts).run w >>= _) = _
    simp only [front]
    rfl
  | reached front source =>
    change ((xmitFront d family addr payload opts).run w >>= _) = _
    simp only [front]
    change ((liftWG (WG.wgXmit family addr _ _)).run _ >>= _) = _
    simp only [source]
    rfl

theorem xmit_normal
    (run : (Environment.batchItemSource d cqes (.xmit family addr payload opts)).run w=
      .ok (result,v)) :
    ∃ out,result=.yield out ∧ Cut d family addr payload opts cqes out w v := by
  rw [xmit_factor] at run
  obtain ⟨prepared,u,front,tail⟩ := RxCredits.bind_ok run
  cases prepared with
  | error err =>
    cases tail
    exact ⟨_,rfl,.rejected front⟩
  | ok pair =>
    rcases pair with ⟨packets,mtu⟩
    obtain ⟨ret,last,source,done⟩ := RxCredits.bind_ok tail
    cases done
    exact ⟨_,rfl,.reached front source⟩

def IsXmit : BatchItem → Prop
  | .xmit .. => True
  | .inject .. => False

def AllXmit (entries : List BatchItem) : Prop := ∀ item∈entries,IsXmit item

/-- The existing native loop, without a replacement interpreter. -/
def loop (d : Device) (entries : List BatchItem) (cqes : List Int) : Leanux.M (List Int) :=
  forIn entries cqes (fun item qs=>Environment.batchItemSource d qs item)

theorem loop_nil (d cqes) : loop d [] cqes=pure cqes := rfl

theorem loop_cons (d item entries cqes) : loop d (item::entries) cqes = (do
    let out ← Environment.batchItemSource d cqes item
    match out with
    | .done qs => pure qs
    | .yield qs => loop d entries qs) := by
  simp only [loop,List.forIn_cons]
  apply RxCredits.bind_congr_source (m:=Leanux.M)
  intro out
  cases out <;> rfl

/-- Ordered original source occurrences. The list position is retained even
when two input items or ordinary errno results have equal values. -/
inductive Path (d : Device) : List BatchItem → List Int → World → List Int → World → Prop
  | nil : Path d [] cqes w cqes w
  | cons (cut : Cut d family addr payload opts cqes middle w u)
      (tail : Path d entries middle u out v) :
      Path d (.xmit family addr payload opts::entries) cqes w out v

theorem Path.source (path : Path d entries cqes w out v) :
    (loop d entries cqes).run w=.ok (out,v) := by
  induction path with
  | nil => rfl
  | cons cut tail ih =>
    rw [loop_cons]
    change ((Environment.batchItemSource _ _ _).run _ >>= _) = _
    rw [cut.source]
    exact ih

theorem loop_normal (all : AllXmit entries)
    (run : (loop d entries cqes).run w=.ok (out,v)) :
    Path d entries cqes w out v := by
  induction entries generalizing cqes w with
  | nil =>
    cases run
    exact .nil
  | cons item entries ih =>
    have head := all item (List.mem_cons_self)
    have rest : AllXmit entries := fun x hx=>all x (List.mem_cons_of_mem item hx)
    cases item with
    | inject family port msg => contradiction
    | xmit family addr payload opts =>
      rw [loop_cons] at run
      obtain ⟨result,u,first,tail⟩ := RxCredits.bind_ok run
      obtain ⟨middle,rfl,cut⟩ := xmit_normal first
      exact .cons cut (ih rest tail)

/-- Selecting by source index exposes the actual prefix, selected item and
remaining suffix; equal item values do not collapse positions. -/
theorem Path.select (path : Path d entries cqes w out v)
    (selected : entries[index]?=some (.xmit family addr payload opts)) :
    ∃ before after u t,
      (loop d (entries.take index) cqes).run w=.ok (before,u) ∧
      Cut d family addr payload opts before after u t ∧
      (loop d (entries.drop (index+1)) after).run t=.ok (out,v) := by
  induction path generalizing index family addr payload opts with
  | nil => simp at selected
  | @cons f a p o qs middle w u entries out v cut tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq,BatchItem.xmit.injEq] at selected
      obtain ⟨rfl,rfl,rfl,rfl⟩ := selected
      exact ⟨qs,middle,w,u,rfl,cut,tail.source⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at selected
      obtain ⟨before,after,t,s,beforeRun,chosen,suffix⟩ := ih selected
      refine ⟨before,after,t,s,?_,chosen,?_⟩
      · simp only [List.take_succ_cons]
        rw [loop_cons]
        change ((Environment.batchItemSource _ _ _).run _ >>= _) = _
        rw [cut.source]
        exact beforeRun
      · simpa only [Nat.succ_add,List.drop_succ_cons] using suffix

def front : Leanux.M Device := do
  let some d := (← getWG).dev | unsupported "a batch without wg0"
  if !d.running then unsupported "a batch with wg0 down"
  for pid in d.peerList do requireNotPending pid "a batch while a handshake is queued"
  return d

def finish (entries : List BatchItem) (cqes : List Int) : Leanux.M Int := do
  modifyAmbient fun w=>{w with extraOut:=[("cqes",Lean.toJson cqes)]}
  afterBatch
  return entries.length

theorem batch_factor (entries : List BatchItem) : Env.batch entries = (do
    let d ← front
    let cqes ← loop d entries []
    finish entries cqes) := by
  rw [← Environment.batchSource_eq]
  unfold Environment.batchSource front finish loop
  simp only [bind_assoc]
  apply RxCredits.bind_congr_source (m:=Leanux.M)
  intro state
  cases state.dev with
  | none => rfl
  | some d =>
    by_cases down : (!d.running)=true
    · simp only [ite_eq_left down,bind_assoc]
      rfl
    · simp only [ite_eq_right down,bind_assoc]
      apply RxCredits.bind_congr_source (m:=Leanux.M)
      intro ignored
      simp only [pure_bind]

/-- Every normal original all-xmit batch has the complete ordered producer
path and its actual deferred tail. No successful leaf is supplied separately. -/
theorem batch_normal (all : AllXmit entries)
    (run : (Env.batch entries).run w=.ok (result,v)) :
    ∃ d u cqes t,front.run w=.ok (d,u) ∧ Path d entries [] u cqes t ∧
      (finish entries cqes).run t=.ok (result,v) := by
  rw [batch_factor] at run
  obtain ⟨d,u,started,rest⟩ := RxCredits.bind_ok run
  obtain ⟨cqes,t,produced,finished⟩ := RxCredits.bind_ok rest
  exact ⟨d,u,cqes,t,started,loop_normal all produced,finished⟩

/-- The unchanged persistent observer has exactly this same native source
path, for arbitrary incoming history; its actual complete history is retained. -/
theorem batch_observed (all : AllXmit entries)
    (run : runPrefix (RxHistory.batch entries) w history=(.ok (result,v),after)) :
    ∃ d u cqes t,front.run w=.ok (d,u) ∧ Path d entries [] u cqes t ∧
      (finish entries cqes).run t=.ok (result,v) :=
  batch_normal all ((RxHistory.batch_erases entries w history).symm.trans (congrArg Prod.fst run))

end Leanux.Proofs.WG.Queues.TxDisposition.ProducerCuts
