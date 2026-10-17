import Leanux.Proofs.WG.Queues.RxEnvBatchHistory
import Leanux.Proofs.Logged.ProjectsPrefix

/-! One original batch item with its concrete fixture, route, NET_RX section,
and CQE handling. Only the receive, poll, multicast and TX observers vary. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing

def batchItemWith {E : Type}
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (poll : PrefixM E Unit)
    (multicast : Nat → Nat → PrefixM E Unit)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (d : Device) (cqes : List Int) (item : BatchItem) : PrefixM E (ForInStep (List Int)) := do
  let mut cqes := cqes
  match item with
  | .inject family port msg =>
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
    runWorkerPrefix .netRx do
      receive msg src
      poll
    cqes := cqes ++ [(msg.length : Int)]
  | .xmit family addr payload opts =>
    match ← liftPrefix (Net.routeLookup family 0 addr) with
    | .error err => cqes := cqes ++ [err]
    | .ok r =>
      if r.dev != WG0_IFINDEX then liftPrefix (unsupported "a batch transmit to a local address (not into wg0)")
      if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
        liftPrefix (unsupported "a transmit after an MTU change took the family's routes into wg0 down")
      liftPrefix fixtureSend
      let opts := { opts with routeMtu := opts.routeMtu <|> (if r.mtu != 0 then some r.mtu else none) }
      match ← liftPrefix (xmitPackets family addr payload opts) with
      | .error e => cqes := cqes ++ [e]
      | .ok (pkts, mtu) =>
        multicast family addr
        if family == 4 then liftPrefix (Net.neighbourClassify WG0_IFINDEX)
        let ret ← xmit family addr pkts mtu
        cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  return .yield cqes

theorem batchItemAudit_factor (d : Device) (cqes : List Int) (item : BatchItem) :
    batchItemAudit d cqes item =
      batchItemWith (fun msg src => auditFocus (liftWGObserver (wgReceivePrefix msg src)))
        pollScheduledInlineAudit xmitMulticastLoopAudit
        (fun family addr pkts mtu => auditFocus (liftWGObserver (wgXmitPrefix family addr pkts mtu)))
        d cqes item := rfl

theorem rxBatchItem_factor (d : Device) (cqes : List Int) (item : BatchItem) :
    Queues.RxHistory.batchItem d cqes item =
      batchItemWith (fun msg src => Queues.RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src)))
        Queues.RxHistory.pollScheduledInline
        (fun family addr => Queues.RxHistory.audit (xmitMulticastLoopAudit family addr))
        (fun family addr pkts mtu => Queues.RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr pkts mtu)))
        d cqes item := rfl

/-- The original section entry/exit wraps the same product callback; Stops
retain the actually reached callback history without an invented section end. -/
theorem runWorkerPrefix_projects {E F : Type} (ρ : E → Option F) (worker : Worker)
    {g : PrefixM E Unit} {f : PrefixM F Unit} (hg : ProjectsPrefix ρ id g f) :
    ProjectsPrefix ρ id (runWorkerPrefix worker g) (runWorkerPrefix worker f) := by
  unfold runWorkerPrefix
  repeat' first
    | exact hg
    | exact projectsPrefix_lift ρ _
    | exact projectsPrefix_pure ρ id _
    | apply projectsPrefix_bind ρ id id
    | apply projectsPrefix_ite
    | maintenance_intro
    | dsimp only [id]
    | split

theorem batchItemWith_projects {E F : Type} (ρ : E → Option F)
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (receive' : List UInt8 → SkbSource → PrefixM F Unit)
    (poll : PrefixM E Unit) (poll' : PrefixM F Unit)
    (multicast : Nat → Nat → PrefixM E Unit) (multicast' : Nat → Nat → PrefixM F Unit)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (xmit' : Nat → Nat → List Packet → Nat → PrefixM F Int)
    (hr : ∀ msg src, ProjectsPrefix ρ id (receive msg src) (receive' msg src))
    (hp : ProjectsPrefix ρ id poll poll')
    (hm : ∀ family addr, ProjectsPrefix ρ id (multicast family addr) (multicast' family addr))
    (hx : ∀ family addr pkts mtu, ProjectsPrefix ρ id
      (xmit family addr pkts mtu) (xmit' family addr pkts mtu))
    (d : Device) (cqes : List Int) (item : BatchItem) :
    ProjectsPrefix ρ id (batchItemWith receive poll multicast xmit d cqes item)
      (batchItemWith receive' poll' multicast' xmit' d cqes item) := by
  cases item
  all_goals unfold batchItemWith
  all_goals repeat' first
    | with_reducible exact hr _ _
    | exact hp
    | with_reducible exact hm _ _
    | with_reducible exact hx _ _ _ _
    | (maintenance_head runWorkerPrefix; apply runWorkerPrefix_projects ρ)
    | exact projectsPrefix_lift ρ _
    | exact projectsPrefix_pure ρ id _
    | apply projectsPrefix_bind ρ id id
    | apply projectsPrefix_ite
    | maintenance_intro
    | dsimp only [id]
    | split

theorem batchItemWith_preserves {E : Type} {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (poll : PrefixM E Unit)
    (multicast : Nat → Nat → PrefixM E Unit)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (hr : ∀ msg src, PrefixPreserves I S (receive msg src)) (hp : PrefixPreserves I S poll)
    (hm : ∀ family addr, PrefixPreserves I S (multicast family addr))
    (hx : ∀ family addr pkts mtu, PrefixPreserves I S (xmit family addr pkts mtu))
    (d : Device) (cqes : List Int) (item : BatchItem) :
    PrefixPreserves I S (batchItemWith receive poll multicast xmit d cqes item) := by
  have frame {α : Type} (a : Leanux.M α) (ha : SameProductStore a) :
      PrefixPreserves I S (liftPrefix a) :=
    viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) safe store
      (ha.of_factor (fun s : ProductStore43 => s.2.2.2) _ (fun _ => rfl))
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I S (liftPrefix (MonadLift.monadLift a : Leanux.M α)) :=
    viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) safe store
      (fun initial => productAmbient_spec a (fun w => wgStoreView w.wg = initial) (fun _ _ hi => hi))
  have routing {α : Type} (a : Net.M α) :
      PrefixPreserves I S (liftPrefix (liftWG (liftRouting a))) :=
    frame _ (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have stable : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v :=
    fun h w v eq hi => store h w v (congrArg (fun s : ProductStore43 => s.2.2.2) eq) hi
  cases item
  all_goals unfold batchItemWith
  all_goals repeat' first
    | with_reducible exact hr _ _
    | exact hp
    | with_reducible exact hm _ _
    | with_reducible exact hx _ _ _ _
    | (traffic_head runWorkerPrefix; apply runWorkerPrefix_preserves safe stable)
    | (traffic_head routeOutput4; exact routing _)
    | (traffic_head routeLookup; exact routing _)
    | (traffic_head neighbourClassify; exact routing _)
    | (traffic_head senderSource; exact frame _ (senderSource_sameKernel _ _ _ _))
    | (traffic_head xmitPackets; exact frame _ (xmitPackets_sameKernel _ _ _ _))
    | (traffic_head fixtureSend; unfold Env.fixtureSend; exact ambient _)
    | (traffic_head unsupported; exact ambient (AmbientM.unsupported _))
    | (traffic_head invariant; exact ambient (AmbientM.invariant _))
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | maintenance_intro
    | dsimp only
    | split

theorem batchItemWith_appends {E : Type}
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (poll : PrefixM E Unit)
    (multicast : Nat → Nat → PrefixM E Unit)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (hr : ∀ msg src, Appends (receive msg src)) (hp : Appends poll)
    (hm : ∀ family addr, Appends (multicast family addr))
    (hx : ∀ family addr pkts mtu, Appends (xmit family addr pkts mtu))
    (d : Device) (cqes : List Int) (item : BatchItem) :
    Appends (batchItemWith receive poll multicast xmit d cqes item) := by
  have callback {α : Type} (a : PrefixM E α) (ha : Appends a) :
      PrefixPreserves (fun _ _ => True) (fun _ => True) a := by
    intro w h _
    obtain ⟨suffix,hs⟩ := ha w h
    refine ⟨suffix,hs,True.intro,?_⟩
    cases (runPrefix a w h).1 <;> trivial
  have checked := batchItemWith_preserves (I := fun _ _ => True) (S := fun _ => True)
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) receive poll multicast xmit
    (fun msg src => callback _ (hr msg src)) (callback _ hp)
    (fun family addr => callback _ (hm family addr))
    (fun family addr pkts mtu => callback _ (hx family addr pkts mtu)) d cqes item
  intro w h
  obtain ⟨suffix,hs,_,_⟩ := checked w h True.intro
  exact ⟨suffix,hs⟩

end Leanux.Proofs.WG.Lifetimes
