import Leanux.Proofs.WG.Queues.PrevQueue
import Leanux.Proofs.WG.Queues.RxCompletionFrame

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Original poll queue boundaries. These names only group the source's
existing operations; in particular dropping the cached head retains both
original getters. No successful endpoint is assumed for a malformed queue. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

def peekRxQueue (pid : PeerId) : WG.M (Option SkbId) := do
  let (first, q) ← (← getPeer pid).rxQueue.peek
  setPeer pid { (← getPeer pid) with rxQueue := q }
  return first

def dropRxQueue (pid : PeerId) : WG.M Unit := do
  setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked }

/-- The polled slot may have disappeared. Every resident must still carry
the stated logical queue; successful getters subsequently establish residency. -/
def QueueIs (pid : PeerId) (items : List SkbId) (w : WGWorld) : Prop :=
  ∀ c, rxQueues w pid = some c → c.queue.all = items

theorem QueueIs.retained {S α : Type} {project : S → WGWorld}
    {a : StateT S (Except Stop) α}
    (h : ProjectedAction (fun w => rxQueues (project w)) ResidentsRetained a)
    (pid : PeerId) (items : List SkbId) (w v : S) (x : α)
    (hi : QueueIs pid items (project w))
    (hr : a.run w = .ok (x, v)) : QueueIs pid items (project v) :=
  fun c hc => hi c ((ProjectedAction.iff_run _ _ _).mp h w x v hr pid c hc)

theorem QueueIs.retained_native {a : WG.M α} (h : RetainsRx a)
    (pid : PeerId) (items : List SkbId) (w v : WGWorld)
    (ambient ambient' : Ambient) (x : α) (hi : QueueIs pid items w)
    (hr : (a.run w).run ambient = .ok ((x, v), ambient')) : QueueIs pid items v :=
  fun c hc => hi c ((ProjectedAction.iff_run_ambient _ _ _).mp h
    w ambient x v ambient' hr pid c hc)

theorem getPeer_normal (pid : PeerId) (w v : WGWorld) (p : Peer)
    (ambient ambient' : Ambient)
    (hr : ((getPeer pid).run w).run ambient = .ok ((p, v), ambient')) :
    v = w ∧ ambient' = ambient ∧ ∃ d, w.dev = some d ∧ d.peers[pid]? = some p := by
  have hv := (hoare_iff_run _ _ _).mp
    (Peers.getPeer_spec pid w ambient w) ambient (p, v) ambient' ⟨rfl, rfl⟩ hr
  exact ⟨hv.1, hv.2.1, hv.1 ▸ hv.2.2⟩

theorem rxQueues_at (w : WGWorld) (d : Device) (pid : PeerId) (p : Peer)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p) :
    rxQueues w pid = some ⟨d.ifindex, p.internalId, p.rxQueue⟩ := by
  simp [rxQueues, rxMap, hd, hp]

theorem setPeer_queue_at (pid : PeerId) (p : Peer) (w v : WGWorld) (d : Device)
    (ambient ambient' : Ambient) (hd : w.dev = some d)
    (hr : ((setPeer pid p).run w).run ambient = .ok (((), v), ambient')) :
    rxQueues v pid = some ⟨d.ifindex, p.internalId, p.rxQueue⟩ := by
  cases hr
  simp [rxQueues, rxMap, hd]

theorem queueIs_of_at (pid : PeerId) (items : List SkbId) (w : WGWorld)
    (c : RxQueueCell) (hc : rxQueues w pid = some c) (hi : c.queue.all = items) :
    QueueIs pid items w := by
  intro other ho
  have he : other = c := Option.some.inj (ho.symm.trans hc)
  simpa only [he] using hi

/-- A complete original peek/cache update preserves logical contents and
leaves its returned head cached in the current resident. -/
theorem peekRxQueue_normal (pid : PeerId) (w v : WGWorld) (first : Option SkbId)
    (ambient ambient' : Ambient)
    (hr : ((peekRxQueue pid).run w).run ambient = .ok ((first, v), ambient')) :
    ∃ before after, rxQueues w pid = some before ∧ rxQueues v pid = some after ∧
      before.epoch = after.epoch ∧ before.stamp = after.stamp ∧
      after.queue.all = before.queue.all ∧ after.queue.peeked = first ∧
      first = before.queue.all.head? := by
  simp only [peekRxQueue, StateT.run_bind] at hr
  cases hget : ((getPeer pid).run w).run ambient with
  | error e => simp [hget] at hr
  | ok out =>
    rcases out with ⟨⟨p, u⟩, a⟩
    obtain ⟨hu, hau, d, hd, hp⟩ := getPeer_normal pid w u p ambient a hget
    subst u
    subst a
    simp only [hget, CounterWindow.except_ok_bind] at hr
    cases hpeek : (p.rxQueue.peek.run w).run ambient with
    | error e => simp [hpeek] at hr
    | ok out =>
      rcases out with ⟨⟨⟨head, q⟩, u⟩, a⟩
      obtain ⟨hh, ha, hq, hk⟩ := prev_peek_normal p.rxQueue w u ambient a head q hpeek
      simp only [hpeek, CounterWindow.except_ok_bind] at hr
      cases hget2 : ((getPeer pid).run u).run a with
      | error e => simp [hget2] at hr
      | ok out =>
        rcases out with ⟨⟨p2, u2⟩, a2⟩
        obtain ⟨hu2, hau2, d2, hd2, hp2⟩ := getPeer_normal pid u u2 p2 a a2 hget2
        subst u2
        subst a2
        have hd2eq : d2 = d := Option.some.inj (hd2.symm.trans (hk ▸ hd))
        subst d2
        have hp2eq : p2 = p := Option.some.inj (hp2.symm.trans hp)
        subst p2
        simp only [hget2, CounterWindow.except_ok_bind] at hr
        cases hset : ((setPeer pid {p with rxQueue := q}).run u).run a with
        | error e => simp [hset] at hr
        | ok out =>
          rcases out with ⟨⟨u0, u2⟩, a2⟩
          cases u0
          simp only [hset, CounterWindow.except_ok_bind, StateT.run_pure] at hr
          cases hr
          exact ⟨⟨d.ifindex, p.internalId, p.rxQueue⟩,
            ⟨d.ifindex, p.internalId, q⟩, rxQueues_at w d pid p hd hp,
            setPeer_queue_at pid {p with rxQueue := q} u v d a ambient' hd2 hset,
            rfl, rfl, ha, hq, hh⟩

/-- The original two-getter update removes exactly the cached item. -/
theorem dropRxQueue_normal (pid : PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((dropRxQueue pid).run w).run ambient = .ok (((), v), ambient')) :
    ∃ before after, rxQueues w pid = some before ∧ rxQueues v pid = some after ∧
      after.epoch = before.epoch ∧ after.stamp = before.stamp ∧
      after.queue = before.queue.dropPeeked := by
  unfold dropRxQueue at hr
  rw [getPeer_twice] at hr
  simp only [StateT.run_bind] at hr
  cases hget : ((getPeer pid).run w).run ambient with
  | error e => simp [hget] at hr
  | ok out =>
    rcases out with ⟨⟨p, u⟩, a⟩
    obtain ⟨hu, hau, d, hd, hp⟩ := getPeer_normal pid w u p ambient a hget
    subst u
    subst a
    simp only [hget, CounterWindow.except_ok_bind] at hr
    exact ⟨⟨d.ifindex, p.internalId, p.rxQueue⟩,
      ⟨d.ifindex, p.internalId, p.rxQueue.dropPeeked⟩,
      rxQueues_at w d pid p hd hp,
      setPeer_queue_at pid {p with rxQueue := p.rxQueue.dropPeeked}
        w v d ambient ambient' hd hr,
      rfl, rfl, rfl⟩

end Leanux.Proofs.WG.Queues
