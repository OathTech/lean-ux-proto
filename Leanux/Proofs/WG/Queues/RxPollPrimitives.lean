import Leanux.Proofs.WG.Queues.PrevQueue
import Leanux.Proofs.WG.Queues.RxCompletionFrame

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Original poll queue boundaries. These names only group the source's
existing operations; in particular dropping the cached head retains both
original getters. No successful endpoint is assumed for a malformed queue. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

def peekRxQueue (pid : PeerId) : M (Option SkbId) := do
  let (first, q) ← (← getPeer pid).rxQueue.peek
  setPeer pid { (← getPeer pid) with rxQueue := q }
  return first

def dropRxQueue (pid : PeerId) : M Unit := do
  setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked }

/-- The polled slot may have disappeared. Every resident must still carry
the stated logical queue; successful getters subsequently establish residency. -/
def QueueIs (pid : PeerId) (items : List SkbId) (w : World) : Prop :=
  ∀ c, rxQueues w pid = some c → c.queue.all = items

theorem QueueIs.retained {a : M α} (h : RetainsRx a) (pid : PeerId) (items : List SkbId)
    (w v : World) (x : α) (hi : QueueIs pid items w)
    (hr : a.run w = .ok (x, v)) : QueueIs pid items v :=
  fun c hc => hi c (h w x v hr pid c hc)

theorem getPeer_normal (pid : PeerId) (w v : World) (p : Peer)
    (hr : (getPeer pid).run w = .ok (p, v)) :
    v = w ∧ ∃ d, w.k.wg = some d ∧ d.peers[pid]? = some p := by
  have hv := (hoare_iff_triple _ _ _).mpr (Peers.getPeer_spec pid w) w p v rfl hr
  exact ⟨hv.1, hv.1 ▸ hv.2⟩

theorem rxQueues_at (w : World) (d : Device) (pid : PeerId) (p : Peer)
    (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p) :
    rxQueues w pid = some ⟨d.ifindex, p.internalId, p.rxQueue⟩ := by
  simp [rxQueues, rxMap, hd, hp]

theorem setPeer_queue_at (pid : PeerId) (p : Peer) (w v : World) (d : Device)
    (hd : w.k.wg = some d) (hr : (setPeer pid p).run w = .ok ((), v)) :
    rxQueues v pid = some ⟨d.ifindex, p.internalId, p.rxQueue⟩ := by
  cases hr
  simp [rxQueues, rxMap, hd]

theorem queueIs_of_at (pid : PeerId) (items : List SkbId) (w : World)
    (c : RxQueueCell) (hc : rxQueues w pid = some c) (hi : c.queue.all = items) :
    QueueIs pid items w := by
  intro other ho
  have he : other = c := Option.some.inj (ho.symm.trans hc)
  simpa only [he] using hi

/-- A complete original peek/cache update preserves logical contents and
leaves its returned head cached in the current resident. -/
theorem peekRxQueue_normal (pid : PeerId) (w v : World) (first : Option SkbId)
    (hr : (peekRxQueue pid).run w = .ok (first, v)) :
    ∃ before after, rxQueues w pid = some before ∧ rxQueues v pid = some after ∧
      before.epoch = after.epoch ∧ before.stamp = after.stamp ∧
      after.queue.all = before.queue.all ∧ after.queue.peeked = first ∧
      first = before.queue.all.head? := by
  simp only [peekRxQueue, StateT.run_bind] at hr
  cases hget : (getPeer pid).run w with
  | error e => simp [hget] at hr
  | ok out =>
    rcases out with ⟨p, u⟩
    obtain ⟨hu, d, hd, hp⟩ := getPeer_normal pid w u p hget
    subst u
    simp only [hget, CounterWindow.except_ok_bind] at hr
    cases hpeek : p.rxQueue.peek.run w with
    | error e => simp [hpeek] at hr
    | ok out =>
      rcases out with ⟨⟨head, q⟩, u⟩
      obtain ⟨hh, ha, hq, hk⟩ := prev_peek_normal p.rxQueue w u head q hpeek
      simp only [hpeek, CounterWindow.except_ok_bind] at hr
      cases hget2 : (getPeer pid).run u with
      | error e => simp [hget2] at hr
      | ok out =>
        rcases out with ⟨p2, u2⟩
        obtain ⟨hu2, d2, hd2, hp2⟩ := getPeer_normal pid u u2 p2 hget2
        subst u2
        have hd2eq : d2 = d := Option.some.inj (hd2.symm.trans (hk ▸ hd))
        subst d2
        have hp2eq : p2 = p := Option.some.inj (hp2.symm.trans hp)
        subst p2
        simp only [hget2, CounterWindow.except_ok_bind] at hr
        cases hset : (setPeer pid {p with rxQueue := q}).run u with
        | error e => simp [hset] at hr
        | ok out =>
          rcases out with ⟨u0, u2⟩
          cases u0
          simp only [hset, CounterWindow.except_ok_bind, StateT.run_pure] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨⟨d.ifindex, p.internalId, p.rxQueue⟩,
            ⟨d.ifindex, p.internalId, q⟩, rxQueues_at w d pid p hd hp,
            setPeer_queue_at pid {p with rxQueue := q} u v d hd2 hset,
            rfl, rfl, ha, hq, hh⟩

/-- The original two-getter update removes exactly the cached item. -/
theorem dropRxQueue_normal (pid : PeerId) (w v : World)
    (hr : (dropRxQueue pid).run w = .ok ((), v)) :
    ∃ before after, rxQueues w pid = some before ∧ rxQueues v pid = some after ∧
      after.epoch = before.epoch ∧ after.stamp = before.stamp ∧
      after.queue = before.queue.dropPeeked := by
  unfold dropRxQueue at hr
  rw [getPeer_twice] at hr
  simp only [StateT.run_bind] at hr
  cases hget : (getPeer pid).run w with
  | error e => simp [hget] at hr
  | ok out =>
    rcases out with ⟨p, u⟩
    obtain ⟨hu, d, hd, hp⟩ := getPeer_normal pid w u p hget
    subst u
    simp only [hget, CounterWindow.except_ok_bind] at hr
    exact ⟨⟨d.ifindex, p.internalId, p.rxQueue⟩,
      ⟨d.ifindex, p.internalId, p.rxQueue.dropPeeked⟩,
      rxQueues_at w d pid p hd hp,
      setPeer_queue_at pid {p with rxQueue := p.rxQueue.dropPeeked} w v d hd hr,
      rfl, rfl, rfl⟩

end Leanux.Proofs.WG.Queues
