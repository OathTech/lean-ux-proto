import Leanux.WG.State

/-!
# `struct prev_queue` as data (W7 stream B)

docs/2026-10-06-w4-w7-transmit-bulk.md, section 5.1. `wg_prev_queue_dequeue`
(queueing.c:80-106) is the single-consumer MPSC dequeue whose decisions are
pointer compares; the mirror keeps the queue's data (`PrevQueue`,
`Leanux/WG/Types.lean`) and takes the same decisions on it: the stub at the
tail, an item after the tail, the re-stub. `wg_prev_queue_peek` and
`wg_prev_queue_drop_peeked` (queueing.h:143-155) keep the peeked item.
-/

namespace Leanux.WG
open Leanux

/-- `atomic_add_unless(&queue->count, 1, MAX_QUEUED_PACKETS)` then
    `__wg_prev_queue_enqueue` (queueing.c:72-78): the caller decides on the
    count (`.enqueuePeerQueueFull`); the item joins the head. -/
def PrevQueue.enqueue (q : PrevQueue α) (x : α) : PrevQueue α := { q with items := q.items ++ [x] }

/-- `queue->count`: enqueued, not dequeued. A peeked item was dequeued. -/
def PrevQueue.count (q : PrevQueue α) : Nat := q.items.length

/-- Every item the queue still holds, the peeked one first: a producer's
    `atomic_set_release` of a packet's state reaches it wherever it is. -/
def PrevQueue.all (q : PrevQueue α) : List α := q.peeked.toList ++ q.items

/-- `f` applied to the first item satisfying `p`, the peeked one first;
    `none` when no item does. -/
def PrevQueue.updateFirst (q : PrevQueue α) (p : α → Bool) (f : α → α) : Option (PrevQueue α) :=
  match q.peeked with
  | some x => if p x then some { q with peeked := some (f x) } else updateItems q
  | none => updateItems q
where
  updateItems (q : PrevQueue α) : Option (PrevQueue α) :=
    match q.items.findIdx? p with
    | some i => some { q with items := q.items.modify i f }
    | none => none

/-- wg_prev_queue_dequeue (queueing.c:80-106). `tail` is the stub, or the
    item returned next; `next` the entry after it. -/
def PrevQueue.dequeue (q : PrevQueue α) : M (Option α × PrevQueue α) := do
  let mut q := q
  -- `tail == STUB(queue)`
  if ← branch .prevQueueTailIsStub q.tailIsStub then
    -- `!next`: nothing after the stub
    if ← branch .prevQueueStubEmpty q.items.isEmpty then return (none, q)
    -- queue->tail = next; tail = next; next = NEXT(next)
    q := { q with tailIsStub := false }
  match q.items with
  | [] => invariant "prev_queue: a tail item without an entry"
  | x :: rest =>
    -- `if (next)`: an entry after the tail item
    if ← branch .prevQueueMoreRemain !rest.isEmpty then
      return (some x, { q with items := rest })   -- queue->tail = next; count--
    -- `tail != READ_ONCE(queue->head)`: a producer between its xchg and its
    -- NEXT write; on this one CPU the consumer never finds one (P5)
    if ← branch .prevQueueTailNotHead false then unsupported "prev_queue: a producer mid-enqueue (tail != head)"
    -- __wg_prev_queue_enqueue(queue, STUB(queue)); next = NEXT(tail): the stub
    if ← branch .prevQueueRestubNext true then
      return (some x, { q with items := [], tailIsStub := true })   -- queue->tail = STUB; count--
    invariant "prev_queue: the stub was not linked"

/-- wg_prev_queue_peek (queueing.h:143-148): the peeked item, else a dequeue
    that stays peeked. -/
def PrevQueue.peek (q : PrevQueue α) : M (Option α × PrevQueue α) := do
  if ← branch .prevQueuePeeked q.peeked.isSome then return (q.peeked, q)
  let (x, q) ← q.dequeue
  return (x, { q with peeked := x })

/-- wg_prev_queue_drop_peeked (queueing.h:150-153). -/
def PrevQueue.dropPeeked (q : PrevQueue α) : PrevQueue α := { q with peeked := none }

end Leanux.WG
