import Leanux.WG.State

/-!
# `struct ptr_ring` as data (simulation-target review, section 4.1)

`include/linux/ptr_ring.h`: on this one CPU, the producer cursor, the consumer
head (the next valid entry), the consumer tail (the next entry to invalidate),
the size, the batch, and the slots' occupancy (`Leanux/WG/Types.lean`,
`PtrRing`). Produce fails when the producer's slot is occupied
(`__ptr_ring_produce`, :104-116); consumption advances the head and leaves
the consumed slot occupied until a batch of entries has been consumed, or
the ring's end is reached, when the consumed slots are cleared in one go
(`__ptr_ring_discard_one`, :247-289). The full test is therefore physical
occupancy, not the logical count: enqueue one item, consume it, enqueue 1023
more, and the next produce fails although 1023 items are queued, because the
slot the first item used is still occupied. The logical FIFO (`PtrRing.items`)
is a derived view. A WireGuard crypt ring has 1024 slots and batch 16
(`wg_packet_queue_init`, `ptr_ring_init`, `PtrRing.init`).
-/

namespace Leanux.WG

/-- `__ptr_ring_full` (:49-52): `r->queue[r->producer]` is occupied (a ring of
    size 0 is always full, as `__ptr_ring_produce`'s first test). -/
def PtrRing.full (r : PtrRing α) : Bool :=
  r.size == 0 || ((r.slots[r.producer]?).getD none).isSome

/-- `__ptr_ring_produce` (:104-116) after its full test: the item in the
    producer's slot, the producer advanced and wrapped at the size. -/
def PtrRing.produce (r : PtrRing α) (x : α) : PtrRing α :=
  let producer := r.producer + 1
  { r with slots := r.slots.set! r.producer (some x),
           producer := if producer ≥ r.size then 0 else producer }

/-- `__ptr_ring_peek` (:169-174): the consumer head's slot. -/
def PtrRing.peek (r : PtrRing α) : Option α :=
  if r.size == 0 then none else (r.slots[r.consumerHead]?).getD none

/-- `__ptr_ring_empty` (:194-199): the consumer head's slot is free. -/
def PtrRing.empty (r : PtrRing α) : Bool := r.peek.isNone

/-- `__ptr_ring_discard_one` (:247-289), after a peek returned an item: the
    head advances; once `batch` entries have been consumed since the tail,
    or the head reaches the ring's end, the consumed slots from the old head
    down to the tail are cleared and the tail catches up; at the ring's end
    both cursors wrap to 0. -/
def PtrRing.discardOne (r : PtrRing α) : PtrRing α :=
  let head := r.consumerHead
  let consumerHead := r.consumerHead + 1
  let (slots, consumerTail) :=
    if consumerHead - r.consumerTail ≥ r.batch || consumerHead ≥ r.size then
      (clear r.slots head r.consumerTail, consumerHead)
    else (r.slots, r.consumerTail)
  let (consumerHead, consumerTail) :=
    if consumerHead ≥ r.size then (0, 0) else (consumerHead, consumerTail)
  { r with slots, consumerHead, consumerTail }
where
  /-- `while (likely(head >= r->consumer_tail)) r->queue[head--] = NULL;` -/
  clear (slots : Array (Option α)) (head tail : Nat) : Array (Option α) :=
    (List.range (head + 1 - tail)).foldl (fun s i => s.set! (head - i) none) slots

/-- `__ptr_ring_consume` (:291-303): the peek, and the discard when it
    returned an item. -/
def PtrRing.consume (r : PtrRing α) : Option α × PtrRing α :=
  match r.peek with
  | some x => (some x, r.discardOne)
  | none => (none, r)

/-- The logical count: the slots from the consumer head to the producer, the
    whole ring when the producer has come round to a live head. `ptr_ring`
    keeps no such count; `wg_prev_queue` keeps its own. -/
def PtrRing.count (r : PtrRing α) : Nat :=
  if r.size == 0 then 0
  else if r.producer == r.consumerHead then (if r.peek.isSome then r.size else 0)
  else (r.producer + r.size - r.consumerHead) % r.size

/-- The logical FIFO, oldest first: a derived view of the slots. -/
def PtrRing.items (r : PtrRing α) : List α :=
  (List.range r.count).filterMap fun i => (r.slots[(r.consumerHead + i) % r.size]?).getD none

-- The review's counterexample (4.1): one item produced and consumed, then
-- 1023 more; the ring is full to the C's test (the first slot is still
-- occupied) while 1023 items are queued, which a count-based test permits.
#guard
  let r : PtrRing Nat := PtrRing.init 1024
  let r := r.produce 0
  let (x, r) := r.consume
  let r := (List.range 1023).foldl (fun r i => r.produce (i + 1)) r
  x == some 0 && r.full && r.count == 1023 && r.items.length == 1023

-- The batch rule: 16 consumed entries clear their slots at once; 15 do not.
#guard
  let r : PtrRing Nat := (List.range 32).foldl (fun r i => r.produce i) (PtrRing.init 1024)
  let r15 := (List.range 15).foldl (fun r _ => (r.consume).2) r
  let r16 := (r15.consume).2
  (r15.slots[0]?).getD none == some 0 && r15.consumerTail == 0
    && (r16.slots[0]?).getD none == none && r16.consumerTail == 16 && r16.count == 16

-- The handshake ring (B1, docs/2026-10-15-design-b1-handshake-ring.md 4.4):
-- 4096 slots, batch 16; 25 produced and consumed leave slots 16 to 24
-- occupied (25 = 16 + 9), then 4087 produces succeed and the 4088th finds the
-- ring full. At batch 32 the 25 would all be carried and only 4071 would fit:
-- the guard discriminates the batch, as the corpus twin `e_ring_carry` does
-- (measured on the oracle: 4087 of 4088).
#guard
  let r : PtrRing Nat := PtrRing.init MAX_QUEUED_INCOMING_HANDSHAKES
  let r := (List.range 25).foldl (fun r i => r.produce i) r
  let r := (List.range 25).foldl (fun r _ => (r.consume).2) r
  let carried := (List.range 25).filter fun i => ((r.slots[i]?).getD none).isSome
  let r' := (List.range 4087).foldl (fun r i => r.produce (100 + i)) r
  r.batch == 16 && r.count == 0 && r.consumerTail == 16 && carried == List.range' 16 9
    && !r.full && r'.count == 4087 && r'.full

-- Wrap at the ring's end: both cursors return to 0 and the slots are cleared.
#guard
  let r : PtrRing Nat := (List.range 1024).foldl (fun r i => r.produce i) (PtrRing.init 1024)
  let r := (List.range 1024).foldl (fun r _ => (r.consume).2) r
  r.empty && r.count == 0 && r.consumerHead == 0 && r.consumerTail == 0 && !r.full

end Leanux.WG
