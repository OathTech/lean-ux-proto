import Leanux.Proofs.WG.Queues.RxPollPrefix
import Leanux.Proofs.Framing.Product

set_option maxHeartbeats 2000000
set_option pp.structureInstances false

/-! An original poll removes a prefix of its entry queue even if execution
later stops. Queue entries may repeat on arbitrary malformed inputs; this is
an order theorem and does not impose packet ownership. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes Std.Do

abbrev ProductRetainsRx (a : Leanux.M α) : Prop :=
  ProjectedAction (fun w : World => rxQueues w.wg) ResidentsRetained a

/-- Native retention enters the product contract through the actual adapter;
arbitrary product callbacks retain their independent original obligation. -/
theorem ProductRetainsRx.of_native {a : WG.M α} (h : RetainsRx a) :
    ProductRetainsRx (liftWG a) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  rw [liftWG_run] at hr
  cases he : (a.run w.wg).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y, g⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact (ProjectedAction.iff_run_ambient _ _ _).mp h _ _ _ _ _ he

def RemovalPrefix (entry removed : List SkbId) : Prop :=
  ∃ tail, entry = removed ++ tail

def PollInv (pid : PeerId) (entry removed : List SkbId) (w : World) : Prop :=
  ∃ tail, entry = removed ++ tail ∧ QueueIs pid tail w.wg

def Cached (pid : PeerId) (first : Option SkbId) (w : World) : Prop :=
  ∀ c, rxQueues w.wg pid = some c → c.queue.peeked = first

theorem PollInv.safe {pid entry h w} (hi : PollInv pid entry h w) : RemovalPrefix entry h :=
  ⟨hi.choose, hi.choose_spec.1⟩

theorem PollInv.retained {a : Leanux.M α} (ha : ProductRetainsRx a) {pid entry h w v x}
    (hi : PollInv pid entry h w) (hr : a.run w = .ok (x, v)) :
    PollInv pid entry h v := by
  obtain ⟨tail, he, hq⟩ := hi
  exact ⟨tail, he, QueueIs.retained ha pid tail w v x hq hr⟩

theorem Cached.retained {a : Leanux.M α} (ha : ProductRetainsRx a) {pid first w v x}
    (hi : Cached pid first w) (hr : a.run w = .ok (x, v)) : Cached pid first v :=
  fun c hc => hi c ((ProjectedAction.iff_run _ _ _).mp ha w x v hr pid c hc)

theorem poll_lift_retains {a : Leanux.M α} (ha : ProductRetainsRx a) (pid : PeerId) (entry : List SkbId) :
    PrefixPreserves (PollInv pid entry) (RemovalPrefix entry) (liftPrefix a) :=
  PrefixEnsures.lift a (fun _ _ => PollInv.safe)
    (fun _ _ _ _ hi hr => PollInv.retained ha hi hr)

theorem poll_lift_cached {a : Leanux.M α} (ha : ProductRetainsRx a) (pid : PeerId)
    (entry : List SkbId) (first : Option SkbId) :
    PrefixPreserves (fun h w => PollInv pid entry h w ∧ Cached pid first w)
      (RemovalPrefix entry) (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift
  · intro h w hi; exact hi.1.safe
  · intro h w x v hi hr
    exact ⟨PollInv.retained ha hi.1 hr, Cached.retained ha hi.2 hr⟩

theorem peekRxPrefix_spec (pid : PeerId) (entry : List SkbId) :
    PrefixEnsures (PollInv pid entry) (RemovalPrefix entry) (liftPrefix (liftWG (peekRxQueue pid)))
      (fun first h w => PollInv pid entry h w ∧ Cached pid first w) := by
  apply PrefixEnsures.lift
  · intro h w hi; exact hi.safe
  intro h w first v hi hr
  rw [liftWG_run] at hr
  cases hn : ((peekRxQueue pid).run w.wg).run w.ambient with
  | error e => simp [hn, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨first', g⟩, ambient⟩
    simp [hn, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    obtain ⟨tail, he, hq⟩ := hi
    obtain ⟨before, after, hb, ha, _, _, hall, hp, _⟩ :=
      peekRxQueue_normal pid w.wg g first' w.ambient ambient hn
    refine ⟨⟨tail, he, queueIs_of_at pid tail g after ha (hall.trans (hq before hb))⟩, ?_⟩
    intro c hc
    have hca : c = after := Option.some.inj (hc.symm.trans ha)
    simpa only [hca] using hp

/-- The event is appended after the original update. Both a failed update
and any later failed continuation therefore retain the exact prefix reached. -/
theorem dropRxPrefix_spec (pid : PeerId) (entry : List SkbId) (id : SkbId) :
    PrefixEnsures (fun h w => PollInv pid entry h w ∧ Cached pid (some id) w)
      (RemovalPrefix entry) (dropRxPrefix pid id) (fun _ => PollInv pid entry) := by
  intro w h hi
  simp only [dropRxPrefix, runPrefix_bind, runPrefix_lift, liftWG_run]
  cases hr : ((dropRxQueue pid).run w.wg).run w.ambient with
  | error e => exact ⟨[], by simp only [List.append_nil]; rfl, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨⟨u0, v⟩, ambient⟩
    cases u0
    obtain ⟨tail, he, hq⟩ := hi.1
    obtain ⟨before, after, hb, ha, _, _, hd⟩ :=
      dropRxQueue_normal pid w.wg v w.ambient ambient hr
    have hp := hi.2 before hb
    have ht : tail = id :: after.queue.all := by
      rw [← hq before hb, hd]
      simp [PrevQueue.all, PrevQueue.dropPeeked, hp]
    have he' : entry = (h ++ [id]) ++ after.queue.all := by
      simpa only [ht, List.append_assoc, List.singleton_append] using he
    exact ⟨[id], rfl, ⟨after.queue.all, he'⟩,
      ⟨after.queue.all, he', queueIs_of_at pid _ v after ha rfl⟩⟩

theorem rxGo_rxQueues (first : Option SkbId) : SameView rxQueues
    (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)) := by
  apply SameView.of_wp
  intro s
  have hs {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) := by
    apply hoare_liftSkb
    intro w d store hi hd
    unfold rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
  unfold Hoare at hs
  mvcgen [WG.andM, branch, invariant, AmbientM.branch, AmbientM.invariant, getRxSkb, hs]

theorem prefix_lift_safe (a : Leanux.M α) (entry : List SkbId) :
    PrefixEnsures (fun h _ => RemovalPrefix entry h) (RemovalPrefix entry)
      (liftPrefix a) (fun _ h _ => RemovalPrefix entry h) :=
  PrefixEnsures.lift a (fun _ _ hi => hi) (fun _ _ _ _ hi _ => hi)

theorem prefix_flush_safe (callback : List (List UInt8) → Leanux.M Unit)
    (entry : List SkbId) (gro : GroState) :
    PrefixEnsures (fun h _ => RemovalPrefix entry h) (RemovalPrefix entry)
      (napiGroFlushAllPrefix (fun bytes => liftPrefix (callback bytes)) gro)
      (fun _ h _ => RemovalPrefix entry h) := by
  apply napiGroFlushAllPrefix_preserves (I := fun h _ => RemovalPrefix entry h)
    (S := RemovalPrefix entry) _ (fun _ _ hi => hi)
  intro bytes
  exact prefix_lift_safe (callback bytes) entry

theorem prefix_invariant (why : String) (f : Unit → PrefixM SkbId α)
    (hs : ∀ h w, P h w → S h) :
    PrefixEnsures P S (liftPrefix (invariant why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by simp only [List.append_nil]; rfl, hs h w hi, True.intro⟩

theorem endpoint_rxQueues (src : SkbSource) : SameView rxQueues (endpointFromSkb src) := by
  apply SameView.of_wp
  intro s
  mvcgen [endpointFromSkb, branch, invariant, unsupported,
    AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]

/-- The complete original poll retains removal order on success and failure.
Batch callbacks can precede later removals, so every successful callback must
retain surviving receive queues. Deletion remains permitted. -/
theorem rxPollRemovals_spec (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ bytes, ProductRetainsRx (callback bytes)) (entry : List SkbId) :
    PrefixEnsures (PollInv pid entry) (RemovalPrefix entry)
      (rxPollRemovals pid budget callback) (fun _ h _ => RemovalPrefix entry h) := by
  have ambient {α : Type} (a : AmbientM α) :
      ProductRetainsRx (MonadLift.monadLift a : Leanux.M α) := by
    apply RetainsRx.of_same
    intro initial
    exact productAmbient_spec a (fun w => rxQueues w.wg = initial) (fun _ _ h => h)
  have branching (d : Decision) (b : Bool) : ProductRetainsRx (branch d b : Leanux.M Bool) :=
    ambient (AmbientM.branch d b)
  have stopped (why : String) : ProductRetainsRx (invariant why : Leanux.M Unit) :=
    ambient (AmbientM.invariant why)
  have skbs {α : Type} (a : SkbM α) : SameView rxQueues (liftSkb a) := by
    intro initial
    apply hoare_liftSkb
    intro w d store hi hd
    unfold rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
  unfold rxPollRemovals
  apply PrefixEnsures.bind (Q := fun _ => PollInv pid entry)
    (poll_lift_retains (branching _ _) pid entry)
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi.safe)
  · apply PrefixEnsures.bind (Q := fun _ => PollInv pid entry)
    · apply PrefixEnsures.preserves
      apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
      intro n acc
      apply PrefixEnsures.preserves
      apply PrefixEnsures.bind (peekRxPrefix_spec pid entry)
      intro first
      apply PrefixEnsures.bind (Q := fun _ h w => PollInv pid entry h w ∧ Cached pid first w)
        (poll_lift_cached (ProductRetainsRx.of_native (RetainsRx.of_same (rxGo_rxQueues first))) pid entry first)
      intro go
      split
      · exact PrefixEnsures.pure (fun _ _ hi => hi.1.safe) (fun _ _ hi => hi.1)
      · cases first with
        | some id =>
          dsimp only
          apply PrefixEnsures.bind (Q := fun _ h w => PollInv pid entry h w ∧ Cached pid (some id) w)
            (poll_lift_cached (ProductRetainsRx.of_native
              (RetainsRx.of_same (skbs (SkbStore.getRx id)))) pid entry (some id))
          intro pkt
          split
          · exact prefix_invariant _ _ (fun _ _ hi => hi.1.safe)
          · apply PrefixEnsures.bind (dropRxPrefix_spec pid entry id)
            intro dropped
            change PrefixPreserves (PollInv pid entry) (RemovalPrefix entry) _
            repeat' first
              | with_reducible exact (napiGroReceivePrefix_preserves _ (fun _ _ hi => hi.safe)
                  (fun bytes => poll_lift_retains (hc bytes) pid entry) _ _)
              | with_reducible exact poll_lift_retains (branching _ _) pid entry
              | with_reducible exact poll_lift_retains (ProductRetainsRx.of_native (RetainsRx.of_same (counterValidate_rxQueues _ _))) pid entry
              | with_reducible exact poll_lift_retains (ProductRetainsRx.of_native (RetainsRx.of_same (endpoint_rxQueues _))) pid entry
              | with_reducible exact poll_lift_retains (ProductRetainsRx.of_native (consumeDataDone_rxQueues _ _ _)) pid entry
              | with_reducible exact poll_lift_retains (ProductRetainsRx.of_native (RetainsRx.of_same (keypairPut_rxQueues _ _))) pid entry
              | with_reducible exact poll_lift_retains (ProductRetainsRx.of_native (peerPut_rxQueues _)) pid entry
              | (change PrefixPreserves _ _ (liftPrefix (liftWG (liftSkb (SkbStore.freeRx _)))); exact poll_lift_retains (ProductRetainsRx.of_native (RetainsRx.of_same (skbs _))) pid entry)
              | with_reducible exact poll_lift_retains (stopped _) pid entry
              | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
              | with_reducible apply PrefixPreserves.bind
              | with_reducible apply PrefixPreserves.ite
              | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
              | (with_reducible intro x; try dsimp only)
              | (with_reducible split)
        | none =>
          dsimp only
          exact prefix_invariant _ _ (fun _ _ hi => hi.1.safe)
    · intro acc
      apply PrefixEnsures.consequence (P := fun h _ => RemovalPrefix entry h)
        (Q := fun _ h _ => RemovalPrefix entry h)
      · repeat' first
          | with_reducible exact prefix_flush_safe callback entry _
          | with_reducible exact prefix_lift_safe _ entry
          | with_reducible exact PrefixEnsures.pure (fun _ _ hi => hi) (fun _ _ hi => hi)
          | with_reducible apply PrefixEnsures.bind
          | with_reducible apply PrefixEnsures.ite
          | (with_reducible intro x; try dsimp only)
          | (with_reducible split)
      · intro h w hi; exact hi.safe
      · intro x h w hi; exact hi

/-- Starting from the current resident's queue, every removal log, including
a failed poll's retained log, is a prefix of those exact entry occurrences. -/
theorem rxPollRemovals_prefix (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit) (w : World) (cell : RxQueueCell)
    (hcallback : ∀ bytes, ProductRetainsRx (callback bytes))
    (hc : rxQueues w.wg pid = some cell) :
    RemovalPrefix cell.queue.all (runPrefix (rxPollRemovals pid budget callback) w []).2 := by
  have hi : PollInv pid cell.queue.all [] w :=
    ⟨cell.queue.all, rfl, queueIs_of_at pid _ w.wg cell hc rfl⟩
  exact (rxPollRemovals_spec pid budget callback hcallback cell.queue.all w [] hi).choose_spec.2.1

end Leanux.Proofs.WG.Queues
