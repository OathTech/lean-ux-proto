import Leanux.Proofs.WG.Queues.RxPollCaptureSupport
import Leanux.Proofs.WG.Queues.PollReleaseCaller
import Leanux.Proofs.WG.Queues.CarrierIdentity

/-! The original capture fixes the slot component of every removal stamp.
The proof follows the existing poll source and retains stopped prefixes;
it does not assume well-formed incoming allocation or event histories. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RemovalIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes RxJoint

def Shape (h : List RxJoint.Event) : Prop :=
  ∀ k ∈ removalKeys h, k.2.2.2 = k.2.1 + 1

def Context (pending : Option (SkbId × PacketStamp)) (h : List RxJoint.Event) : Prop :=
  Shape h ∧ ∀ p ∈ pending, p.2.2 = p.1 + 1

theorem quiet (pending : Option (SkbId × PacketStamp))
    (a : Obs α) (ha : Appends a) (hm : HistoryFrame removedStamp a) :
    PrefixPreserves (fun h _ => Context pending h) Shape a := by
  intro w h hi
  obtain ⟨tail, ht⟩ := ha w h
  have hs : Shape (runPrefix a w h).2 := by
    intro k hk
    have frame : removalKeys (runPrefix a w h).2 = removalKeys h := removalKeys_frame ha hm w h
    exact hi.1 k (frame ▸ hk)
  refine ⟨tail, ht, hs, ?_⟩
  cases (runPrefix a w h).1
  · trivial
  · exact ⟨hs, hi.2⟩

theorem access_shape (pending : Option (SkbId × PacketStamp))
    (a : PrefixM LifetimeEvent α) :
    PrefixPreserves (fun h _ => Context pending h) Shape (access a) :=
  quiet pending _ (access_appends a)
    (fun w h => focusPrefix_other Event.access accessEvent removedStamp (fun _ => rfl) a w h)

theorem lift_shape (pending : Option (SkbId × PacketStamp)) (a : Leanux.M α) :
    PrefixPreserves (fun h _ => Context pending h) Shape (liftPrefix a) :=
  quiet pending _ (Appends.lift a) (HistoryFrame.lift _ a)

theorem captured (skb : SkbId) :
    PrefixEnsures (fun h _ => Context none h) Shape (capture skb)
      (fun out h _ => Context (some (skb, out.2)) h) := by
  intro w h hi
  rw [capture_run]
  cases hg : (liftWG (getRxSkb skb)).run w with
  | error e => exact ⟨[], by simp, hi.1, True.intro⟩
  | ok out =>
    have hs : Shape (h ++ [readEvent skb (packetStamp w.wg skb)]) := by
      simpa only [Shape, removalKeys, List.filterMap_append, List.filterMap_cons,
        readEvent, removedKey, List.filterMap_nil, List.append_nil] using hi.1
    refine ⟨[readEvent skb (packetStamp w.wg skb)], rfl, hs, hs, ?_⟩
    intro p hp
    simp only [Option.mem_some_iff] at hp
    subst p
    rfl

theorem marked (n skb : Nat) (stamp : PacketStamp) :
    PrefixEnsures (fun h _ => Context (some (skb, stamp)) h) Shape
      (emitPrefix (.removed n skb stamp) : Obs Unit) (fun _ h _ => Context none h) := by
  intro w h hi
  have hs : Shape (h ++ [.removed n skb stamp]) := by
    intro k hk
    simp only [removalKeys, List.filterMap_append, List.filterMap_cons, removedKey,
      List.filterMap_nil, List.mem_append, List.mem_singleton] at hk
    rcases hk with old | rfl
    · exact hi.1 k old
    · exact hi.2 (skb, stamp) (by simp)
  exact ⟨[.removed n skb stamp], rfl, hs, hs, by simp⟩

theorem dropped (pid n skb : Nat) (stamp : PacketStamp) :
    PrefixEnsures (fun h _ => Context (some (skb, stamp)) h) Shape
      (drop pid n skb stamp) (fun _ h _ => Context none h) := by
  unfold drop
  exact PrefixEnsures.bind (Q := fun _ h _ => Context (some (skb, stamp)) h)
    (access_shape _ _) (fun _ => marked n skb stamp)

theorem bind_shape (pending : Option (SkbId × PacketStamp))
    (a : Obs α) (f : α → Obs β)
    (ha : PrefixPreserves (fun h _ => Context pending h) Shape a)
    (hf : ∀ x, PrefixEnsures (fun h _ => Context pending h) Shape (f x) Q) :
    PrefixEnsures (fun h _ => Context pending h) Shape (a >>= f) Q :=
  PrefixEnsures.bind (Q := fun _ h _ => Context pending h) ha hf

theorem option_shape (pending : Option (SkbId × PacketStamp))
    (out : Option RxJoint.Entry) (g : Gro) :
    PrefixPreserves (fun h _ => Context pending h) Shape
      (forIn out.toList g (fun e g => do let g' ← receive g e; pure (.yield g'))) :=
  PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.1)
    (fun e g => PrefixPreserves.bind
      (quiet pending _ (receive_appends g e) (receive_removed g e))
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.1) _))

theorem stop_shape (pending : Option (SkbId × PacketStamp))
    (a : Leanux.M Unit) (ha : ∀ w, ∃ e, a.run w = .error e) (f : Unit → Obs α) :
    PrefixEnsures (fun h _ => Context pending h) Shape
      (liftPrefix a >>= f) Q := by
  intro w h hi
  obtain ⟨e, he⟩ := ha w
  simp only [runPrefix_bind, runPrefix_lift, he]
  exact ⟨[], by simp, hi.1, True.intro⟩

theorem receipt_access (pending : Option (SkbId × PacketStamp))
    (a : PrefixM LifetimeEvent α) (f : RunWitness α → RxJoint.Event)
    (hf : ∀ r, removedStamp (f r) = none) :
    PrefixPreserves (fun h _ => Context pending h) Shape (receiptObserved (access a) f) :=
  quiet pending _ (access_appends a).receiptObserved
    ((show HistoryFrame removedStamp (access a) from
      fun w h => focusPrefix_other Event.access accessEvent removedStamp (fun _ => rfl) a w h).receiptObserved hf)

theorem receipt_lift (pending : Option (SkbId × PacketStamp))
    (a : Leanux.M α) (f : RunWitness α → RxJoint.Event) (hf : ∀ r, removedStamp (f r) = none) :
    PrefixPreserves (fun h _ => Context pending h) Shape (receiptObserved (liftPrefix a) f) :=
  quiet pending _ (Appends.lift a).receiptObserved ((HistoryFrame.lift _ a).receiptObserved hf)

macro "removal_shape_step" : tactic => `(tactic|
  repeat' first
    | exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
    | with_reducible apply stop_shape _ (invariant _) (fun _ => ⟨_, rfl⟩)
    | with_reducible apply stop_shape _ (unsupported _) (fun _ => ⟨_, rfl⟩)
    | with_reducible apply PrefixEnsures.bind (captured _)
    | with_reducible apply PrefixEnsures.bind (dropped _ _ _ _)
    | with_reducible apply bind_shape _ _ _ (quiet _ _ (consume_appends _ _ _ _ _ _) (consume_removed _ _ _ _ _ _))
    | with_reducible apply bind_shape _ _ _ (quiet _ _ (receive_appends _ _) (receive_removed _ _))
    | with_reducible apply bind_shape _ _ _ (quiet _ _ (flushAll_appends _) (flushAll_removed _))
    | with_reducible apply bind_shape _ _ _ (option_shape _ _ _)
    | with_reducible apply bind_shape _ _ _ (receipt_access _ _ _ (fun _ => rfl))
    | with_reducible apply bind_shape _ _ _ (receipt_lift _ _ _ (fun _ => rfl))
    | with_reducible apply bind_shape _ _ _ (access_shape _ _)
    | with_reducible apply bind_shape _ _ _ (lift_shape _ _)
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.1)
    | with_reducible apply PrefixEnsures.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split))

theorem poll_preserves (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h _ => Context none h) Shape (poll pid budget) := by
  change PrefixEnsures (fun h _ => Context none h) Shape _ (fun _ h _ => Context none h)
  unfold poll
  apply bind_shape none _ _ (lift_shape _ _)
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (Q := fun _ h _ => Context none h)
    · change PrefixPreserves (fun h _ => Context none h) Shape _
      apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.1)
      intro index acc
      change PrefixEnsures (fun h _ => Context none h) Shape _ (fun _ h _ => Context none h)
      removal_shape_step
    · intro acc
      removal_shape_step

theorem poll_shape (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    Shape (runPrefix (poll pid budget) w (seed prior)).2 := by
  have hi : Context none (seed prior) := by
    constructor
    · intro k hk
      rw [seed_removals] at hk
      contradiction
    · simp
  exact (poll_preserves pid budget w (seed prior) hi).choose_spec.2.1

theorem certificate_shape (certificate : PollReleaseCaller.Certificate cut n skb stamp history) :
    stamp.2 = skb + 1 := by
  obtain ⟨incoming,w,pid,budget,result,v,before,after,tail,_,_,run,_⟩ := certificate
  have hs := poll_shape pid budget w (RxHistory.prior incoming)
  apply hs (n,skb,stamp)
  rw [run]
  exact List.mem_filterMap.mpr ⟨.removed n skb stamp, by simp, rfl⟩

theorem certificate_stamp (certificate : PollReleaseCaller.Certificate cut n skb stamp history) :
    CarrierIdentity.stamp (PollCarrier.packetOfStamp stamp) = stamp := by
  have shape := certificate_shape certificate
  apply Prod.ext
  · rfl
  · change stamp.2 - 1 + 1 = stamp.2
    rw [shape]
    simp

/-- The captured removal's actual release occurs in the same final history,
with the canonical carrier identity, not just its truncated slot decode. -/
theorem certificate_release (certificate : PollReleaseCaller.Certificate cut n skb stamp history) :
    RxHistory.Released history (CarrierIdentity.stamp (PollCarrier.packetOfStamp stamp)) := by
  rw [certificate_stamp certificate]
  obtain ⟨incoming,w,pid,budget,result,v,before,after,tail,_,_,_,journal,released⟩ := certificate.release
  rw [journal, RxHistory.released_append, RxHistory.released_append]
  exact Or.inl (Or.inr released)

/-- A completed captured removal cannot also be a pending carrier in the
same final complete account. Repeated equal event values do not matter. -/
theorem certificate_absent (certificate : PollReleaseCaller.Certificate cut n skb stamp history)
    (entry : HolderEntry.Inv cs loans history w) :
    PollCarrier.packetOfStamp stamp ∉ cs.map Carrier.packet := by
  intro member
  obtain ⟨c,pending,identity⟩ := List.mem_map.mp member
  apply CarrierIdentity.entry_not_released entry pending
  rw [identity]
  exact certificate_release certificate

end Leanux.Proofs.WG.Queues.RxCredits.RemovalIdentity
