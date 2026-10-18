import Leanux.Proofs.WG.Roaming.ConsumedEndpointModel
import Leanux.Proofs.WG.Noise.CounterConsumeSource
import Leanux.Proofs.WG.Roaming.EndpointClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ConsumedEndpoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes RxJoint
variable {α β : Type}

theorem lift_checks (a : Leanux.M α) :
    PrefixPreserves (fun h _ => Checks h) Checks (liftPrefix a) := by
  intro w h hi
  refine ⟨[],by simp,hi,?_⟩
  simp only [runPrefix_lift]
  cases a.run w <;> trivial

theorem access_checks (a : PrefixM LifetimeEvent α) :
    PrefixPreserves (fun h _ => Checks h) Checks (access a) := by
  intro w h hi
  let suffix := ((runPrefix a w (h.filterMap accessEvent)).2.drop
    (h.filterMap accessEvent).length).map Event.access
  have next : Checks (h ++ suffix) := checks_append hi (by
    intro e member
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp member
    trivial)
  refine ⟨suffix,rfl,next,?_⟩
  cases (runPrefix (access a) w h).1 <;> trivial

theorem emit_checks (e : RxJoint.Event) (he : EventFacts e) :
    PrefixPreserves (fun h _ => Checks h) Checks (emitPrefix (State := World) e) := by
  intro w h hi
  exact ⟨[e],rfl,checks_snoc hi e he,checks_snoc hi e he⟩

theorem receipt_checks (a : Obs α) (event : RunWitness α → RxJoint.Event)
    (keep : PrefixPreserves (fun h _ => Checks h) Checks a)
    (he : ∀ r, EventFacts (event r)) :
    PrefixPreserves (fun h _ => Checks h) Checks (receiptObserved a event) := by
  unfold receiptObserved
  exact keep.captureObserved.bind (fun r => (emit_checks (event r) (he r)).bind
    (fun _ => PrefixPreserves.pure (I := fun h (_ : World) => Checks h) (fun _ _ hi => hi) _))

theorem capture_checks (id : SkbId) :
    PrefixPreserves (fun h _ => Checks h) Checks (capture id) := by
  intro w h hi
  obtain ⟨s,he,hs,hn⟩ := access_checks (liftWGObserver (getRxSkbPrefix id)) w h hi
  refine ⟨s,he,hs,?_⟩
  cases (runPrefix (capture id) w h).1 <;> trivial

theorem drop_checks (pid n id : Nat) (stamp : PacketStamp) :
    PrefixPreserves (fun h _ => Checks h) Checks (drop pid n id stamp) := by
  unfold drop
  exact (access_checks _).bind (fun _ => emit_checks _ True.intro)

theorem consume_checks (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (ep : Endpoint) (source : ep = sourceEndpoint pkt.source)
    (family : pkt.source.family = 4 ∨ pkt.source.family = 6) :
    PrefixPreserves (fun h _ => Checks h) Checks (consume pid n id stamp pkt ep) := by
  intro w h hi
  obtain ⟨suffix,append,safety,normal⟩ := access_checks
    (liftWGObserver (consumeDataDonePrefix pid pkt ep)) w h hi
  rw [consume_run]
  cases run : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t =>
    simp only [run] at append safety normal
    cases result with
    | error stop => exact ⟨suffix,append,safety,True.intro⟩
    | ok out =>
      obtain ⟨returned,v⟩ := out
      let r : RxDisposition.ConsumeReceipt := ⟨pid,pkt,ep,⟨returned,w.wg,v.wg,w.ambient,v.ambient⟩⟩
      have next := checks_snoc safety (.consumed n id stamp r) ⟨source,family⟩
      cases returned with
      | none => exact ⟨suffix ++ [_],by simp only [append,List.append_assoc]; rfl,next,next⟩
      | some bytes =>
        have last := checks_snoc next (.buffered ⟨⟨n,id,bytes⟩,stamp,some r⟩) True.intro
        exact ⟨suffix ++ [_,_],by simp only [append,List.append_assoc]; rfl,last,last⟩

theorem endpoint_return (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixEnsures (fun h _ => Checks h) Checks
      (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
        (Event.checkedEndpoint n id stamp pkt))
      (fun ep h _ => Checks h ∧ ep = some (sourceEndpoint pkt.source) ∧
        (pkt.source.family = 4 ∨ pkt.source.family = 6)) := by
  intro w h hi
  rw [runPrefix_receiptObserved,runPrefix_lift]
  cases run : (liftWG (endpointFromSkb pkt.source)).run w with
  | error stop => exact ⟨[],by simp,hi,True.intro⟩
  | ok out =>
    obtain ⟨ep,v⟩ := out
    have native := run
    rw [liftWG_run] at native
    cases hr : ((endpointFromSkb pkt.source).run w.wg).run w.ambient with
    | error stop => simp [hr,Except.map] at native
    | ok out =>
      obtain ⟨⟨value,g⟩,ambient⟩ := out
      simp only [hr,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
      obtain ⟨rfl,rfl⟩ := native
      obtain ⟨_,value,family⟩ := (Noise.ensures_iff _ _ _).mpr
        (endpointFromSkb_exact pkt.source (fun _ => True))
        w.wg w.ambient value g ambient True.intro hr
      exact ⟨[_],rfl,checks_snoc hi _ True.intro,checks_snoc hi _ True.intro,value,family⟩

theorem branch_const {P : List Event → World → Prop} {Q : α → List Event → World → Prop}
    (site : Decision) (b : Bool) (f : Bool → Obs α)
    (transport : ∀ h w v, P h w → P h v)
    (tail : PrefixEnsures P Checks (f b) Q) :
    PrefixEnsures P Checks (liftPrefix (branch site b) >>= f) Q := by
  intro w h hi
  let v : World := {w with ambient := {w.ambient with steps := w.ambient.steps.push ({decision := site,outcome := b,netRx := w.ambient.netRxSection})}}
  exact tail v h (transport h w v hi)

theorem block_checks (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (fun h _ => Checks h) Checks
      (Noise.CounterConsume.counterBlock pid n id stamp pkt) := by
  apply PrefixEnsures.preserves
  unfold Noise.CounterConsume.counterBlock
  apply PrefixEnsures.bind (Q := fun _ h _ => Checks h)
    (receipt_checks _ (Event.checkedCounter n id stamp pkt) (access_checks _) (fun _ => True.intro))
  intro b
  apply PrefixPreserves.bind (lift_checks _)
  intro rejected
  split
  · dsimp only
    apply PrefixEnsures.preserves
    apply PrefixEnsures.bind (endpoint_return n id stamp pkt)
    intro ep
    apply branch_const
    · intro h w v hi; exact hi
    intro w h hi
    obtain ⟨checks,rfl,family⟩ := hi
    simp only [Option.isNone_some,Bool.not_false,ite_true]
    exact ((consume_checks pid n id stamp pkt (sourceEndpoint pkt.source) rfl family).bind
      (fun out => PrefixPreserves.pure (I := fun h (_ : World) => Checks h) (fun _ _ hi => hi) _)) w h checks
  · dsimp only
    exact PrefixPreserves.pure (I := fun h (_ : World) => Checks h) (fun _ _ hi => hi) _

theorem receive_checks (g : Gro) (e : Entry) :
    PrefixPreserves (fun h _ => Checks h) Checks (receive g e) := by
  rw [GroSource.receive_factor]
  apply GroSource.receive_preserves (I := fun h (_ : World) => Checks h) (S := Checks)
    _root_.id _ (fun _ _ hi => hi)
  · intro e h w hi; exact checks_snoc hi _ True.intro
  · intro bytes; exact access_checks _
  · intro e w h x v t hi run next; exact checks_snoc next _ True.intro

theorem flushAll_checks (g : Gro) :
    PrefixPreserves (fun h _ => Checks h) Checks (flushAll g) := by
  rw [GroSource.flushAll_factor]
  apply GroSource.flushAll_preserves (I := fun h (_ : World) => Checks h) (S := Checks)
    _root_.id _ (fun _ _ hi => hi)
  · intro e h w hi; exact checks_snoc hi _ True.intro
  · intro bytes; exact access_checks _
  · intro e w h x v t hi run next; exact checks_snoc next _ True.intro

theorem checks_bind (a : Obs α) (f : α → Obs β)
    (ha : PrefixPreserves (fun h _ => Checks h) Checks a)
    (hf : ∀ x, PrefixPreserves (fun h _ => Checks h) Checks (f x)) :
    PrefixPreserves (fun h _ => Checks h) Checks (a >>= f) := ha.bind hf

theorem state_checks (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (fun h _ => Checks h) Checks
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState n id stamp pkt)) :=
  receipt_checks _ (Event.checkedState n id stamp pkt) (lift_checks _) (fun _ => True.intro)

theorem poll_checks (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h _ => Checks h) Checks (RxJoint.poll pid budget) := by
  rw [Noise.CounterConsume.poll_factor]
  unfold Noise.CounterConsume.pollWithBlock
  repeat' first
    | assumption
    | rx_phase_reduce
    | (rx_phase_head plain Pure.pure; exact PrefixPreserves.pure (I := fun h (_ : World) => Checks h) (fun _ _ hi => hi) _)
    | (rx_phase_head plain Noise.CounterConsume.counterBlock; apply checks_bind _ _ (block_checks _ _ _ _ _))
    | (rx_phase_head plain capture; apply checks_bind _ _ (capture_checks _))
    | (rx_phase_head plain drop; apply checks_bind _ _ (drop_checks _ _ _ _))
    | (rx_phase_head plain receive; apply checks_bind _ _ (receive_checks _ _))
    | (rx_phase_head plain flushAll; apply checks_bind _ _ (flushAll_checks _))
    | (rx_phase_head receipt branch; apply checks_bind _ _
        (state_checks _ _ _ _))
    | (rx_phase_head plain access; apply checks_bind _ _ (access_checks _))
    | (rx_phase_head plain liftPrefix; apply checks_bind _ _ (lift_checks _))
    | (rx_phase_head plain ForIn.forIn; apply checks_bind _ _; first
        | apply PrefixPreserves.range
        | apply PrefixPreserves.forIn)
    | (rx_phase_head plain ite; apply PrefixPreserves.ite)
    | (exact fun _ _ hi => hi)
    | rx_phase_intro
    | rx_phase_match


end Leanux.Proofs.WG.Roaming.ConsumedEndpoint
