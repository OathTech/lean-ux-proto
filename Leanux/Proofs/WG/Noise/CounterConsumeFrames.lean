import Leanux.Proofs.WG.Noise.ConsumeConfirmationClaims
import Leanux.Proofs.WG.Queues.GroPreservation
import Leanux.Proofs.WG.Queues.RxLinkRunner

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.CounterConsume
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes RxJoint
variable {α β : Type}

def CounterAt (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (b : Bool) (h : List Event) (device : Option Device) : Prop :=
  ∃ cr : RunWitness Bool,
    Event.checkedCounter n id stamp pkt cr ∈ h ∧
    cr.Valid (liftWG (counterValidate pkt.keypair pkt.nonce)) ∧ cr.value = b ∧
    cr.after.wg.dev = device

def supported (h : List Event) : Event → Prop
  | .consumed n id stamp r => CounterAt n id stamp r.packet true h r.run.before.dev
  | _ => True

def Checks (h : List Event) : Prop := ∀ e ∈ h, supported h e

theorem counter_mono {n id : Nat} {stamp : PacketStamp} {pkt : RxPacket} {b : Bool}
    {h t : List Event} {device : Option Device}
    (old : CounterAt n id stamp pkt b h device) (sub : h.Sublist t) :
    CounterAt n id stamp pkt b t device := by
  obtain ⟨cr,member,valid,value,dev⟩ := old
  exact ⟨cr,sub.subset member,valid,value,dev⟩

theorem support_mono {h t : List Event} {e : Event} (old : supported h e) (sub : h.Sublist t) :
    supported t e := by
  cases e <;> first | trivial | exact counter_mono old sub

theorem checks_snoc {h : List Event} {e : Event} (old : Checks h) (next : supported h e) :
    Checks (h ++ [e]) := by
  intro x member
  have sub : h.Sublist (h ++ [e]) := List.sublist_append_left _ _
  rcases List.mem_append.mp member with member | member
  · exact support_mono (old x member) sub
  · have eq : x=e := by simpa using member
    subst x
    exact support_mono next sub

theorem checks_append_quiet {h : List Event} (old : Checks h) (t : List Event)
    (quiet : ∀ e ∈ t, ∀ prior, supported prior e) : Checks (h ++ t) := by
  induction t generalizing h with
  | nil => simpa using old
  | cons e es ih =>
    have first := checks_snoc old (quiet e (by simp) h)
    simpa only [List.append_assoc,List.singleton_append] using
      ih first (fun x hx prior => quiet x (List.mem_cons_of_mem _ hx) prior)

theorem access_checks (a : PrefixM LifetimeEvent α) :
    PrefixPreserves (fun h _ => Checks h) Checks (access a) := by
  intro w h hi
  let suffix := ((runPrefix a w (h.filterMap accessEvent)).2.drop
    (h.filterMap accessEvent).length).map Event.access
  have safe : Checks (h ++ suffix) := checks_append_quiet hi suffix (by
    intro e member prior
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp member
    trivial)
  refine ⟨suffix,rfl,safe,?_⟩
  cases (runPrefix (access a) w h).1 <;> trivial

theorem lift_checks (a : Leanux.M α) :
    PrefixPreserves (fun h _ => Checks h) Checks (liftPrefix a) := by
  intro w h hi
  refine ⟨[],by simp,hi,?_⟩
  simp only [runPrefix_lift]
  cases a.run w <;> trivial

theorem emit_checks (e : Event) (quiet : ∀ h, supported h e) :
    PrefixPreserves (fun h _ => Checks h) Checks (emitPrefix (State := World) e) := by
  intro w h hi
  exact ⟨[e],rfl,checks_snoc hi (quiet h),checks_snoc hi (quiet h)⟩

theorem receipt_checks (a : Obs α) (event : RunWitness α → Event)
    (checked : PrefixPreserves (fun h _ => Checks h) Checks a)
    (quiet : ∀ r h, supported h (event r)) :
    PrefixPreserves (fun h _ => Checks h) Checks (receiptObserved a event) := by
  unfold receiptObserved
  exact checked.captureObserved.bind (fun r =>
    (emit_checks (event r) (quiet r)).bind (fun _ =>
      PrefixPreserves.pure (I := fun h (_ : World) => Checks h) (fun _ _ h => h) r.value))

theorem counter_observed (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixEnsures (fun h _ => Checks h) Checks
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (Event.checkedCounter n id stamp pkt))
      (fun b h w => Checks h ∧ CounterAt n id stamp pkt b h w.wg.dev) := by
  intro w h hi
  obtain ⟨suffix,append,safety,normal⟩ := access_checks
    (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)) w h hi
  have erased := access_erases (liftWGObserver_erases
    (counterValidatePrefix_erases pkt.keypair pkt.nonce)) w h
  rw [runPrefix_receiptObserved]
  cases run : runPrefix (access (liftWGObserver
      (counterValidatePrefix pkt.keypair pkt.nonce))) w h with
  | mk result t =>
    simp only [run] at append safety normal erased
    cases result with
    | error stop => exact ⟨suffix,append,safety,True.intro⟩
    | ok out =>
      obtain ⟨b,v⟩ := out
      have next := checks_snoc safety (e := Event.checkedCounter n id stamp pkt ⟨b,w,v⟩) True.intro
      exact ⟨suffix ++ [Event.checkedCounter n id stamp pkt ⟨b,w,v⟩],
        by simp only [append,List.append_assoc],next,next,
        ⟨⟨b,w,v⟩,by simp,erased.symm,rfl,rfl⟩⟩

theorem consume_checked (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixEnsures
      (fun h w => Checks h ∧ CounterAt n id stamp pkt true h w.wg.dev)
      Checks (consume pid n id stamp pkt ep) (fun _ h _ => Checks h) := by
  intro w h hi
  obtain ⟨suffix,append,safety,normal⟩ := access_checks
    (liftWGObserver (consumeDataDonePrefix pid pkt ep)) w h hi.1
  rw [consume_run]
  cases run : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t =>
    simp only [run] at append safety normal
    cases result with
    | error stop => exact ⟨suffix,append,safety,True.intro⟩
    | ok out =>
      obtain ⟨returned,v⟩ := out
      let r : RxDisposition.ConsumeReceipt := ⟨pid,pkt,ep,⟨returned,w.wg,v.wg,w.ambient,v.ambient⟩⟩
      have prior : CounterAt n id stamp pkt true t w.wg.dev :=
        counter_mono hi.2 (append ▸ List.sublist_append_left h suffix)
      have next := checks_snoc safety (e := .consumed n id stamp r) prior
      cases returned with
      | none => exact ⟨suffix ++ [_],by simp only [append,List.append_assoc]; rfl,next,next⟩
      | some bytes =>
        let e : Entry := ⟨⟨n,id,bytes⟩,stamp,some r⟩
        have last := checks_snoc next (e := .buffered e) True.intro
        exact ⟨suffix ++ [_,_],by simp only [append,List.append_assoc]; rfl,last,last⟩


def Anchored (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (b : Bool) :
    List Event → World → Prop :=
  fun h w => Checks h ∧ CounterAt n id stamp pkt b h w.wg.dev

theorem anchored_quiet (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (b : Bool)
    (a : Obs α) (original : Leanux.M α)
    (checks : PrefixPreserves (fun h _ => Checks h) Checks a)
    (erases : ErasesPrefix a original)
    (frame : SameView (fun w : World => w.wg.dev) original) :
    PrefixPreserves (Anchored n id stamp pkt b) Checks a := by
  intro w h hi
  obtain ⟨suffix,append,safety,normal⟩ := checks w h hi.1
  refine ⟨suffix,append,safety,?_⟩
  cases run : (runPrefix a w h).1 with
  | error stop => trivial
  | ok out =>
    have eq : out.2.wg.dev = w.wg.dev :=
      (ProjectedAction.iff_run _ _ _).mp frame w out.1 out.2 ((erases w h).symm.trans run)
    have old := counter_mono hi.2 (append ▸ List.sublist_append_left h suffix)
    exact ⟨by simpa only [run] using normal,eq ▸ old⟩

theorem branch_const {P : List Event → World → Prop}
    {Q : α → List Event → World → Prop}
    (site : Decision) (b : Bool) (f : Bool → Obs α)
    (transport : ∀ h w v, w.wg.dev = v.wg.dev → P h w → P h v)
    (tail : PrefixEnsures P Checks (f b) Q) :
    PrefixEnsures P Checks (liftPrefix (branch site b) >>= f) Q := by
  intro w h hi
  let v : World := {w with ambient := {w.ambient with steps := w.ambient.steps.push ({decision := site,outcome := b,netRx := w.ambient.netRxSection})}}
  exact tail v h (transport h w v rfl hi)

theorem endpoint_anchored (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (b : Bool) :
    PrefixPreserves (Anchored n id stamp pkt b) Checks
      (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
        (Event.checkedEndpoint n id stamp pkt)) := by
  apply anchored_quiet n id stamp pkt b _ (liftWG (endpointFromSkb pkt.source))
  · exact receipt_checks _ _ (lift_checks _) (fun _ _ => True.intro)
  · exact RxLink.receipt_erases (erasesPrefix_lift _)
  · apply sameView_liftWG (fun w : World => w.wg.dev) (fun g : WGWorld => g.dev)
    · exact (endpointFromSkb_sameWGStore pkt.source).factor WGStoreView.dev
    · intro w g ambient same
      exact same

theorem counter_product_stamp (pkt : RxPacket) (cr : RunWitness Bool)
    (valid : cr.Valid (liftWG (counterValidate pkt.keypair pkt.nonce))) :
    ∃ stamp,
      ConsumeConfirmation.keyStampAt cr.before.wg pkt.keypair = some stamp ∧
      ConsumeConfirmation.keyStampAt cr.after.wg pkt.keypair = some stamp := by
  change (liftWG (counterValidate pkt.keypair pkt.nonce)).run cr.before =
    .ok (cr.value,cr.after) at valid
  rw [liftWG_run] at valid
  cases native : ((counterValidate pkt.keypair pkt.nonce).run cr.before.wg).run cr.before.ambient with
  | error stop => simp [native,Except.map] at valid
  | ok result =>
    obtain ⟨⟨b,g⟩,ambient⟩ := result
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    have same : g = cr.after.wg := congrArg World.wg valid.2
    obtain ⟨stamp,before,after⟩ := (hoare_iff_run_ambient _ _ _).mp
      (ConsumeConfirmation.counter_stamped pkt.keypair pkt.nonce
        (ConsumeConfirmation.keyStampAt cr.before.wg pkt.keypair))
      cr.before.wg cr.before.ambient b g ambient rfl native
    exact ⟨stamp,before,same ▸ after⟩


end Leanux.Proofs.WG.Noise.CounterConsume
