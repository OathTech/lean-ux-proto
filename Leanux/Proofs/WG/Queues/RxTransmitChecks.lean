import Leanux.Proofs.WG.Queues.RxTransmit
import Leanux.Proofs.WG.Queues.ObservePollContext
import Leanux.Proofs.WG.Packets.TransmitStack
import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames

/-! A local poll is checked at its actual caller prefix. Local promotion emits
no routing completion, so every captured transmit entry uses that fixed
outer routing fold. The strict global positions are recovered under promotion. -/
namespace Leanux.Proofs.WG.Queues.RxTransmit.Position
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Packets AllowedIps RxHistory.ObserveSource

def Checks (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (h : List LocalEvent) : Prop :=
  ∀ r ∈ h.filterMap receiptEvent,
    r.Valid ∧ GlobalCompletionState initial (TransmitJoint.routes prior) r.run.before

def Inv (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (h : List LocalEvent) (w : World) : Prop :=
  GlobalCompletionState initial (TransmitJoint.routes prior) w.wg ∧ Checks initial prior h

def Safe (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (h : List LocalEvent) : Prop :=
  CompletionSafe initial (TransmitJoint.routes prior) ∧ Checks initial prior h

theorem Inv.safe (hi : Inv initial prior h w) : Safe initial prior h := ⟨hi.1.1,hi.2⟩

theorem checks_seed (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event) :
    Checks initial prior (seed prior) := by
  intro r member
  simp only [seed,filterMap_disjoint LocalEvent.old receiptEvent (fun _ => rfl),List.not_mem_nil] at member

theorem seed_inv (hi : TransmitJoint.Inv initial prior w) : Inv initial prior (seed prior) w :=
  ⟨hi.1,checks_seed initial prior⟩

theorem checks_oldAccess (g : MixedM α) (w : WGWorld) (ambient : Ambient)
    (checked : Checks initial prior h) :
    Checks initial prior (runWGPrefix (oldAccess g) w ambient h).2 := by
  intro r member
  have quiet := oldAccess_receipts g w ambient h
  change (runWGPrefix (oldAccess g) w ambient h).2.filterMap receiptEvent = h.filterMap receiptEvent at quiet
  rw [quiet] at member
  exact checked r member

/-- The fresh receipt is justified by this front's entry and exact successful
native run. Earlier local receipts retain their original captured worlds. -/
theorem front_checks (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : WGWorld) (ambient : Ambient) (h : List LocalEvent)
    (routing : GlobalCompletionState initial (TransmitJoint.routes prior) w)
    (checked : Checks initial prior h) :
    Checks initial prior (runWGPrefix (TransmitJoint.Source.frontWith
      (fun r => LocalEvent.transmit ⟨family,addr,packets,mtu,r⟩)
      (oldAccess (txFrontPrefix family addr packets mtu))) w ambient h).2 := by
  have oldChecked := checks_oldAccess (txFrontPrefix family addr packets mtu) w ambient checked
  have erased := focusStatePrefix_erases LocalEvent.old oldRx
    (focusStatePrefix_erases RxJoint.Event.access RxJoint.accessEvent
      (txFrontPrefix_erases family addr packets mtu)) w ambient h
  change (runWGPrefix (oldAccess (txFrontPrefix family addr packets mtu)) w ambient h).1 =
    ((txFront family addr packets mtu).run w).run ambient at erased
  rw [TransmitJoint.Source.frontWith_run]
  cases run : runWGPrefix (oldAccess (txFrontPrefix family addr packets mtu)) w ambient h with
  | mk result hist =>
    simp only [run] at oldChecked erased
    cases result with
    | error stop => exact oldChecked
    | ok out =>
      rcases out with ⟨⟨value,v⟩,after⟩
      cases value with
      | error err => exact oldChecked
      | ok pid =>
        intro r member
        simp only [List.filterMap_append,List.filterMap_cons,receiptEvent,
          List.filterMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with previous | fresh
        · exact oldChecked r previous
        · subst r
          exact ⟨⟨erased.symm,⟨pid,rfl⟩⟩,routing⟩

theorem nativeTransmit_checks (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : WGWorld) (ambient : Ambient) (h : List LocalEvent)
    (routing : GlobalCompletionState initial (TransmitJoint.routes prior) w)
    (checked : Checks initial prior h) :
    Checks initial prior (runWGPrefix (nativeTransmit family addr packets mtu) w ambient h).2 := by
  intro r member
  rw [nativeTransmit_receipts] at member
  exact front_checks family addr packets mtu w ambient h routing checked r member

/-- Routing is transported only at a normal endpoint. A Stop keeps the
checked actual prefix, with no invented final state or positive-refcount premise. -/
theorem nativeTransmit_preserves (initial : FlatTable × FlatTable)
    (prior : List TransmitJoint.Event) (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StatePrefixPreserves
      (fun h w _ => GlobalCompletionState initial (TransmitJoint.routes prior) w ∧ Checks initial prior h)
      (Safe initial prior) (nativeTransmit family addr packets mtu) := by
  intro w ambient h hi
  obtain ⟨suffix,append⟩ := nativeTransmit_appends family addr packets mtu w ambient h
  have checked := nativeTransmit_checks family addr packets mtu w ambient h hi.1 hi.2
  refine ⟨suffix,append,⟨hi.1.1,checked⟩,?_⟩
  cases run : (runPrefix ((nativeTransmit family addr packets mtu).run w) ambient h).1 with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨value,v⟩,after⟩
    have source : ((wgXmit family addr packets mtu).run w).run ambient = .ok ((value,v),after) :=
      (nativeTransmit_erases family addr packets mtu w ambient h).symm.trans run
    have retained := (ProjectedAction.iff_run_ambient _ _ _).mp
      (wgXmit_routing family addr packets mtu) w ambient value v after source
    exact ⟨⟨hi.1.1,hi.1.2.retains retained⟩,checked⟩

theorem transmit_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    PrefixPreserves (Inv initial prior) (Safe initial prior) (transmit family addr packets mtu) :=
  (nativeTransmit_preserves initial prior family addr packets mtu).liftWGObserver

theorem routes_promoted (prior : List TransmitJoint.Event) (suffix : List LocalEvent) :
    TransmitJoint.routes (prior ++ suffix.map promote) = TransmitJoint.routes prior := by
  unfold TransmitJoint.routes
  rw [List.filterMap_append,List.filterMap_append]
  have quiet : ((suffix.map promote).filterMap TransmitJoint.oldEvent).filterMap RoutingJoint.routingEvent = [] := by
    rw [List.filterMap_filterMap]
    exact filterMap_disjoint promote _ promote_noRouting suffix
  rw [quiet,List.append_nil]

/-- Promotion preserves old strict positions and checks every newly promoted
handoff at the corresponding actual prefix, whose routing fold is unchanged. -/
theorem checks_promoted (oldChecked : TransmitJoint.Checks initial prior)
    (checked : Checks initial prior suffix) :
    TransmitJoint.Checks initial (prior ++ suffix.map promote) := by
  apply oldChecked.append
  intro pre event post position
  have member : event ∈ suffix.map promote := by rw [position]; simp
  obtain ⟨localEvent,localMember,rfl⟩ := List.mem_map.mp member
  cases localEvent with
  | old event => trivial
  | transmit receipt =>
    simp only [promote] at position
    have fact := checked receipt (List.mem_filterMap.mpr ⟨.transmit receipt,localMember,rfl⟩)
    have noRouting : TransmitJoint.routes (pre ++ .transmit receipt :: post) = [] := by
      rw [← position]
      exact routes_promoted [] suffix
    have prefixEmpty : TransmitJoint.routes pre = [] := by
      simp only [TransmitJoint.routes,List.filterMap_append,List.filterMap_cons,
        TransmitJoint.oldEvent] at noRouting
      exact (List.append_eq_nil_iff.mp noRouting).1
    change receipt.Valid ∧ GlobalCompletionState initial (TransmitJoint.routes (prior ++ pre)) receipt.run.before
    refine ⟨fact.1,?_⟩
    have routingPrefix : TransmitJoint.routes (prior ++ pre) = TransmitJoint.routes prior := by
      unfold TransmitJoint.routes at prefixEmpty ⊢
      simp only [List.filterMap_append,prefixEmpty,List.append_nil]
    rw [routingPrefix]
    exact fact.2

theorem atPrefix_routes (prior : List TransmitJoint.Event) (h : List LocalEvent) :
    TransmitJoint.routes (atPrefix seed promote prior h) = TransmitJoint.routes prior :=
  routes_promoted prior _

theorem atPrefix_checks (oldChecked : TransmitJoint.Checks initial prior)
    (checked : Checks initial prior h) :
    TransmitJoint.Checks initial (atPrefix seed promote prior h) := by
  apply checks_promoted oldChecked
  intro r member
  obtain ⟨event,he,hr⟩ := List.mem_filterMap.mp member
  exact checked r (List.mem_filterMap.mpr ⟨event,List.mem_of_mem_drop he,hr⟩)

theorem atPrefix_inv (oldChecked : TransmitJoint.Checks initial prior)
    (hi : Inv initial prior h w) : TransmitJoint.Inv initial (atPrefix seed promote prior h) w :=
  ⟨by simpa only [atPrefix_routes] using hi.1,atPrefix_checks oldChecked hi.2⟩

/-- The local seed contains only old lifetime events. The caller's entire
actual prefix, including its earlier transmit checks, remains outside it. -/
theorem seeded_preserves (initial : FlatTable × FlatTable) (poll : PrefixM LocalEvent α)
    (callback : ∀ prior, PrefixPreserves (Inv initial prior) (Safe initial prior) poll) :
    PrefixPreserves (TransmitJoint.Inv initial) (TransmitJoint.Safe initial)
      (seededWith seed promote poll) := by
  intro w prior hi
  obtain ⟨suffix,append,safe,normal⟩ := callback prior w (seed prior) (seed_inv hi)
  have output := seeded_suffix seed promote poll w prior _ suffix (Prod.ext rfl append)
  rw [output]
  have globalChecked := atPrefix_checks hi.2 safe.2
  rw [append,atPrefix_suffix] at globalChecked
  refine ⟨suffix.map promote,rfl,⟨?_,globalChecked⟩,?_⟩
  · simpa only [routes_promoted] using safe.1
  · cases run : (runPrefix poll w (seed prior)).1 with
    | error stop => trivial
    | ok out =>
      have endInv : Inv initial prior (runPrefix poll w (seed prior)).2 out.2 := by
        simpa only [run] using normal
      have lifted := atPrefix_inv hi.2 endInv
      simpa only [append,atPrefix_suffix] using lifted

end Leanux.Proofs.WG.Queues.RxTransmit.Position
