import Leanux.Proofs.WG.Packets.TransmitChecks
import Leanux.Proofs.WG.Configuration.RoutingConfiguration

/-! Existing joint product observers run on their actual projected incoming
journal. Their routing completions may change the route fold; old transmit
certificates retain the strict prefixes recorded when they were emitted. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Packets AllowedIps Configuration

/-- Canonical product focus; the old callback remains an arbitrary observer. -/
def oldProduct (g : PrefixM RoutingJoint.Event α) : PrefixM Event α :=
  focusPrefix Event.old oldEvent g

theorem oldProduct_appends (g : PrefixM RoutingJoint.Event α) : Appends (oldProduct g) :=
  Appends.focus _ _ _

theorem oldProduct_projects (g : PrefixM RoutingJoint.Event α) (hg : Appends g) :
    ProjectsPrefix oldEvent id (oldProduct g) g :=
  hg.project_focus Event.old oldEvent (fun _ => rfl)

theorem oldProduct_erases {g : PrefixM RoutingJoint.Event α} {a : Leanux.M α}
    (hg : ErasesPrefix g a) : ErasesPrefix (oldProduct g) a :=
  focusPrefix_erases Event.old oldEvent hg

theorem oldProduct_receipts (g : PrefixM RoutingJoint.Event α) :
    HistoryFrame receiptEvent (oldProduct g) :=
  focusPrefix_other Event.old oldEvent receiptEvent (fun _ => rfl) g

/-- A product callback cannot manufacture transmit entries through this
embedding, even if its own history behavior is otherwise unrestricted. -/
theorem Checks.oldProduct (g : PrefixM RoutingJoint.Event α) (w : World)
    (checked : Checks initial h) : Checks initial (runPrefix (oldProduct g) w h).2 := by
  let suffix := ((runPrefix g w (h.filterMap oldEvent)).2.drop
    (h.filterMap oldEvent).length).map Event.old
  change Checks initial (h ++ suffix)
  apply checked.append
  intro pre event post position
  have member : event ∈ suffix := by rw [position]; simp
  obtain ⟨lower,_,same⟩ := List.mem_map.mp member
  subst event
  trivial

/-- Result-dependent old contracts compose on the same execution and projected
history. Neither the routing history nor the callback is assumed constant. -/
theorem oldProduct_ensures (initial : FlatTable × FlatTable)
    {P : List RoutingJoint.Event → World → Prop} {S : List RoutingJoint.Event → Prop}
    {Q : α → List RoutingJoint.Event → World → Prop}
    (g : PrefixM RoutingJoint.Event α) (hg : PrefixEnsures P S g Q) :
    PrefixEnsures (fun h w => P (h.filterMap oldEvent) w ∧ Checks initial h)
      (fun h => S (h.filterMap oldEvent) ∧ Checks initial h) (oldProduct g)
      (fun x h w => Q x (h.filterMap oldEvent) w ∧ Checks initial h) := by
  have focused : PrefixEnsures (fun h w => P (h.filterMap oldEvent) w)
      (fun h => S (h.filterMap oldEvent)) (oldProduct g)
      (fun x h w => Q x (h.filterMap oldEvent) w) :=
    PrefixEnsures.focus Event.old oldEvent (fun _ => rfl) hg
  intro w h hi
  obtain ⟨suffix,hs,safe,normal⟩ := focused w h hi.1
  have checked := hi.2.oldProduct g w
  refine ⟨suffix,hs,⟨safe,checked⟩,?_⟩
  cases result : (runPrefix (oldProduct g) w h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [result] using normal,checked⟩

/-- Transport the original routing-state contract, allowing new completion
events and preserving all previous transmit positions. -/
theorem oldProduct_preserves (initial : FlatTable × FlatTable)
    (g : PrefixM RoutingJoint.Event α)
    (hg : PrefixPreserves
      (fun h w => GlobalCompletionState initial (h.filterMap RoutingJoint.routingEvent) w.wg)
      (fun h => CompletionSafe initial (h.filterMap RoutingJoint.routingEvent)) g) :
    PrefixPreserves (Inv initial) (Safe initial) (oldProduct g) :=
  (oldProduct_ensures initial
    (P := fun h w => GlobalCompletionState initial (h.filterMap RoutingJoint.routingEvent) w.wg)
    (S := fun h => CompletionSafe initial (h.filterMap RoutingJoint.routingEvent))
    (Q := fun _ h w => GlobalCompletionState initial (h.filterMap RoutingJoint.routingEvent) w.wg)
    g hg).preserves

/-- A caller which also tracks the original consume positions retains both
sets of exact-prefix checks; its original invariant premise is explicit. -/
theorem oldProduct_routingPosition (initial : FlatTable × FlatTable)
    (g : PrefixM RoutingJoint.Event α)
    (hg : PrefixPreserves (RoutingPosition.Inv initial) (RoutingPosition.Safe initial) g) :
    PrefixPreserves
      (fun h w => RoutingPosition.Inv initial (h.filterMap oldEvent) w ∧ Checks initial h)
      (fun h => RoutingPosition.Safe initial (h.filterMap oldEvent) ∧ Checks initial h)
      (oldProduct g) :=
  (oldProduct_ensures initial (Q := fun _ => RoutingPosition.Inv initial) g hg).preserves

/-- Existing routing projections supply the actual lower contract. This rule
allows configuration observers to append real routing updates. -/
theorem oldProduct_projected (initial : FlatTable × FlatTable)
    (g : PrefixM RoutingJoint.Event α) (a : PrefixM RoutingCompletion α)
    (appends : Appends g) (projection : ProjectsPrefix RoutingJoint.routingEvent id g a)
    (routing : PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg)
      (CompletionSafe initial) a) :
    PrefixPreserves (Inv initial) (Safe initial) (oldProduct g) := by
  apply oldProduct_preserves initial g
  intro w h hi
  obtain ⟨_,_,safe,normal⟩ := routing w (h.filterMap RoutingJoint.routingEvent) hi
  rw [projection w h] at safe normal
  obtain ⟨suffix,hs⟩ := appends w h
  refine ⟨suffix,hs,safe,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out => simpa only [result,Except.map,id_eq] using normal

/-- Arbitrary actual product actions use their original routing-retention
contract; no restriction to native actions or to successful returns is added. -/
theorem oldProduct_lift (initial : FlatTable × FlatTable) (a : Leanux.M α)
    (frame : ProductRetainsRoutingCall a) :
    PrefixPreserves (Inv initial) (Safe initial) (oldProduct (liftPrefix a)) := by
  apply oldProduct_preserves initial _
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi run
  exact ⟨hi.1,hi.2.retains ((ProjectedAction.iff_run _ _ _).mp frame w x v run)⟩

/-- Peer configuration uses the original address-shape premise. -/
theorem oldProduct_setPeer (initial : FlatTable × FlatTable) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) :
    PrefixPreserves (Inv initial) (Safe initial)
      (oldProduct (liftWGObserver (RoutingJoint.setPeerCommand attrs))) :=
  oldProduct_projected initial _ _ (RoutingPosition.Controls.setPeer_appends attrs).liftWGObserver
    ((RoutingJoint.setPeerCommand_routing attrs).liftWGObserver _ _)
    (setPeerCmdObserved_global initial attrs shape).liftWGObserver

theorem oldProduct_setDevice (initial : FlatTable × FlatTable) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) :
    PrefixPreserves (Inv initial) (Safe initial)
      (oldProduct (liftWGObserver (RoutingJoint.setDevice attrs))) :=
  oldProduct_projected initial _ _ (RoutingPosition.Controls.setDevice_appends attrs).liftWGObserver
    ((RoutingJoint.setDevice_routing attrs).liftWGObserver _ _)
    (wgSetDeviceObserved_global initial attrs shape).liftWGObserver

theorem oldProduct_dispatchSet (initial : FlatTable × FlatTable) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) :
    PrefixPreserves (Inv initial) (Safe initial) (oldProduct (RoutingJoint.dispatchSet attrs)) :=
  oldProduct_projected initial _ _ (RoutingPosition.Controls.dispatchSet_appends attrs)
    (RoutingJoint.dispatchSet_routing attrs) (dispatchObserved_global initial (.wgSet attrs) shape)

theorem oldProduct_dispatchCreate (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) (oldProduct RoutingJoint.dispatchCreate) :=
  oldProduct_projected initial _ _ RoutingPosition.Controls.dispatchCreate_appends
    RoutingJoint.dispatchCreate_routing (dispatchObserved_global initial .wgCreate True.intro)

theorem oldProduct_dispatchDelete (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) (oldProduct RoutingJoint.dispatchDelete) :=
  oldProduct_projected initial _ _ RoutingPosition.Controls.dispatchDelete_appends
    RoutingJoint.dispatchDelete_routing (dispatchObserved_global initial .wgDelete True.intro)

end Leanux.Proofs.WG.TransmitJoint
