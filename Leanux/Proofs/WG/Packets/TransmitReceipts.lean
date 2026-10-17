import Leanux.Proofs.WG.Queues.JointPrimitives
import Leanux.Proofs.WG.Packets.TxFront

/-! Transmit-front receipts extend the existing joint journal. Capture executes
one actual observer and appends a receipt only after a completed splice; later
tail failures retain it. Projection preserves every older event and Stop. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Packets AllowedIps

structure Receipt where
  family : Nat
  addr : Nat
  packets : List Packet
  mtu : Nat
  run : WGRunWitness (Except Int PeerId)

inductive Event where
  | old (event : RoutingJoint.Event)
  | transmit (receipt : Receipt)

def oldEvent : Event → Option RoutingJoint.Event
  | .old e => some e
  | .transmit _ => none

def old (g : WGPrefix RoutingJoint.Event α) : WGPrefix Event α :=
  focusStatePrefix Event.old oldEvent g

theorem old_projects (g : WGPrefix RoutingJoint.Event α) (hg : StateAppends g) :
    StateProjectsPrefix oldEvent id (old g) g :=
  fun w => (hg w).project_focus Event.old oldEvent (fun _ => rfl)

theorem old_appends (g : WGPrefix RoutingJoint.Event α) : StateAppends (old g) :=
  StateAppends.focus _ _ _

def observeFront (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId)) :
    WGPrefix Event (Except Int PeerId) := do
  let r ← captureWGObserved (old front)
  match r.value with
  | .error _ => pure r.value
  | .ok _ =>
    emitStatePrefix (.transmit ⟨family,addr,packets,mtu,r⟩)
    pure r.value

theorem observeFront_run (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (w : WGWorld) (ambient : Ambient) (h : List Event) :
    runWGPrefix (observeFront family addr packets mtu front) w ambient h =
      match runWGPrefix (old front) w ambient h with
      | (.error stop,hist) => (.error stop,hist)
      | (.ok ((value,v),after),hist) =>
        (.ok ((value,v),after), match value with
          | .error _ => hist
          | .ok _ => hist ++ [.transmit ⟨family,addr,packets,mtu,⟨value,w,v,ambient,after⟩⟩]) := by
  change runStatePrefix (observeFront family addr packets mtu front) w ambient h = _
  rw [observeFront,runStatePrefix_bind]
  have capture := runWGPrefix_captureWGObserved (old front) w ambient h
  simp only [runWGPrefix] at capture
  rw [capture]
  simp only [runWGPrefix]
  cases run : runStatePrefix (old front) w ambient h with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out =>
      rcases out with ⟨⟨value,v⟩,after⟩
      cases value <;> rfl

theorem observeFront_projects (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId)) (hf : StateAppends front) :
    StateProjectsPrefix oldEvent id (observeFront family addr packets mtu front) front := by
  intro w ambient h
  have projected := old_projects front hf w ambient h
  change runWGPrefix front w ambient (h.filterMap oldEvent) =
    ((runWGPrefix (observeFront family addr packets mtu front) w ambient h).1.map
      (fun ((x,v),a) => ((x,v),a)),
      (runWGPrefix (observeFront family addr packets mtu front) w ambient h).2.filterMap oldEvent)
  change runWGPrefix front w ambient (h.filterMap oldEvent) =
    ((runWGPrefix (old front) w ambient h).1.map (fun ((x,v),a) => ((x,v),a)),
      (runWGPrefix (old front) w ambient h).2.filterMap oldEvent) at projected
  rw [observeFront_run]
  cases run : runWGPrefix (old front) w ambient h with
  | mk result hist =>
    cases result with
    | error stop => simpa only [run] using projected
    | ok out =>
      rcases out with ⟨⟨value,v⟩,after⟩
      cases value <;> simpa only [run,List.filterMap_append,List.filterMap_cons,
        oldEvent,List.filterMap_nil,List.append_nil] using projected

theorem observeFront_appends (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId)) :
    StateAppends (observeFront family addr packets mtu front) := by
  unfold observeFront
  apply StateAppends.bind (old_appends front).captureWGObserved
  intro r
  cases r.value with
  | error err => exact StateAppends.pure _
  | ok pid =>
    apply StateAppends.bind
    · intro w ambient h; exact ⟨[_],rfl⟩
    · intro _; exact StateAppends.pure _

def receiptEvent : Event → Option Receipt
  | .old _ => none
  | .transmit r => some r

def Receipt.Valid (r : Receipt) : Prop :=
  r.run.Valid (txFront r.family r.addr r.packets r.mtu) ∧
    ∃ pid, r.run.value = .ok pid

def ReceiptsValid (h : List Event) : Prop :=
  ∀ r ∈ h.filterMap receiptEvent, r.Valid

theorem old_receipts (g : WGPrefix RoutingJoint.Event α) :
    StateHistoryFrame receiptEvent (old g) :=
  fun w => focusPrefix_other Event.old oldEvent receiptEvent (fun _ => rfl) (g.run w)

/-- The existing incoming receipts stay arbitrary except for their supplied
validity. Each newly emitted receipt records this actual native execution. -/
theorem observeFront_valid (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (source : ErasesStatePrefix front (txFront family addr packets mtu))
    (w : WGWorld) (ambient : Ambient) (h : List Event) (valid : ReceiptsValid h) :
    ReceiptsValid (runWGPrefix (observeFront family addr packets mtu front) w ambient h).2 := by
  have quiet := old_receipts front w ambient h
  have erasure := focusStatePrefix_erases Event.old oldEvent source w ambient h
  change (runWGPrefix (old front) w ambient h).2.filterMap receiptEvent = h.filterMap receiptEvent at quiet
  change (runWGPrefix (old front) w ambient h).1 =
    ((txFront family addr packets mtu).run w).run ambient at erasure
  rw [observeFront_run]
  cases run : runWGPrefix (old front) w ambient h with
  | mk result hist =>
    simp only [run] at quiet erasure
    cases result with
    | error stop =>
      intro r member
      exact valid r (quiet ▸ member)
    | ok out =>
      rcases out with ⟨⟨value,v⟩,after⟩
      cases value with
      | error err =>
        intro r member
        exact valid r (quiet ▸ member)
      | ok pid =>
        intro r member
        simp only [List.filterMap_append,List.filterMap_cons,receiptEvent,
          List.filterMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with previous | fresh
        · exact valid r (quiet ▸ previous)
        · subst r
          exact ⟨erasure.symm,⟨pid,rfl⟩⟩

/-- This is a local consequence of an actual receipt and supplied reached
routing, with no claim that an initialized caller has supplied that routing. -/
theorem Receipt.authorized (r : Receipt) (pid : PeerId) (v4 : Bool)
    (valid : r.Valid) (selected : r.run.value = .ok pid)
    (family : r.family = (if v4 then 4 else 6)) (xs : FlatTable × FlatTable)
    (routing : RoutedView (routingView r.run.before) xs) :
    TxFrontCut (if v4 then 4 else 6) r.addr r.packets r.mtu r.run.before
      r.run.after r.run.ambientBefore r.run.ambientAfter pid ∧
    PeerWinner (rootWidth v4) r.addr (selectedFlat v4 xs) (some pid) ∧
    ∀ pkt ∈ r.packets, destinationField (if v4 then 4 else 6) pkt.bytes = r.addr := by
  apply txFront_authorized v4 r.addr r.packets r.mtu r.run.before r.run.after
    r.run.ambientBefore r.run.ambientAfter pid xs routing
  have source := valid.1
  simpa only [WGRunWitness.Valid,family,selected] using source

/-- A completed splice entails an actual non-null destination lookup, whose
source selects only IPv4 or IPv6. No input-family premise is added. -/
theorem Receipt.family_of_valid (r : Receipt) (valid : r.Valid) :
    ∃ v4 : Bool, r.family = (if v4 then 4 else 6) := by
  obtain ⟨pid,selected⟩ := valid.2
  have run := valid.1
  simp only [WGRunWitness.Valid,selected] at run
  obtain ⟨u,q,v,a,b,c,_,lookup,_,_⟩ := txFront_cut r.family r.addr r.packets r.mtu
    r.run.before r.run.after r.run.ambientBefore r.run.ambientAfter pid run
  by_cases four : r.family = 4
  · exact ⟨true,four⟩
  by_cases six : r.family = 6
  · exact ⟨false,six⟩
  cases device : u.dev with
  | none =>
    simp [lookupDst,getDev,device,invariant,AmbientM.invariant] at lookup
    change Except.error _ = Except.ok _ at lookup
    cases lookup
  | some d => simp [lookupDst,getDev,device,branch,AmbientM.branch,four,six] at lookup

/-- Local authorization needs only the actual receipt and reached routing;
family and destination width follow from the successful front itself. -/
theorem Receipt.winner (r : Receipt) (valid : r.Valid) (xs : FlatTable × FlatTable)
    (routing : RoutedView (routingView r.run.before) xs) :
    ∃ (pid : PeerId) (v4 : Bool), r.run.value = .ok pid ∧
      r.family = (if v4 then 4 else 6) ∧
      TxFrontCut (if v4 then 4 else 6) r.addr r.packets r.mtu r.run.before
        r.run.after r.run.ambientBefore r.run.ambientAfter pid ∧
      PeerWinner (rootWidth v4) r.addr (selectedFlat v4 xs) (some pid) ∧
      ∀ pkt ∈ r.packets, destinationField (if v4 then 4 else 6) pkt.bytes = r.addr := by
  obtain ⟨pid,selected⟩ := valid.2
  obtain ⟨v4,family⟩ := r.family_of_valid valid
  exact ⟨pid,v4,selected,family,r.authorized pid v4 valid selected family xs routing⟩

end Leanux.Proofs.WG.TransmitJoint
