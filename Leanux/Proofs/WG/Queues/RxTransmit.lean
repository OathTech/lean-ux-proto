import Leanux.Proofs.WG.Packets.TransmitSource
import Leanux.Proofs.WG.Queues.ObservePollSource

/-! One local poll journal retains every original RX event and adds only
completed transmit-front receipts. Promotion is exhaustive and never creates
a routing configuration completion. -/
namespace Leanux.Proofs.WG.Queues.RxTransmit
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Packets

inductive LocalEvent where
  | old (event : RxJoint.Event)
  | transmit (receipt : TransmitJoint.Receipt)

def oldRx : LocalEvent → Option RxJoint.Event
  | .old e => some e
  | .transmit _ => none

def receiptEvent : LocalEvent → Option TransmitJoint.Receipt
  | .old _ => none
  | .transmit r => some r

def promote : LocalEvent → TransmitJoint.Event
  | .old e => .old (.rx (RxHistory.promote e))
  | .transmit r => .transmit r

def globalRx (e : TransmitJoint.Event) : Option RxHistory.Event :=
  (TransmitJoint.oldEvent e).bind RoutingJoint.rxEvent

def seed (h : List TransmitJoint.Event) : List LocalEvent :=
  (RxJoint.seed (RxHistory.prior (h.filterMap globalRx))).map LocalEvent.old

theorem oldRx_old (e : RxJoint.Event) : oldRx (.old e) = some e := rfl

theorem seed_oldRx (h : List TransmitJoint.Event) :
    (seed h).filterMap oldRx = RxJoint.seed (RxHistory.prior (h.filterMap globalRx)) :=
  filterMap_encoded LocalEvent.old oldRx oldRx_old _

theorem promote_rx (e : LocalEvent) : globalRx (promote e) = (oldRx e).map RxHistory.promote := by
  cases e <;> rfl

theorem promote_receipt (e : LocalEvent) : TransmitJoint.receiptEvent (promote e) = receiptEvent e := by
  cases e <;> rfl

theorem promote_noRouting (e : LocalEvent) :
    (TransmitJoint.oldEvent (promote e)).bind RoutingJoint.routingEvent = none := by
  cases e <;> rfl

/-- The original lifetime focus on native WG/Ambient, with every other local
RX record left in its incoming position. -/
def rxAccess (g : MixedM α) : WGPrefix RxJoint.Event α :=
  focusStatePrefix RxJoint.Event.access RxJoint.accessEvent g

def oldAccess (g : MixedM α) : WGPrefix LocalEvent α :=
  focusStatePrefix LocalEvent.old oldRx (rxAccess g)

theorem rxAccess_product (g : MixedM α) :
    liftWGObserver (rxAccess g) = RxJoint.access (liftWGObserver g) := rfl

theorem oldAccess_projects (g : MixedM α) :
    StateProjectsPrefix oldRx id (oldAccess g) (rxAccess g) :=
  fun w => (StateAppends.focus RxJoint.Event.access RxJoint.accessEvent g w).project_focus
    LocalEvent.old oldRx oldRx_old

private theorem rxAccess_bind {α β : Type} (g : MixedM α) (f : α → MixedM β)
    (hg : StateAppends g) (hf : ∀ x, StateAppends (f x)) :
    (rxAccess g >>= fun x => rxAccess (f x)) = rxAccess (g >>= f) := by
  funext w ambient
  apply ExceptT.ext
  funext h
  exact focusPrefix_bind_appends RxJoint.Event.access RxJoint.accessEvent (fun _ => rfl)
    (hg w) (fun out => hf out.1 out.2) ambient h

private theorem rxAccess_pure {α : Type} (x : α) : rxAccess (pure x) = (pure x : WGPrefix RxJoint.Event α) := by
  funext w ambient
  apply ExceptT.ext
  funext h
  change (.ok ((x,w),ambient),h ++ ((h.filterMap RxJoint.accessEvent).drop
    (h.filterMap RxJoint.accessEvent).length).map RxJoint.Event.access) =
    (Except.ok (ε := Stop) ((x,w),ambient),h)
  simp only [List.drop_length,List.map_nil,List.append_nil]

private theorem rxAccess_front_factor (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    (do match ← rxAccess (txFrontPrefix family addr packets mtu) with
        | .error err => pure err
        | .ok pid => rxAccess (txTailPrefix pid)) =
      rxAccess (wgXmitPrefix family addr packets mtu) := by
  rw [wgXmitPrefix_front_factor]
  have tail (result : Except Int PeerId) :
      (match result with | .error err => pure err | .ok pid => rxAccess (txTailPrefix pid)) =
      rxAccess (match result with | .error err => pure err | .ok pid => txTailPrefix pid) := by
    cases result with
    | error err => exact (rxAccess_pure err).symm
    | ok pid => rfl
  rw [show (fun result : Except Int PeerId => match result with
      | .error err => pure err | .ok pid => rxAccess (txTailPrefix pid)) =
      (fun result => rxAccess (match result with
        | .error err => pure err | .ok pid => txTailPrefix pid)) from funext tail]
  apply rxAccess_bind _ _ (txFrontPrefix_appends family addr packets mtu)
  intro result
  cases result with
  | error err => exact StateAppends.pure err
  | ok pid => exact txTailPrefix_appends pid

/-- Exactly one captured original front, followed by its original tail. -/
def nativeTransmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : WGPrefix LocalEvent Int :=
  TransmitJoint.Source.transmitWith
    (fun r => .transmit ⟨family,addr,packets,mtu,r⟩)
    (oldAccess (txFrontPrefix family addr packets mtu)) (fun pid => oldAccess (txTailPrefix pid))

theorem nativeTransmit_projects (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateProjectsPrefix oldRx id (nativeTransmit family addr packets mtu)
      (rxAccess (wgXmitPrefix family addr packets mtu)) := by
  rw [← rxAccess_front_factor]
  exact TransmitJoint.Source.transmitWith_projects oldRx _ _ _ _ _ (fun _ => rfl)
    (oldAccess_projects _) (fun _ => oldAccess_projects _)

theorem nativeTransmit_appends (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateAppends (nativeTransmit family addr packets mtu) :=
  TransmitJoint.Source.transmitWith_appends _ _ _
    (StateAppends.focus _ _ _) (fun _ => StateAppends.focus _ _ _)

theorem nativeTransmit_erases (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesStatePrefix (nativeTransmit family addr packets mtu) (wgXmit family addr packets mtu) := by
  intro w ambient h
  have projected := congrArg Prod.fst (nativeTransmit_projects family addr packets mtu w ambient h)
  have erased := focusStatePrefix_erases RxJoint.Event.access RxJoint.accessEvent
    (wgXmitPrefix_erases family addr packets mtu) w ambient (h.filterMap oldRx)
  change (runWGPrefix (rxAccess (wgXmitPrefix family addr packets mtu)) w ambient (h.filterMap oldRx)).1 =
    (runWGPrefix (nativeTransmit family addr packets mtu) w ambient h).1.map
      (fun ((x,v),a) => ((x,v),a)) at projected
  have same := projected.symm.trans erased
  change (runWGPrefix (nativeTransmit family addr packets mtu) w ambient h).1 = _
  cases run : (runWGPrefix (nativeTransmit family addr packets mtu) w ambient h).1 <;>
    simpa only [run,Except.map] using same

def transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : PrefixM LocalEvent Int :=
  liftWGObserver (nativeTransmit family addr packets mtu)

theorem transmit_projects (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ProjectsPrefix oldRx id (transmit family addr packets mtu)
      (RxJoint.access (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  (nativeTransmit_projects family addr packets mtu).liftWGObserver oldRx id

theorem transmit_appends (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Appends (transmit family addr packets mtu) := (nativeTransmit_appends family addr packets mtu).liftWGObserver

theorem transmit_erases (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesPrefix (transmit family addr packets mtu) (liftWG (wgXmit family addr packets mtu)) :=
  liftWGObserver_erases (nativeTransmit_erases family addr packets mtu)

/-- Only the receipt variant is extracted; all original RX events remain
untouched by this separate projection. -/
def ReceiptsValid (h : List LocalEvent) : Prop :=
  ∀ r ∈ h.filterMap receiptEvent, r.Valid

theorem oldAccess_receipts (g : MixedM α) : StateHistoryFrame receiptEvent (oldAccess g) :=
  fun w => focusPrefix_other LocalEvent.old oldRx receiptEvent (fun _ => rfl) ((rxAccess g).run w)

/-- A successful local capture records the actual native front and its four
state endpoints. Normal errno and Stop add no handoff receipt. -/
theorem front_valid (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : WGWorld) (ambient : Ambient) (h : List LocalEvent) (valid : ReceiptsValid h) :
    ReceiptsValid (runWGPrefix (TransmitJoint.Source.frontWith
      (fun r => LocalEvent.transmit ⟨family,addr,packets,mtu,r⟩)
      (oldAccess (txFrontPrefix family addr packets mtu))) w ambient h).2 := by
  let front := oldAccess (txFrontPrefix family addr packets mtu)
  have quiet := oldAccess_receipts (txFrontPrefix family addr packets mtu) w ambient h
  have erased := focusStatePrefix_erases LocalEvent.old oldRx
    (focusStatePrefix_erases RxJoint.Event.access RxJoint.accessEvent
      (txFrontPrefix_erases family addr packets mtu)) w ambient h
  change (runWGPrefix front w ambient h).2.filterMap receiptEvent = h.filterMap receiptEvent at quiet
  change (runWGPrefix front w ambient h).1 =
    ((txFront family addr packets mtu).run w).run ambient at erased
  rw [TransmitJoint.Source.frontWith_run]
  dsimp only [front] at quiet erased
  cases run : runWGPrefix (oldAccess (txFrontPrefix family addr packets mtu)) w ambient h with
  | mk result hist =>
    simp only [run] at quiet erased
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
          exact ⟨erased.symm,⟨pid,rfl⟩⟩

/-- The tail runs after the receipt and cannot remove it, even when it Stops. -/
theorem nativeTransmit_receipts (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : WGWorld) (ambient : Ambient) (h : List LocalEvent) :
    (runWGPrefix (nativeTransmit family addr packets mtu) w ambient h).2.filterMap receiptEvent =
      (runWGPrefix (TransmitJoint.Source.frontWith
        (fun r => LocalEvent.transmit ⟨family,addr,packets,mtu,r⟩)
        (oldAccess (txFrontPrefix family addr packets mtu))) w ambient h).2.filterMap receiptEvent := by
  change (runStatePrefix (nativeTransmit family addr packets mtu) w ambient h).2.filterMap receiptEvent = _
  rw [nativeTransmit,TransmitJoint.Source.transmitWith,runStatePrefix_bind]
  simp only [runWGPrefix]
  cases run : runStatePrefix (TransmitJoint.Source.frontWith
      (fun r => LocalEvent.transmit ⟨family,addr,packets,mtu,r⟩)
      (oldAccess (txFrontPrefix family addr packets mtu))) w ambient h with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out =>
      rcases out with ⟨⟨value,v⟩,after⟩
      cases value with
      | error err => rfl
      | ok pid => exact oldAccess_receipts (txTailPrefix pid) v after hist

theorem nativeTransmit_valid (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : WGWorld) (ambient : Ambient) (h : List LocalEvent) (valid : ReceiptsValid h) :
    ReceiptsValid (runWGPrefix (nativeTransmit family addr packets mtu) w ambient h).2 := by
  intro r member
  rw [nativeTransmit_receipts] at member
  exact front_valid family addr packets mtu w ambient h valid r member

theorem transmit_valid (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : World) (h : List LocalEvent) (valid : ReceiptsValid h) :
    ReceiptsValid (runPrefix (transmit family addr packets mtu) w h).2 :=
  nativeTransmit_valid family addr packets mtu w.wg w.ambient h valid

/-- Concrete local receipt geometry at the source splice. The error cases
retain exactly their reached lifetime journal; the tail receives the receipt
before any send, payment or possible Stop. -/
theorem nativeTransmit_run (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : WGWorld) (ambient : Ambient) (h : List LocalEvent) :
    runWGPrefix (nativeTransmit family addr packets mtu) w ambient h =
      match runWGPrefix (oldAccess (txFrontPrefix family addr packets mtu)) w ambient h with
      | (.error stop,hist) => (.error stop,hist)
      | (.ok ((.error err,v),after),hist) => (.ok ((err,v),after),hist)
      | (.ok ((.ok pid,v),after),hist) =>
        runWGPrefix (oldAccess (txTailPrefix pid)) v after
          (hist ++ [.transmit ⟨family,addr,packets,mtu,⟨.ok pid,w,v,ambient,after⟩⟩]) :=
by
  unfold nativeTransmit
  rw [TransmitJoint.Source.transmitWith_run]
  cases runWGPrefix (oldAccess (txFrontPrefix family addr packets mtu)) w ambient h with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out => rcases out with ⟨⟨value,v⟩,after⟩; cases value <;> rfl

end Leanux.Proofs.WG.Queues.RxTransmit
