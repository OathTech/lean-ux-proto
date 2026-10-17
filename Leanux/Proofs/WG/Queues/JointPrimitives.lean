import Leanux.Proofs.WG.Lifetimes.ConfigurationLeaves
import Leanux.Proofs.WG.Queues.RxPollComposition
import Leanux.Proofs.WG.AllowedIps.RoutingCompletions
import Leanux.Proofs.Logged.NativeCapture

/-! A single native execution retains the existing lifetime observer and adds
its actual routing completion. The two projections retain all other entries
in their respective incoming streams, including saved probes and RX receipts.
A Stop keeps the access prefix but does not manufacture a completion. -/
namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps

inductive Event where
  | routing (completion : RoutingCompletion)
  | rx (event : RxHistory.Event)

def routingEvent : Event → Option RoutingCompletion
  | .routing e => some e
  | .rx _ => none

def rxEvent : Event → Option RxHistory.Event
  | .routing _ => none
  | .rx e => some e

/-- The same nested focus as the existing product RX observer, on the actual
WG/Ambient stack. Arbitrary incoming probe and receipt entries are retained. -/
def nativeRx (g : WGPrefix LifetimeEvent α) : WGPrefix RxHistory.Event α :=
  focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? g)

def access (g : WGPrefix LifetimeEvent α) : WGPrefix Event α :=
  focusStatePrefix Event.rx rxEvent (nativeRx g)

theorem nativeRx_product (g : WGPrefix LifetimeEvent α) :
    liftWGObserver (nativeRx g) = RxHistory.mixed (liftWGObserver g) := rfl

theorem access_erases {g : WGPrefix LifetimeEvent α} {a : WG.M α}
    (hg : ErasesStatePrefix g a) : ErasesStatePrefix (access g) a :=
  focusStatePrefix_erases _ _ (focusStatePrefix_erases _ _
    (focusStatePrefix_erases _ _ hg))

theorem access_appends (g : WGPrefix LifetimeEvent α) : StateAppends (access g) :=
  StateAppends.focus _ _ _

theorem access_rx (g : WGPrefix LifetimeEvent α) :
    StateProjectsPrefix rxEvent id (access g) (nativeRx g) := by
  intro w
  exact (StateAppends.focus RxHistory.Event.audit RxHistory.auditEvent
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? g) w).project_focus
      Event.rx rxEvent (fun _ => rfl)

theorem access_routing (g : WGPrefix LifetimeEvent α) :
    StateHistoryFrame routingEvent (access g) :=
  fun w => focusPrefix_other Event.rx rxEvent routingEvent (fun _ => rfl) ((nativeRx g).run w)

/-- Capture exactly one existing native observer and emit after its normal
return. A negative Int remains a normal result, so it also gets its completion. -/
def completed (g : WGPrefix LifetimeEvent α) (call : α → RoutingCompletedCall) :
    WGPrefix Event α :=
  receiptWGObserved (access g) (fun r => .routing
    ⟨call r.value, routingView r.before, routingView r.after⟩)

theorem completed_run (g : WGPrefix LifetimeEvent α) (call : α → RoutingCompletedCall)
    (w : WGWorld) (ambient : Ambient) (h : List Event) :
    runWGPrefix (completed g call) w ambient h =
      match runWGPrefix (access g) w ambient h with
      | (.error e, history) => (.error e, history)
      | (.ok ((x,v),ambient'), history) =>
        (.ok ((x,v),ambient'), history ++ [.routing ⟨call x,routingView w,routingView v⟩]) :=
by
  unfold completed
  rw [runWGPrefix_receiptWGObserved]
  cases runWGPrefix (access g) w ambient h with
  | mk result history =>
    cases result with
    | error e => rfl
    | ok out => rcases out with ⟨⟨x,v⟩,ambient'⟩; rfl

theorem completed_appends (g : WGPrefix LifetimeEvent α) (call : α → RoutingCompletedCall) :
    StateAppends (completed g call) :=
  (access_appends g).receiptWGObserved _

theorem completed_erases {g : WGPrefix LifetimeEvent α} {a : WG.M α}
    (hg : ErasesStatePrefix g a) (call : α → RoutingCompletedCall) :
    ErasesStatePrefix (completed g call) a :=
  receiptWGObserved_erases (access_erases hg) _

theorem completed_rx (g : WGPrefix LifetimeEvent α) (call : α → RoutingCompletedCall) :
    StateProjectsPrefix rxEvent id (completed g call) (nativeRx g) := by
  intro w ambient h
  have hp := access_rx g w ambient h
  change runWGPrefix (nativeRx g) w ambient (h.filterMap rxEvent) =
    ((runWGPrefix (completed g call) w ambient h).1.map
      (fun ((x,v),a) => ((x,v),a)),
      (runWGPrefix (completed g call) w ambient h).2.filterMap rxEvent)
  rw [completed_run]
  change runWGPrefix (nativeRx g) w ambient (h.filterMap rxEvent) =
    ((runWGPrefix (access g) w ambient h).1.map
      (fun ((x,v),a) => ((x,v),a)),
      (runWGPrefix (access g) w ambient h).2.filterMap rxEvent) at hp
  cases hr : runWGPrefix (access g) w ambient h with
  | mk result history =>
    cases result with
    | error e => simpa only [hr] using hp
    | ok out =>
      rcases out with ⟨⟨x,v⟩,ambient'⟩
      simpa only [hr,List.filterMap_append,List.filterMap_cons,rxEvent,
        List.filterMap_nil,List.append_nil] using hp

/-- Exact projection to the unchanged product RX observer, with its actual
incoming history. No history-independence or allocation premise is needed. -/
theorem completed_rx_product (g : WGPrefix LifetimeEvent α) (call : α → RoutingCompletedCall) :
    ProjectsPrefix rxEvent id (liftWGObserver (completed g call))
      (RxHistory.mixed (liftWGObserver g)) := by
  rw [← nativeRx_product]
  exact (completed_rx g call).liftWGObserver _ _

theorem completed_routing_run {g : WGPrefix LifetimeEvent α} {a : WG.M α}
    (hg : ErasesStatePrefix g a) (call : α → RoutingCompletedCall)
    (w : WGWorld) (ambient : Ambient) (h : List Event) :
    ((runWGPrefix (completed g call) w ambient h).1,
      (runWGPrefix (completed g call) w ambient h).2.filterMap routingEvent) =
      match (a.run w).run ambient with
      | .error e => (.error e,h.filterMap routingEvent)
      | .ok ((x,v),ambient') => (.ok ((x,v),ambient'),
          h.filterMap routingEvent ++ [⟨call x,routingView w,routingView v⟩]) := by
  have he := access_erases hg w ambient h
  have hh := access_routing g w ambient h
  change (runWGPrefix (access g) w ambient h).1 = (a.run w).run ambient at he
  change (runWGPrefix (access g) w ambient h).2.filterMap routingEvent =
    h.filterMap routingEvent at hh
  rw [completed_run]
  cases hr : runWGPrefix (access g) w ambient h with
  | mk result history =>
    simp only [hr] at he hh
    rw [← he]
    cases result with
    | error e => exact Prod.ext rfl hh
    | ok out =>
      rcases out with ⟨⟨x,v⟩,ambient'⟩
      simp only [List.filterMap_append,List.filterMap_cons,routingEvent,
        List.filterMap_nil,hh]

def completedAllowedip (pid : PeerId) (attrs : AllowedIpAttrs) : WGPrefix Event Int :=
  completed (setAllowedipPrefix pid attrs) (.allowedIp pid attrs)

def completedRemovePeer (pid : PeerId) : WGPrefix Event Unit :=
  completed (removeByPeerPrefix pid) (fun _ => .removePeer pid)

def completedFree : WGPrefix Event Unit :=
  completed freeAllowedIpsPrefix (fun _ => .clear)

theorem completedAllowedip_erases (pid : PeerId) (attrs : AllowedIpAttrs) :
    ErasesStatePrefix (completedAllowedip pid attrs) (setAllowedip pid attrs) :=
  completed_erases (setAllowedipPrefix_erases pid attrs) _

theorem completedRemovePeer_erases (pid : PeerId) :
    ErasesStatePrefix (completedRemovePeer pid) (removeByPeer pid) :=
  completed_erases (removeByPeerPrefix_erases pid) _

theorem completedFree_erases : ErasesStatePrefix completedFree WG.free :=
  completed_erases freeAllowedIpsPrefix_erases _

theorem completedAllowedip_routing (pid : PeerId) (attrs : AllowedIpAttrs) :
    StateProjectsPrefix routingEvent id (completedAllowedip pid attrs)
      (AllowedIps.completedAllowedip pid attrs) := by
  intro w ambient h
  have hr := completed_routing_run (setAllowedipPrefix_erases pid attrs)
    (.allowedIp pid attrs) w ambient h
  change runWGPrefix (AllowedIps.completedAllowedip pid attrs) w ambient
    (h.filterMap routingEvent) = _
  calc
    _ = ((runWGPrefix (completedAllowedip pid attrs) w ambient h).1,
        (runWGPrefix (completedAllowedip pid attrs) w ambient h).2.filterMap routingEvent) := by
      rw [AllowedIps.completedAllowedip_run]
      cases result : ((setAllowedip pid attrs).run w).run ambient with
      | error e => simpa only [result,completedAllowedip] using hr.symm
      | ok out =>
        rcases out with ⟨⟨x,v⟩,ambient'⟩
        simpa only [result,completedAllowedip] using hr.symm
    _ = _ := by
      change (_,_) = ((runWGPrefix (completedAllowedip pid attrs) w ambient h).1.map
        (fun ((x,v),a) => ((x,v),a)),_)
      cases (runWGPrefix (completedAllowedip pid attrs) w ambient h).1 <;> rfl

theorem completedRemovePeer_routing (pid : PeerId) :
    StateProjectsPrefix routingEvent id (completedRemovePeer pid)
      (AllowedIps.completedRemovePeer pid) := by
  intro w ambient h
  have hr := completed_routing_run (removeByPeerPrefix_erases pid)
    (fun _ => .removePeer pid) w ambient h
  change runWGPrefix (AllowedIps.completedRemovePeer pid) w ambient
    (h.filterMap routingEvent) = _
  calc
    _ = ((runWGPrefix (completedRemovePeer pid) w ambient h).1,
        (runWGPrefix (completedRemovePeer pid) w ambient h).2.filterMap routingEvent) := by
      rw [AllowedIps.completedRemovePeer_run]
      cases result : ((removeByPeer pid).run w).run ambient with
      | error e => simpa only [result,completedRemovePeer] using hr.symm
      | ok out =>
        rcases out with ⟨⟨u,v⟩,ambient'⟩
        cases u
        simpa only [result,completedRemovePeer] using hr.symm
    _ = _ := by
      change (_,_) = ((runWGPrefix (completedRemovePeer pid) w ambient h).1.map
        (fun ((x,v),a) => ((x,v),a)),_)
      cases (runWGPrefix (completedRemovePeer pid) w ambient h).1 <;> rfl

theorem completedFree_routing :
    StateProjectsPrefix routingEvent id completedFree AllowedIps.completedFree := by
  intro w ambient h
  have hr := completed_routing_run freeAllowedIpsPrefix_erases
    (fun _ => .clear) w ambient h
  change runWGPrefix AllowedIps.completedFree w ambient (h.filterMap routingEvent) = _
  calc
    _ = ((runWGPrefix completedFree w ambient h).1,
        (runWGPrefix completedFree w ambient h).2.filterMap routingEvent) := by
      rw [AllowedIps.completedFree_run]
      cases result : (WG.free.run w).run ambient with
      | error e => simpa only [result,completedFree] using hr.symm
      | ok out =>
        rcases out with ⟨⟨u,v⟩,ambient'⟩
        cases u
        simpa only [result,completedFree] using hr.symm
    _ = _ := by
      change (_,_) = ((runWGPrefix completedFree w ambient h).1.map
        (fun ((x,v),a) => ((x,v),a)),_)
      cases (runWGPrefix completedFree w ambient h).1 <;> rfl

end Leanux.Proofs.WG.Queues.RoutingJoint
