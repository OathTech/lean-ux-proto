import Leanux.Proofs.WG.Packets.TransmitReceipts
import Leanux.Proofs.WG.Configuration.ConsumedRouting

/-! Transmit checks are indexed by the strict prefix of the actual handoff.
The routing state belongs to its captured front entry, not a later endpoint. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Packets AllowedIps

def routes (h : List Event) : List RoutingCompletion :=
  (h.filterMap oldEvent).filterMap RoutingJoint.routingEvent

def Checked (initial : FlatTable × FlatTable) (pre : List Event) : Event → Prop
  | .old _ => True
  | .transmit r => r.Valid ∧ GlobalCompletionState initial (routes pre) r.run.before

def Checks (initial : FlatTable × FlatTable) (h : List Event) : Prop :=
  ∀ pre event post, h = pre ++ event :: post → Checked initial pre event

def Inv (initial : FlatTable × FlatTable) (h : List Event) (w : World) : Prop :=
  GlobalCompletionState initial (routes h) w.wg ∧ Checks initial h

def Safe (initial : FlatTable × FlatTable) (h : List Event) : Prop :=
  CompletionSafe initial (routes h) ∧ Checks initial h

theorem Inv.safe (hi : Inv initial h w) : Safe initial h := ⟨hi.1.1,hi.2⟩

theorem Checks.append (hh : Checks initial h)
    (hs : ∀ pre e post, s = pre ++ e :: post → Checked initial (h ++ pre) e) :
    Checks initial (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    (Checked initial) h s hh hs

theorem Checks.focusedOld (g : WGPrefix RoutingJoint.Event α) (w : WGWorld) (ambient : Ambient)
    (hh : Checks initial h) : Checks initial (runWGPrefix (old g) w ambient h).2 := by
  let suffix := ((runWGPrefix g w ambient (h.filterMap oldEvent)).2.drop
    (h.filterMap oldEvent).length).map Event.old
  have history : (runWGPrefix (old g) w ambient h).2 = h ++ suffix := rfl
  rw [history]
  apply hh.append
  intro pre event post position
  have member : event ∈ suffix := by rw [position]; simp
  obtain ⟨lower,_,same⟩ := List.mem_map.mp member
  subst event
  trivial

theorem old_routes (g : WGPrefix RoutingJoint.Event α) (hg : StateAppends g)
    (frame : StateHistoryFrame RoutingJoint.routingEvent g)
    (w : WGWorld) (ambient : Ambient) (h : List Event) :
    routes (runWGPrefix (old g) w ambient h).2 = routes h := by
  have projected := congrArg Prod.snd (old_projects g hg w ambient h)
  change (runWGPrefix g w ambient (h.filterMap oldEvent)).2 =
    (runWGPrefix (old g) w ambient h).2.filterMap oldEvent at projected
  have kept := frame w ambient (h.filterMap oldEvent)
  unfold routes
  rw [← projected]
  exact kept

/-- No earlier supplied receipt is recertified from a later endpoint. The
single fresh receipt uses the actual front entry and its unchanged route fold. -/
theorem observeFront_checks (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (appends : StateAppends front) (frame : StateHistoryFrame RoutingJoint.routingEvent front)
    (source : ErasesStatePrefix front (txFront family addr packets mtu))
    (w : WGWorld) (ambient : Ambient) (h : List Event)
    (routing : GlobalCompletionState initial (routes h) w) (checked : Checks initial h) :
    Checks initial (runWGPrefix (observeFront family addr packets mtu front) w ambient h).2 := by
  have oldChecked := checked.focusedOld front w ambient
  have oldRouting := old_routes front appends frame w ambient h
  have erasure := focusStatePrefix_erases Event.old oldEvent source w ambient h
  change (runWGPrefix (old front) w ambient h).1 =
    ((txFront family addr packets mtu).run w).run ambient at erasure
  rw [observeFront_run]
  cases run : runWGPrefix (old front) w ambient h with
  | mk result hist =>
    simp only [run] at oldChecked oldRouting erasure
    cases result with
    | error stop => exact oldChecked
    | ok out =>
      rcases out with ⟨⟨value,v⟩,after⟩
      cases value with
      | error err => exact oldChecked
      | ok pid =>
        apply oldChecked.append
        intro pre event post position
        have first : pre = [] := by
          have sizes := congrArg List.length position
          simp only [List.length_append,List.length_cons,List.length_nil] at sizes
          have empty : pre.length = 0 := by omega
          exact List.eq_nil_of_length_eq_zero empty
        subst pre
        simp only [List.nil_append,List.cons.injEq] at position
        obtain ⟨rfl,_⟩ := position
        change _ ∧ GlobalCompletionState initial (routes (hist ++ [])) w
        refine ⟨⟨erasure.symm,⟨pid,rfl⟩⟩,?_⟩
        simpa only [List.append_nil,oldRouting] using routing

/-- The actual successful front necessarily starts with a present device;
its protocol/header prefix preserves the routing view before destination lookup. -/
theorem Receipt.present (r : Receipt) (valid : r.Valid) : routingView r.run.before ≠ none := by
  obtain ⟨pid,selected⟩ := valid.2
  have run := valid.1
  simp only [WGRunWitness.Valid,selected] at run
  obtain ⟨u,q,v,a,b,c,check,lookup,_,_⟩ := txFront_cut r.family r.addr r.packets r.mtu
    r.run.before r.run.after r.run.ambientBefore r.run.ambientAfter pid run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (txCheck_routing r.family r.addr r.packets r.mtu)
    r.run.before r.run.ambientBefore true u a check
  intro absent
  have unavailable : routingView u = none := same.trans absent
  cases device : u.dev with
  | none =>
    simp [lookupDst,getDev,device,invariant,AmbientM.invariant] at lookup
    change Except.error _ = Except.ok _ at lookup
    cases lookup
  | some d => simp [routingView,device] at unavailable

/-- A specified handoff gets its destination winner from the earlier routing
prefix attached to that same receipt. No final World is needed. -/
theorem Checks.winner (checked : Checks initial h) (pre post : List Event) (r : Receipt)
    (position : h = pre ++ .transmit r :: post) :
    ∃ (pid : PeerId) (v4 : Bool), r.run.value = .ok pid ∧
      r.family = (if v4 then 4 else 6) ∧
      TxFrontCut (if v4 then 4 else 6) r.addr r.packets r.mtu r.run.before
        r.run.after r.run.ambientBefore r.run.ambientAfter pid ∧
      PeerWinner (rootWidth v4) r.addr
        (selectedFlat v4 (completionFold (routes pre) initial)) (some pid) ∧
      ∀ pkt ∈ r.packets, destinationField (if v4 then 4 else 6) pkt.bytes = r.addr := by
  have capture := checked pre (.transmit r) post position
  exact r.winner capture.1 _ (capture.2.2.present (r.present capture.1))

end Leanux.Proofs.WG.TransmitJoint
