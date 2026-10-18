import Leanux.Proofs.WG.Queues.JointRunner
import Leanux.Proofs.WG.Origins.CurrentChecks
import Leanux.Proofs.WG.Configuration.LifecycleCompletion
import Leanux.Proofs.WG.Packets.PublicationRetained

/-! Routing evidence is indexed by the strict joint prefix of a captured
consume. The local source rule records the real entry even on normal None;
Stops add no invented receipt. Whole initialized preservation is not assumed. -/
namespace Leanux.Proofs.WG.RoutingPosition
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps Packets

def Checked (initial : FlatTable × FlatTable) (pre : List RoutingJoint.Event) :
    RoutingJoint.Event → Prop
  | .rx (.consumed _ _ _ r) =>
      GlobalCompletionState initial (pre.filterMap RoutingJoint.routingEvent) r.run.before
  | _ => True

def Checks (initial : FlatTable × FlatTable) (h : List RoutingJoint.Event) : Prop :=
  ∀ pre e post, h = pre ++ e :: post → Checked initial pre e

def Inv (initial : FlatTable × FlatTable) (h : List RoutingJoint.Event) (w : World) : Prop :=
  GlobalCompletionState initial (h.filterMap RoutingJoint.routingEvent) w.wg ∧ Checks initial h

def Safe (initial : FlatTable × FlatTable) (h : List RoutingJoint.Event) : Prop :=
  CompletionSafe initial (h.filterMap RoutingJoint.routingEvent) ∧ Checks initial h

theorem Checks.append (hh : Checks initial h)
    (hs : ∀ pre e post, s = pre ++ e :: post → Checked initial (h ++ pre) e) :
    Checks initial (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    (Checked initial) h s hh hs

theorem Inv.safe (hi : Inv initial h w) : Safe initial h := ⟨hi.1.1,hi.2⟩

theorem inv_initial (trace : Runner.Trace) (w : World)
    (hw : wgStoreView w.wg = wgStoreView (Runner.initialWG trace.net trace.bare)) :
    Inv ([],[]) [] w := by
  refine ⟨Configuration.global_initial trace w hw,?_⟩
  intro pre e post impossible
  cases pre <;> cases impossible

/-- Arbitrary actual product actions retain the positional checks while their
existing routing relation transports the current routing state. -/
theorem lift_preserves (initial : FlatTable × FlatTable) (a : Leanux.M α)
    (ha : ProjectedRetainsRoutingCall World.wg a) :
    PrefixPreserves (Inv initial) (Safe initial) (liftPrefix a) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  exact ⟨⟨hi.1.1,hi.1.2.retains ((ProjectedAction.iff_run _ _ _).mp ha w x v hr)⟩,hi.2⟩

/-- Normal routing and occurrence checks are joined on the identical joint
invocation. The callback/action domain remains the arbitrary product observer. -/
theorem combine (initial : FlatTable × FlatTable) (g : PrefixM RoutingJoint.Event α)
    (a : PrefixM RoutingCompletion α) (appends : Appends g)
    (projection : ProjectsPrefix RoutingJoint.routingEvent id g a)
    (routing : PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg)
      (CompletionSafe initial) a)
    (captures : ∀ w h, Inv initial h w → Checks initial (runPrefix g w h).2) :
    PrefixPreserves (Inv initial) (Safe initial) g := by
  intro w h hi
  obtain ⟨suffix,hs⟩ := appends w h
  obtain ⟨_,_,safe,normal⟩ := routing w (h.filterMap RoutingJoint.routingEvent) hi.1
  have projected := projection w h
  rw [projected] at safe normal
  have checked := captures w h hi
  refine ⟨suffix,hs,⟨safe,checked⟩,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    have state : GlobalCompletionState initial
        ((runPrefix g w h).2.filterMap RoutingJoint.routingEvent) out.2.wg := by
      simpa only [result,Except.map,id_eq] using normal
    exact ⟨state,checked⟩

/-- The existing native capture freezes its actual WG and Ambient entry.
Only the newly emitted suffix is examined; old receipts remain arbitrary. -/
theorem consume_entry (pid occurrence id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (endpoint : Endpoint) (w : World) (h : List RxJoint.Event) :
    ∃ suffix,
      (runPrefix (RxJoint.consume pid occurrence id stamp pkt endpoint) w h).2 = h ++ suffix ∧
      ∀ n skb saved receipt, RxJoint.Event.consumed n skb saved receipt ∈ suffix →
        receipt.run.before = w.wg ∧ receipt.run.ambientBefore = w.ambient := by
  let a := liftWGObserver (consumeDataDonePrefix pid pkt endpoint)
  let raw := runPrefix a w (h.filterMap RxJoint.accessEvent)
  let extra := (raw.2.drop (h.filterMap RxJoint.accessEvent).length).map RxJoint.Event.access
  have access : runPrefix (RxJoint.access a) w h = (raw.1,h ++ extra) := rfl
  have quiet : ∀ n skb saved receipt, RxJoint.Event.consumed n skb saved receipt ∉ extra := by
    intro n skb saved receipt member
    obtain ⟨event,_,same⟩ := List.mem_map.mp member
    cases same
  rw [RxJoint.consume_run,access]
  cases result : raw.1 with
  | error stop => exact ⟨extra,rfl,fun n skb saved receipt member => False.elim (quiet n skb saved receipt member)⟩
  | ok out =>
    rcases out with ⟨returned,v⟩
    let receipt : RxDisposition.ConsumeReceipt :=
      ⟨pid,pkt,endpoint,⟨returned,w.wg,v.wg,w.ambient,v.ambient⟩⟩
    cases returned with
    | none =>
      refine ⟨extra ++ [.consumed occurrence id stamp receipt],by simp only [List.append_assoc]; rfl,?_⟩
      intro n skb saved r member
      rcases List.mem_append.mp member with old | new
      · exact False.elim (quiet n skb saved r old)
      · have same := List.mem_singleton.mp new
        cases same
        exact ⟨rfl,rfl⟩
    | some bytes =>
      let entry : RxJoint.Entry := ⟨⟨occurrence,id,bytes⟩,stamp,some receipt⟩
      refine ⟨extra ++ [.consumed occurrence id stamp receipt,.buffered entry],by simp only [List.append_assoc]; rfl,?_⟩
      intro n skb saved r member
      rcases List.mem_append.mp member with old | new
      · exact False.elim (quiet n skb saved r old)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at new
        rcases new with same | impossible
        · cases same
          exact ⟨rfl,rfl⟩
        · cases impossible

/-- A lower consume suffix is injected by the existing two event constructors.
There are no routing completions inside that suffix; its earlier routing
prefix is therefore exactly the caller's entry prefix. -/
theorem checks_consume_suffix (hi : Inv initial h w) (pid occurrence id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (endpoint : Endpoint) (localHistory : List RxJoint.Event) :
    ∃ suffix,
      (runPrefix (RxJoint.consume pid occurrence id stamp pkt endpoint) w localHistory).2 =
        localHistory ++ suffix ∧
      Checks initial (h ++ suffix.map (fun e => RoutingJoint.Event.rx (RxHistory.promote e))) := by
  obtain ⟨suffix,hs,entry⟩ := consume_entry pid occurrence id stamp pkt endpoint w localHistory
  refine ⟨suffix,hs,hi.2.append ?_⟩
  intro pre event post position
  have member : event ∈ suffix.map (fun e => RoutingJoint.Event.rx (RxHistory.promote e)) := by
    rw [position]
    simp
  obtain ⟨lower,hl,he⟩ := List.mem_map.mp member
  subst event
  cases lower <;> try trivial
  case consumed n skb saved receipt =>
    have before := (entry n skb saved receipt hl).1
    have noRouting : (pre ++ RoutingJoint.Event.rx (RxHistory.promote (.consumed n skb saved receipt)) :: post).filterMap
        RoutingJoint.routingEvent = [] := by
      rw [← position]
      exact filterMap_disjoint _ _ (fun _ => rfl) _
    have projectedPrefix : pre.filterMap RoutingJoint.routingEvent = [] := by
      simp only [List.filterMap_append,List.filterMap_cons,RoutingJoint.routingEvent] at noRouting
      exact (List.append_eq_nil_iff.mp noRouting).1
    change GlobalCompletionState initial ((h ++ pre).filterMap RoutingJoint.routingEvent) receipt.run.before
    simpa only [List.filterMap_append,projectedPrefix,List.append_nil,before] using hi.1

/-- Routing at the captured entry yields authorization only for an actual
Some payload. Normal None and stopped executions gain no delivery claim. -/
theorem consume_authorized {occurrence id : Nat} {stamp : PacketStamp}
    {receipt : RxDisposition.ConsumeReceipt} (checks : Checks initial h)
    (position : h = pre ++ .rx (.consumed occurrence id stamp receipt) :: post)
    (valid : receipt.Valid) (bytes : List UInt8) (delivered : receipt.run.value = some bytes) :
    ∃ v4 : Bool, ipTunnelParseProtocol bytes = (if v4 then 4 else 6) ∧
      ipTunnelParseProtocol receipt.packet.bytes = (if v4 then 4 else 6) ∧
      PeerWinner (rootWidth v4) (sourceAddress v4 bytes)
        (selectedFlat v4 (completionFold (pre.filterMap RoutingJoint.routingEvent) initial))
        (some receipt.peer) ∧
      sourceAddress v4 bytes = sourceAddress v4 receipt.packet.bytes := by
  have state := checks pre (.rx (.consumed occurrence id stamp receipt)) post position
  have resident := PublicationIdentity.consume_peer_resident receipt.peer receipt.packet receipt.endpoint
    receipt.run.before receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter receipt.run.value valid
  obtain ⟨d,p,hd,_⟩ := resident
  have present : routingView receipt.run.before ≠ none := by simp only [routingView,hd,Option.map_some]; intro impossible; cases impossible
  exact consumeDataDone_authorized receipt.peer receipt.packet receipt.endpoint
    receipt.run.before receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter bytes _
    (state.2.present present) (by simpa only [RxDisposition.ConsumeReceipt.Valid,WGRunWitness.Valid,delivered] using valid)

end Leanux.Proofs.WG.RoutingPosition
