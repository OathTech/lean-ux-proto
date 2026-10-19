import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchSource

/-! History safety through the native receive, clear and dump repayments.
Each release callback must preserve the predicate; native state frames are
separate and cannot erase a possible disposal event. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
open TransmitSecurity.Driver
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

structure Ops.History (Safe : List E → Prop) (ops : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (action : WG.M α), StateHistorySafe Safe (ops.step action)
  release : ∀ peer, StateHistorySafe Safe (ops.release peer)

macro "nested_release_history " h:ident : tactic => `(tactic| first
  | with_reducible exact Ops.History.step $h _
  | with_reducible exact Ops.History.release $h _
  | driver_state_history_step)

variable {Safe : List E → Prop} {g : Ops (WGPrefix E)}

theorem clear_history (h : Ops.History Safe g) (pid : PeerId) :
    StateHistorySafe Safe (clearWith g pid) := by
  unfold clearWith
  repeat' first
    | nested_release_history h

theorem flushedClear_history (h : Ops.History Safe g) (pid : PeerId) :
    StateHistorySafe Safe (flushedClearWith g pid) := by
  unfold flushedClearWith
  repeat' first
    | with_reducible exact clear_history h _
    | nested_release_history h

theorem cleanup_history (h : Ops.History Safe g) (id : SkbId) (pkt : RxPacket) (flag : Bool) :
    StateHistorySafe Safe (cleanupWith g id pkt flag) := by
  unfold cleanupWith
  repeat' first
    | nested_release_history h

theorem rx_publish_history (h : Ops.History Safe g) (irq : WGPrefix E Unit) (skb : SkbId) (state : PacketState) (hirq : StateHistorySafe Safe irq) :
    StateHistorySafe Safe (publishWith g irq skb state) := by
  unfold publishWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hirq
    | nested_release_history h

theorem rx_admit_history (h : Ops.History Safe g) (allocate : RxPacket → WGPrefix E SkbId) (msg : Key) (src : SkbSource) (ds : Nat) (hallocate : ∀ x, StateHistorySafe Safe (allocate x)) :
    StateHistorySafe Safe (admitWith g allocate msg src ds) := by
  unfold admitWith RxOrigin.admitWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hallocate _
    | nested_release_history h

theorem rx_ingressFinish_history (h : Ops.History Safe g) (publish : SkbId → WGPrefix E Unit) (a : RxOrigin.Admission) (hpublish : ∀ x, StateHistorySafe Safe (publish x)) :
    StateHistorySafe Safe (ingressFinishWith g publish a) := by
  unfold ingressFinishWith RxOrigin.finishWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hpublish _
    | nested_release_history h

theorem rx_ingress_history (h : Ops.History Safe g) (msg : Key) (src : SkbSource) (ds : Nat) :
    StateHistorySafe Safe (ingress g msg src ds) := by
  unfold ingress ingressWith ingressFinishWith RxOrigin.finishWith admitWith RxOrigin.admitWith publishWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_history h

theorem rx_rxAfterLookup_history (h : Ops.History Safe g) (pid : PeerId) (ready : Packets.RxReady) (routed : Option PeerId) :
    StateHistorySafe Safe (rxAfterLookupWith g pid ready routed) := by
  unfold rxAfterLookupWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_history h

theorem rx_rxFinish_history (h : Ops.History Safe g) (pid : PeerId) (ready : Packets.RxReady) :
    StateHistorySafe Safe (rxFinishWith g pid ready) := by
  unfold rxFinishWith rxAfterLookupWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_history h

theorem packetReceive_history {g : Ops (WGPrefix E)}
    (h : Ops.History Safe g) (consume : Key → SkbSource → Nat → WGPrefix E Unit)
    (hc : ∀ msg src ds, StateHistorySafe Safe (consume msg src ds))
    (msg : Key) (src : SkbSource) :
    StateHistorySafe Safe (packetReceiveWith g consume msg src) := by
  unfold packetReceiveWith
  repeat' first
    | with_reducible exact hc _ _ _
    | nested_release_history h

theorem receiveWith_history {g : Ops (WGPrefix E)}
    (h : Ops.History Safe g) (consume : Key → SkbSource → Nat → WGPrefix E Unit)
    (hc : ∀ msg src ds, StateHistorySafe Safe (consume msg src ds))
    (msg : Key) (src : SkbSource) :
    StateHistorySafe Safe (receiveWith g consume msg src) := by
  unfold receiveWith
  repeat' first
    | with_reducible exact packetReceive_history h consume hc _ _
    | nested_release_history h

theorem receive_history {g : Ops (WGPrefix E)}
    (h : Ops.History Safe g) (msg : Key) (src : SkbSource) :
    StateHistorySafe Safe (receive g msg src) :=
  receiveWith_history h _ (rx_ingress_history h) msg src

theorem dumpDone_history (h : Ops.History Safe g) (ctx : DumpCtx) :
    StateHistorySafe Safe (dumpDoneWith g ctx) := by
  unfold dumpDoneWith
  repeat' first
    | nested_release_history h

theorem dumpReplace_history (h : Ops.History Safe g) (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) :
    StateHistorySafe Safe (dumpReplaceWith g ctx nextCursor done) := by
  unfold dumpReplaceWith
  repeat' first
    | nested_release_history h

theorem dumpFinish_history (h : Ops.History Safe g) (seq : Nat) (ctx : DumpCtx) (nextCursor : Option PeerId) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) (done : Bool) (peers : Option (Array PeerDumpAttrs)) :
    StateHistorySafe Safe (dumpFinishWith g seq ctx nextCursor skb flags attrs done peers) := by
  unfold dumpFinishWith
  repeat' first
    | with_reducible exact dumpReplace_history h _ _ _
    | nested_release_history h

theorem dumpTail_history (h : Ops.History Safe g) (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) :
    StateHistorySafe Safe (dumpTailWith g d ctx skb flags attrs) := by
  unfold dumpTailWith
  repeat' first
    | with_reducible exact dumpFinish_history h _ _ _ _ _ _ _ _
    | nested_release_history h

theorem dumpChunk_history (h : Ops.History Safe g) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    StateHistorySafe Safe (dumpChunkWith g ctx prevSeq skb) := by
  unfold dumpChunkWith
  repeat' first
    | with_reducible exact dumpTail_history h _ _ _ _ _
    | nested_release_history h

theorem dumpSocket_history (h : Ops.History Safe g) (fd : Nat) :
    StateHistorySafe Safe (dumpSocketWith g fd) := by
  unfold dumpSocketWith
  repeat' first
    | with_reducible exact dumpChunk_history h _ _ _
    | with_reducible exact dumpDone_history h _
    | nested_release_history h

theorem dumpStart_history (h : Ops.History Safe g) (fd : Nat) (ref : DeviceRef) :
    StateHistorySafe Safe (dumpStartWith g fd ref) := by
  unfold dumpStartWith
  repeat' first
    | with_reducible exact dumpSocket_history h _
    | nested_release_history h

theorem dumpReceive_history (h : Ops.History Safe g) (fd : Nat) :
    StateHistorySafe Safe (dumpReceiveWith g fd) := by
  unfold dumpReceiveWith
  repeat' first
    | with_reducible exact dumpSocket_history h _
    | nested_release_history h

theorem dumpDevice_history (h : Ops.History Safe g) (ref : DeviceRef) :
    StateHistorySafe Safe (dumpDeviceWith g ref) := by
  unfold dumpDeviceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact dumpStart_history h _ _
    | with_reducible exact dumpReceive_history h _
    | nested_release_history h

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
