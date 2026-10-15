import Leanux.Proofs.WG.Config.SocketReadbackTransportSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- Original coalescing checks the identical repeated device part and the
public-key-only continuation, then appends the two actual IP lists. -/
theorem coalesce_socket_chunks (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front ids : List NodeId) (b : NodeId) (endpoint : p.endpoint = none) :
    coalesce ((socketFirstCall d p nodes front b).skb.messages ++
      (socketLastChunk d p nodes ids).messages) =
      pure (.ok (suffixJson d p nodes (front ++ ids))) := by
  have hn : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  simp [socketFirstCall, socketLastChunk, socketLastCall, socketFirstPeer, coalesce,
    suffixLast, suffixJson, peerFixedAttrs, endpoint, hn, List.forIn_cons, List.forIn_nil,
    bind_assoc, List.lookup, ipv4Jsons, ipv4NodeJson]

theorem receiveDumpStep_front (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId) (sock : NlSock)
    (empty : sock.queue = [])
    (room : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (callback : Returns (wgGetDeviceDump
        { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
        d.deviceUpdateGen {}) (fun w => w.k.wg = some d)
      (fun q w => q = socketLastCall d p nodes (b :: tail) ∧ w.k.wg = some d)) :
    Returns (receiveDumpStep 0 (#[], false))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = socketFirstState sock d p nodes front b)
      (fun q w => q = .yield ((socketFirstCall d p nodes front b).skb.messages.toArray, false) ∧
        w.k.wg = some d ∧ w.k.nlSock7 = socketLastState sock d p nodes (b :: tail)) := by
  simp only [receiveDumpStep, Bool.false_eq_true, if_false]
  apply returns_bind _ _ (netlinkRecvmsg_front d p nodes front b tail sock empty room callback)
  intro q
  rw [returns_iff]
  intro w ⟨heq, hd, hs⟩
  subst q
  simp [socketFirstCall, List.forIn_cons, List.forIn_nil]
  exact ⟨hd, hs⟩

theorem receiveDumpStep_last (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) (sock : NlSock) (empty : sock.queue = []) (messages : Array NlMessage) :
    Returns (receiveDumpStep 1 (messages, false))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = socketLastState sock d p nodes ids)
      (fun q w => q = .yield (messages ++ (socketLastChunk d p nodes ids).messages.toArray, true) ∧
        w.k.wg = some d ∧ w.k.nlSock7 = socketReadbackFinal sock d) := by
  simp only [receiveDumpStep, Bool.false_eq_true, if_false]
  apply returns_bind _ _ (netlinkRecvmsg_last d p nodes ids sock empty)
  intro q
  rw [returns_iff]
  intro w ⟨heq, hd, hs⟩
  subst q
  simp [socketLastChunk, socketLastCall, List.forIn_cons, List.forIn_nil]
  exact ⟨by simp only [Array.push_eq_append, Array.append_assoc]; rfl, hd, hs⟩

theorem getterDrain_two_source :
    getterDrainSource = (do
      let first ← receiveDumpStep 0 (#[], false)
      let second ← match first with
        | .done acc => pure (.done acc)
        | .yield acc => receiveDumpStep 1 acc
      let (messages, finished) ← match second with
        | .done acc => pure acc
        | .yield acc => forIn (List.range' 2 4094) acc receiveDumpStep
      if !finished then invariant "op 9: the dump did not finish"
      coalesce messages.toList) := by
  rw [getterDrain_first]
  congr 1
  funext first
  cases first with
  | done acc => simp [bind_assoc]
  | yield acc =>
    rw [show 4095 = 4094 + 1 from rfl, List.range'_succ]
    simp [List.forIn_cons, bind_assoc]
    congr 1
    funext second
    cases second <;> simp [bind_assoc]

theorem getterDrain_two (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId) (sock : NlSock)
    (empty : sock.queue = []) (endpoint : p.endpoint = none)
    (room : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (callback : Returns (wgGetDeviceDump
        { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
        d.deviceUpdateGen {}) (fun w => w.k.wg = some d)
      (fun q w => q = socketLastCall d p nodes (b :: tail) ∧ w.k.wg = some d)) :
    Returns getterDrainSource
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = socketFirstState sock d p nodes front b)
      (fun q w => q = .ok (suffixJson d p nodes (front ++ b :: tail)) ∧
        w.k.wg = some d ∧ w.k.nlSock7 = socketReadbackFinal sock d) := by
  intro entry pre
  obtain ⟨first, middle, runFirst, firstEq, hd, hs⟩ :=
    receiveDumpStep_front d p nodes front b tail sock empty room callback entry pre
  subst first
  obtain ⟨second, final, runSecond, secondEq, hdFinal, hsFinal⟩ :=
    receiveDumpStep_last d p nodes (b :: tail) sock empty
      (socketFirstCall d p nodes front b).skb.messages.toArray middle ⟨hd, hs⟩
  subst second
  refine ⟨.ok (suffixJson d p nodes (front ++ b :: tail)), final, ?_, rfl, hdFinal, hsFinal⟩
  have okbind {α β : Type} (x : α) (f : α → Except Stop β) :
      ((Except.ok x : Except Stop α) >>= f) = f x := rfl
  simp only [getterDrain_two_source, StateT.run_bind, runFirst, okbind, runSecond,
    receiveDump_finished, StateT.run_pure, pure_bind, Bool.not_true, Bool.false_eq_true, if_false,
    Array.toList_append, List.toList_toArray]
  rw [coalesce_socket_chunks d p nodes front (b :: tail) b endpoint]
  rfl

end Leanux.Proofs.WG.Config
