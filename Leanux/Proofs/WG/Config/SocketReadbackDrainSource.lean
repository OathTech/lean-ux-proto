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
    List.lookup, ipv4Jsons, ipv4NodeJson]

theorem receiveDumpStep_front (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId) (sock : NlSock)
    (empty : sock.queue = [])
    (room : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (callback : Returns (wgGetDeviceDump
        { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
        d.deviceUpdateGen {}) (fun w => w.dev = some d)
      (fun q w => q = socketLastCall d p nodes (b :: tail) ∧ w.dev = some d)) :
    Returns (receiveDumpStep 0 (#[], false))
      (fun w => w.dev = some d ∧ w.nlSock7 = socketFirstState sock d p nodes front b)
      (fun q w => q = .yield ((socketFirstCall d p nodes front b).skb.messages.toArray, false) ∧
        w.dev = some d ∧ w.nlSock7 = socketLastState sock d p nodes (b :: tail)) := by
  simp only [receiveDumpStep, Bool.false_eq_true, ite_false]
  apply returns_bind _ _ (netlinkRecvmsg_front d p nodes front b tail sock empty room callback)
  intro q
  intro w ambient ⟨heq, hd, hs⟩
  subst q
  refine ⟨_, w, ambient, ?_, rfl, hd, hs⟩
  simp [socketFirstCall, List.forIn_cons, List.forIn_nil]
  rfl

theorem receiveDumpStep_last (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) (sock : NlSock) (empty : sock.queue = []) (messages : Array NlMessage) :
    Returns (receiveDumpStep 1 (messages, false))
      (fun w => w.dev = some d ∧ w.nlSock7 = socketLastState sock d p nodes ids)
      (fun q w => q = .yield (messages ++ (socketLastChunk d p nodes ids).messages.toArray, true) ∧
        w.dev = some d ∧ w.nlSock7 = socketReadbackFinal sock d) := by
  simp only [receiveDumpStep, Bool.false_eq_true, ite_false]
  apply returns_bind _ _ (netlinkRecvmsg_last d p nodes ids sock empty)
  intro q
  intro w ambient ⟨heq, hd, hs⟩
  subst q
  refine ⟨.yield (messages ++ (socketLastChunk d p nodes ids).messages.toArray, true),
    w, ambient, ?_, rfl, hd, hs⟩
  simp [socketLastChunk, socketLastCall, List.forIn_cons, List.forIn_nil]
  simp only [Array.push_eq_append, Array.append_assoc]
  rfl

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
  | done acc => simp
  | yield acc =>
    rw [show 4095 = 4094 + 1 from rfl, List.range'_succ]
    simp [List.forIn_cons, bind_assoc]
    congr 1
    funext second
    cases second <;> simp

theorem getterDrain_two (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId) (sock : NlSock)
    (empty : sock.queue = []) (endpoint : p.endpoint = none)
    (room : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (callback : Returns (wgGetDeviceDump
        { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
        d.deviceUpdateGen {}) (fun w => w.dev = some d)
      (fun q w => q = socketLastCall d p nodes (b :: tail) ∧ w.dev = some d)) :
    Returns getterDrainSource
      (fun w => w.dev = some d ∧ w.nlSock7 = socketFirstState sock d p nodes front b)
      (fun q w => q = .ok (suffixJson d p nodes (front ++ b :: tail)) ∧
        w.dev = some d ∧ w.nlSock7 = socketReadbackFinal sock d) := by
  intro entry ambient pre
  obtain ⟨first, middle, middleAmbient, runFirst, firstEq, hd, hs⟩ :=
    receiveDumpStep_front d p nodes front b tail sock empty room callback entry ambient pre
  subst first
  obtain ⟨second, final, finalAmbient, runSecond, secondEq, hdFinal, hsFinal⟩ :=
    receiveDumpStep_last d p nodes (b :: tail) sock empty
      (socketFirstCall d p nodes front b).skb.messages.toArray middle middleAmbient ⟨hd, hs⟩
  subst second
  refine ⟨.ok (suffixJson d p nodes (front ++ b :: tail)), final, finalAmbient, ?_, rfl, hdFinal, hsFinal⟩
  rw [getterDrain_two_source]
  change (((receiveDumpStep 0 (#[], false)).run entry).run ambient >>= _) = _
  rw [runFirst]
  change (((receiveDumpStep 1 ((socketFirstCall d p nodes front b).skb.messages.toArray, false)).run middle).run middleAmbient >>= _) = _
  rw [runSecond]
  dsimp only [bind, Except.bind]
  rw [receiveDump_finished]
  change ((coalesce (((socketFirstCall d p nodes front b).skb.messages.toArray ++
    (socketLastChunk d p nodes (b :: tail)).messages.toArray).toList)).run final).run finalAmbient = _
  simp only [Array.toList_append]
  rw [coalesce_socket_chunks d p nodes front (b :: tail) b endpoint]
  rfl

end Leanux.Proofs.WG.Config
