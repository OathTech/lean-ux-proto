import MirrorLoop

namespace Binary.PeerMirror
open Leanux Leanux.WG
open LookupMirror (record)

private theorem throw_run (e : Stop) (w : World) :
    (throw e : M α).run w = .error e := rfl

def recordCmp (w : World) (d : Decision) (outcome : Bool) (a b : Int) : World :=
  {w with steps := w.steps.push {decision := d, outcome, operands := some (a, b), netRx := w.netRxSection}}

def countRecords (w : World) (old : Nat) : World :=
  let w := recordCmp w .refcountAddNzZero (old == 0) old 0
  let w := if old == 0 then w else record w .refcountAddNzRetry false
  record (record w .refcountAddNzNegative false) .refcountAddNzWraps false

theorem count_run (old : Nat) (w : World) (small : old + 1 < 2^31) :
    (refcountIncNotZero old).run w = .ok (old != 0, countRecords w old) := by
  have noWrap : ¬old + 1 ≥ 2^31 := by omega
  by_cases zero : old = 0 <;>
    simp [refcountIncNotZero, branchCmp, branch, countRecords, recordCmp, record, zero, noWrap] <;> rfl

/-- Saturation is ruled out by accepted mirror execution, not by hiding
    those states in an entry precondition or trusting a warning callee. -/
theorem accepted_count_bound (old : Nat) (w w' : World) (answer : Bool)
    (accepted : (refcountIncNotZero old).run w = .ok (answer, w')) : old + 1 < 2^31 := by
  by_cases h : old + 1 < 2^31
  · exact h
  have wraps : old + 1 ≥ 2^31 := by omega
  have zero : old ≠ 0 := by omega
  simp [refcountIncNotZero, branchCmp, branch, unsupported, zero, wraps, throw_run] at accepted
  cases accepted

theorem count_zero (w : World) :
    (refcountIncNotZero 0).run w = .ok (false, countRecords w 0) :=
  count_run 0 w (by decide)

/-- Accepted peer-get supplies the arithmetic bound used by the binary
    helper proof. It is not a separate restriction on dead-peer entries. -/
theorem accepted_peer_bound (pid : PeerId) (w w' : World) (answer : Option PeerId)
    (device : Device) (peer : Peer)
    (hasDevice : w.k.wg = some device) (hasPeer : device.peers.get? pid = some peer)
    (accepted : (peerGetMaybeZero (some pid)).run w = .ok (answer, w')) :
    peer.refcount + 1 < 2^31 := by
  by_cases small : peer.refcount + 1 < 2^31
  · exact small
  have wraps : peer.refcount + 1 ≥ 2^31 := by omega
  have nonzero : peer.refcount ≠ 0 := by omega
  have peerRead : device.peers[pid]? = some peer := hasPeer
  have wraps' : 2147483647 ≤ peer.refcount := by omega
  simp [peerGetMaybeZero, branch, requireNotPending, getPeer, getDev, getK,
    hasDevice, peerRead, refcountIncNotZero, branchCmp, unsupported, nonzero, wraps', throw_run]
    at accepted
  cases accepted

/-- Exact source postworld, including its decision history. Only the
    successful branch changes the peer's count; null/dead do not change k. -/
def peerFinal (pid : PeerId) (w : World) (peer : Peer) : World :=
  let logged := record (countRecords (record w .peerGetMaybeZeroNull false) peer.refcount)
    .peerGetMaybeZeroDead (peer.refcount == 0)
  if peer.refcount = 0 then logged
  else {logged with k := {logged.k with wg := logged.k.wg.map fun device =>
    {device with peers := device.peers.insert pid {peer with refcount := peer.refcount+1}}}}

theorem peer_null_run (w : World) :
    (peerGetMaybeZero none).run w = .ok (none, record w .peerGetMaybeZeroNull true) := rfl

theorem peer_run (pid : PeerId) (w : World) (device : Device) (peer : Peer)
    (hasDevice : w.k.wg = some device) (hasPeer : device.peers.get? pid = some peer)
    (small : peer.refcount+1 < 2^31) :
    (peerGetMaybeZero (some pid)).run w =
      .ok ((if peer.refcount = 0 then none else some pid), peerFinal pid w peer) := by
  have peerRead : device.peers[pid]? = some peer := hasPeer
  have noWrap : ¬2147483647 ≤ peer.refcount := by omega
  by_cases zero : peer.refcount = 0
  all_goals have boolZero : (peer.refcount == 0) = decide (peer.refcount = 0) := rfl
  all_goals simp only [zero, decide_true, decide_false] at boolZero
  all_goals
    simp [peerGetMaybeZero, branch, requireNotPending, getPeer, getDev, getK,
      hasDevice, peerRead, refcountIncNotZero, branchCmp, zero, noWrap,
      setPeer, modifyDev, modifyK, peerFinal, countRecords, recordCmp, record, bne, boolZero] <;> rfl

theorem accepted_peer_result (pid : PeerId) (w w' : World) (answer : Option PeerId)
    (device : Device) (peer : Peer)
    (hasDevice : w.k.wg = some device) (hasPeer : device.peers.get? pid = some peer)
    (accepted : (peerGetMaybeZero (some pid)).run w = .ok (answer, w')) :
    answer = (if peer.refcount = 0 then none else some pid) ∧ w' = peerFinal pid w peer := by
  have small := accepted_peer_bound pid w w' answer device peer hasDevice hasPeer accepted
  rw [peer_run pid w device peer hasDevice hasPeer small] at accepted
  exact Prod.mk.inj (Except.ok.inj accepted.symm)

#print axioms count_run
#print axioms accepted_count_bound
#print axioms count_zero
#print axioms accepted_peer_bound
#print axioms peer_null_run
#print axioms peer_run
#print axioms accepted_peer_result
end Binary.PeerMirror
