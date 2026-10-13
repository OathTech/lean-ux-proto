import Leanux.Proofs.WG.Queues.RxPollPrefix
import Leanux.Proofs.WG.Queues.GroCallback

set_option maxHeartbeats 2000000
set_option pp.structureInstances false

/-! The original poll with tagged GRO buffering and actual stack callback
entry observations. Tags are local removal ordinals and skb values, never
payload identities. Buffered events remain visible when the poll later stops. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

def dropGroPrefix (pid : PeerId) (occurrence : Nat) (id : SkbId) : PrefixM GroEvent Unit := do
  liftPrefix (dropRxQueue pid)
  emitPrefix (.removed occurrence id)

theorem dropGroPrefix_erases (pid : PeerId) (occurrence : Nat) (id : SkbId) :
    ErasesPrefix (dropGroPrefix pid occurrence id) (dropRxQueue pid) := by
  intro w h
  simp only [dropGroPrefix, runPrefix_bind, runPrefix_lift]
  cases (dropRxQueue pid).run w with
  | error e => rfl
  | ok out => cases out; rfl

def consumeGro (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (pkt : RxPacket) (endpoint : Endpoint) : PrefixM GroEvent (Option GroEntry) := do
  match ← liftPrefix (consumeDataDone pid pkt endpoint) with
  | none => return none
  | some bytes =>
    let entry : GroEntry := ⟨occurrence, id, bytes⟩
    emitPrefix (.buffered entry)
    return some entry

theorem consumeGro_erases (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (pkt : RxPacket) (endpoint : Endpoint) :
    ErasesTo (Option.map GroEntry.bytes) (consumeGro pid occurrence id pkt endpoint)
      (consumeDataDone pid pkt endpoint) := by
  intro w h
  simp only [consumeGro, runPrefix_bind, runPrefix_lift]
  cases (consumeDataDone pid pkt endpoint).run w with
  | error e => rfl
  | ok out =>
    rcases out with ⟨bytes, v⟩
    cases bytes <;> rfl

def pollProject (s : Nat × List GroEntry × Bool) : Nat × List (List UInt8) × Bool :=
  (s.1, s.2.1.map GroEntry.bytes, s.2.2)

def rxPollGro (pid : PeerId) (budget : Nat) : PrefixM GroEvent Nat := do
  if ← liftPrefix (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : List GroEntry := []
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let first ← liftPrefix (peekRxQueue pid)
    let go ← liftPrefix (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted))
    if !go then
      drained := true
      break
    let some id := first | liftPrefix (invariant "unreachable")
    let pkt ← liftPrefix (getRxSkb id)
    if pkt.peer != pid then liftPrefix (invariant "a packet on another peer's rx_queue")
    dropGroPrefix pid workDone id
    let mut free := true
    if !(← liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted))) then
      if !(← liftPrefix (branch .rxPollCounterInvalid !(← liftPrefix (counterValidate pkt.keypair pkt.nonce)))) then
        let endpoint ← liftPrefix (endpointFromSkb pkt.source)
        if !(← liftPrefix (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | liftPrefix (invariant "unreachable")
          gro := gro ++ (← consumeGro pid workDone id pkt e).toList
          free := false
    liftPrefix (keypairPut (some pkt.keypair) false)
    liftPrefix (peerPut (some pid))
    _ ← liftPrefix (branch .rxPollFree free)
    liftPrefix (freeRxSkb id)
    workDone := workDone + 1
    if ← liftPrefix (branch .rxPollBudgetDone (workDone ≥ budget)) then break
  if !drained && workDone < budget then liftPrefix (invariant "the rx_queue did not drain")
  if ← liftPrefix (branch .rxPollComplete (workDone < budget)) then
    liftPrefix (completeRxQueue pid)
    flushGro gro
  else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

theorem rxPollGro_erases (pid : PeerId) (budget : Nat) :
    ErasesPrefix (rxPollGro pid budget)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) := by
  rw [← rxPollGrouped_eq]
  apply ErasesTo.identity
  unfold rxPollGro rxPollGrouped
  apply erasesTo_bind id id (ErasesPrefix.to_projected (erasesPrefix_lift _))
  intro noBudget
  dsimp only [id]
  apply erasesTo_ite
  · intro hb
    exact erasesTo_pure id _
  · intro hb
    apply erasesTo_bind pollProject id
    · apply erasesTo_range pollProject
      intro n acc
      repeat' first
        | with_reducible exact ErasesPrefix.to_projected (erasesPrefix_lift _)
        | with_reducible exact ErasesPrefix.to_projected (dropGroPrefix_erases _ _ _)
        | with_reducible exact consumeGro_erases _ _ _ _ _
        | with_reducible apply erasesTo_bind (Option.map GroEntry.bytes)
        | with_reducible apply erasesTo_bind id
        | with_reducible apply erasesTo_ite
        | (with_reducible intro x; try dsimp only [id, pollProject])
        | (with_reducible split)
        | (simpa [pollProject, projectStep, List.map_append, Option.toList_map] using
            erasesTo_pure (projectStep pollProject) _)
      all_goals simp_all [ErasesTo, projectStep, pollProject, List.map_append, Option.toList_map, Except.map]
    · intro acc
      dsimp only [pollProject]
      repeat' first
        | with_reducible exact ErasesPrefix.to_projected (erasesPrefix_lift _)
        | with_reducible exact ErasesPrefix.to_projected (flushGro_erases _)
        | with_reducible exact erasesTo_pure id _
        | with_reducible apply erasesTo_bind id
        | with_reducible apply erasesTo_ite
        | (with_reducible intro x; try dsimp only [id])
        | (with_reducible split)
      all_goals simp_all [ErasesTo, Except.map]

end Leanux.Proofs.WG.Queues
