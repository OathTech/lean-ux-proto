import Leanux.Proofs.WG.Queues.RxPollPrefix
import Leanux.Proofs.WG.Queues.GroCallback
import Leanux.Proofs.WG.Queues.GroState

set_option maxHeartbeats 2000000
set_option pp.structureInstances false

/-! The original poll with tagged completion offers, actual normal/held GRO
state, and stack callback entry observations. Tags use local workDone and skb
values, never payload identities. The buffered event precedes GRO admission
and remains visible if that admission or a later operation stops. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

def dropGroPrefix (pid : PeerId) (occurrence : Nat) (id : SkbId) : PrefixM GroEvent Unit := do
  liftPrefix (liftWG (dropRxQueue pid))
  emitPrefix (.removed occurrence id)

theorem dropGroPrefix_erases (pid : PeerId) (occurrence : Nat) (id : SkbId) :
    ErasesPrefix (dropGroPrefix pid occurrence id) (liftWG (dropRxQueue pid)) := by
  intro w h
  simp only [dropGroPrefix, runPrefix_bind, runPrefix_lift]
  cases (liftWG (dropRxQueue pid)).run w with
  | error e => rfl
  | ok out => cases out; rfl

def consumeGro (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (pkt : RxPacket) (endpoint : Endpoint) : PrefixM GroEvent (Option GroEntry) := do
  match ← liftPrefix (liftWG (consumeDataDone pid pkt endpoint)) with
  | none => return none
  | some bytes =>
    let entry : GroEntry := ⟨occurrence, id, bytes⟩
    emitPrefix (.buffered entry)
    return some entry

theorem consumeGro_erases (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (pkt : RxPacket) (endpoint : Endpoint) :
    ErasesTo (Option.map GroEntry.bytes) (consumeGro pid occurrence id pkt endpoint)
      (liftWG (consumeDataDone pid pkt endpoint)) := by
  intro w h
  simp only [consumeGro, runPrefix_bind, runPrefix_lift]
  cases (liftWG (consumeDataDone pid pkt endpoint)).run w with
  | error e => rfl
  | ok out =>
    rcases out with ⟨bytes, v⟩
    cases bytes <;> rfl

def pollProject (s : Nat × TaggedGro × Bool) : Nat × GroState × Bool :=
  (s.1, s.2.1.erase, s.2.2)

theorem groOption_erases (g : TaggedGro) (out : Option GroEntry) :
    ErasesTo TaggedGro.erase (out.elim (pure g) (napiGroReceiveTagged g))
      ((out.toList.map GroEntry.bytes).foldlM
        (fun g bytes => napiGroReceive (fun bs => bs.forM Leanux.Env.deliverInner) g bytes) g.erase) := by
  cases out with
  | none => exact erasesTo_pure TaggedGro.erase g
  | some e => simpa using napiGroReceiveTagged_erases g e

def rxPollGro (pid : PeerId) (budget : Nat) : PrefixM GroEvent Nat := do
  if ← liftPrefix (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : TaggedGro := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let first ← liftPrefix (liftWG (peekRxQueue pid))
    let go ← liftPrefix (liftWG (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)))
    if !go then
      drained := true
      break
    let some id := first | liftPrefix (invariant "unreachable")
    let pkt ← liftPrefix (liftWG (getRxSkb id))
    if pkt.peer != pid then liftPrefix (invariant "a packet on another peer's rx_queue")
    dropGroPrefix pid workDone id
    let mut free := true
    if !(← liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted))) then
      if !(← liftPrefix (branch .rxPollCounterInvalid !(← liftPrefix (liftWG (counterValidate pkt.keypair pkt.nonce))))) then
        let endpoint ← liftPrefix (liftWG (endpointFromSkb pkt.source))
        if !(← liftPrefix (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | liftPrefix (invariant "unreachable")
          for entry in (← consumeGro pid workDone id pkt e).toList do
            gro ← napiGroReceiveTagged gro entry
          free := false
    liftPrefix (liftWG (keypairPut (some pkt.keypair) false))
    liftPrefix (liftWG (peerPut (some pid)))
    _ ← liftPrefix (branch .rxPollFree free)
    liftPrefix (liftWG (freeRxSkb id))
    workDone := workDone + 1
    if ← liftPrefix (branch .rxPollBudgetDone (workDone ≥ budget)) then break
  if !drained && workDone < budget then liftPrefix (invariant "the rx_queue did not drain")
  if ← liftPrefix (branch .rxPollComplete (workDone < budget)) then
    liftPrefix (liftWG (completeRxQueue pid))
    napiGroFlushAllTagged gro
  else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

theorem rxPollGro_erases (pid : PeerId) (budget : Nat) :
    ErasesPrefix (rxPollGro pid budget)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) := by
  rw [← rxPollGrouped_eq]
  apply ErasesTo.identity
  unfold rxPollGro rxPollGrouped
  have hl {α : Type} (a : WG.M α) : (liftM a : Leanux.M α) = liftWG a := rfl
  simp only [hl]
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
        | with_reducible exact napiGroReceiveTagged_erases _ _
        | with_reducible exact groOption_erases _ _
        | with_reducible apply erasesTo_forIn_map TaggedGro.erase GroEntry.bytes
        | with_reducible apply erasesTo_bind TaggedGro.erase
        | with_reducible apply erasesTo_bind (Option.map GroEntry.bytes)
        | with_reducible apply erasesTo_bind id
        | with_reducible apply erasesTo_ite
        | (with_reducible intro x; try dsimp only [id, pollProject]; try simp only [Option.toList_map])
        | (with_reducible split)
        | (simpa [pollProject, projectStep, List.map_append, Option.toList_map] using
            erasesTo_pure (projectStep pollProject) _)
        | with_reducible exact erasesTo_pure (projectStep TaggedGro.erase) _
      all_goals simp_all [ErasesTo, Option.toList_map, Except.map]
      all_goals exact groOption_erases _ _
    · intro acc
      dsimp only [pollProject]
      repeat' first
        | with_reducible exact ErasesPrefix.to_projected (erasesPrefix_lift _)
        | with_reducible exact ErasesPrefix.to_projected (napiGroFlushAllTagged_erases _)
        | with_reducible exact erasesTo_pure id _
        | with_reducible apply erasesTo_bind id
        | with_reducible apply erasesTo_ite
        | (with_reducible intro x; try dsimp only [id])
        | (with_reducible split)
      all_goals simp_all [ErasesTo, Except.map]

end Leanux.Proofs.WG.Queues
