import Leanux.Proofs.Logged.ProjectsUnder
import Leanux.Proofs.WG.Queues.TxRingEntry
import Leanux.Proofs.WG.Lifetimes.TxWorker

/-! Joint observations of actual TX admission/publication and disposal cuts.
Access events retain the existing lifetime observer's full reached prefix.
Queue/publication events follow their real writes; completion entry precedes
its original call. A refusal is not itself a packet release. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes

inductive Event where
  | access (event : LifetimeEvent)
  | ring (event : TxRing.Event)
  | queued (pid : PeerId) (item : List SkbId)
  | published (pid : PeerId) (head : SkbId) (state : PacketState)
  | removed (pid : PeerId) (item : List SkbId)
  | completion (pid : PeerId) (item : List SkbId)

def accessEvent : Event → Option LifetimeEvent | .access e => some e | _ => none
def ringEvent : Event → Option TxRing.Event | .ring e => some e | _ => none
abbrev Obs := PrefixM Event

def access (a : MixedM α) : Obs α := focusPrefix Event.access accessEvent a

theorem access_erases (he : ErasesPrefix a original) : ErasesPrefix (access a) original :=
  focusPrefix_erases _ _ he

theorem access_projects (ha : PrefixPreserves AllocationInv LifetimeEvent.Safe a) :
    ProjectsUnder AllocationInv accessEvent (access a) a :=
  ha.projects_focus _ _ (fun _ => rfl)

theorem access_ring (he : ErasesPrefix a original) :
    ProjectsPrefix ringEvent id (access a) (liftPrefix original) :=
  projectsPrefix_focus_other _ _ _ (fun _ => rfl) he

theorem cut_erases (e : Event) : ErasesPrefix (emitPrefix e) (pure ()) := erasesPrefix_emit e

theorem emit_bind_erases (e : Event) (he : ErasesPrefix a original) :
    ErasesPrefix (do emitPrefix e; a) original := by
  simpa only [pure_bind] using erasesPrefix_bind (cut_erases e) (fun _ => he)

theorem bind_ite {m : Type → Type} [Monad m] (c : Prop) [Decidable c]
    (a b : m α) (f : α → m β) :
    (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

def enqueueCore (pid : PeerId) (item : List SkbId) : Obs Int := do
  let some first := item.head? | liftPrefix (invariant "an empty ring item")
  access (setTxSkbPrefix first fun p => {p with state := .uncrypted})
  let p ← access (getPeerMixed pid)
  if ← liftPrefix (branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS)) then return -WG.ENOSPC
  access (setPeerMixed pid {p with txQueue := p.txQueue.enqueue item})
  emitPrefix (.queued pid item)
  let d ← liftPrefix getDev
  let cpu ← liftPrefix (cpumaskNextOnlineFrom d.encryptLastCpu)
  liftPrefix (modifyDev fun d => {d with encryptLastCpu := cpu})
  if ← liftPrefix (branch .enqueueRingFull d.encryptQueue.full) then return -WG.EPIPE
  liftPrefix (queueDeviceWork .encryptWorker)
  liftPrefix (modifyDev fun d => {d with encryptQueue := d.encryptQueue.produce item})
  return 0

def enqueue (pid : PeerId) (item : List SkbId) : Obs Int := do
  let ret ← enqueueCore pid item
  if ret = 0 then emitPrefix (.ring (.offered item true))
  else if ret = -WG.EPIPE then emitPrefix (.ring (.offered item false))
  return ret

def publish (item : List SkbId) (state : PacketState) : Obs Unit := do
  let some first := item.head? | liftPrefix (invariant "an empty ring item")
  let pid := (← access (getKeypairPrefix (← access (getTxSkbPrefix first)).keypair)).peer
  access (peerGetMixed pid)
  if !((← access (getPeerMixed pid)).txQueue.all.any (·.head? == some first)) then
    liftPrefix (invariant "an item for the tx worker that is not on its peer's tx_queue")
  access (setTxSkbPrefix first fun p => {p with state})
  emitPrefix (.published pid first state)
  _ ← access (cpumaskChooseOnlinePrefix pid)
  if !(← liftPrefix getDev).txWorkQueue.contains pid || (← liftPrefix (peekQueuedUnit .txWorker pid)) then
    liftPrefix (recordQueued .txWorker pid)
    liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
  access (peerPutMixed (some pid))

def create (pid : PeerId) (item : List SkbId) : Obs Unit := do
  let some first := item.head? | liftPrefix (invariant "an empty ring item")
  let ret ← do
    if ← liftPrefix (branch .createDataDead (← access (getPeerMixed pid)).isDead) then pure (-EINVAL)
    else
      let ret ← enqueue pid item
      if ← liftPrefix (branch .createDataEpipe (ret == -WG.EPIPE)) then publish item .dead
      pure ret
  if ← liftPrefix (branch .createDataOk (ret == 0)) then return
  if ← liftPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
  access (keypairPutPrefix (some (← access (getTxSkbPrefix first)).keypair) false)
  access (peerPutMixed (some pid))
  for id in item do access (freeTxSkbPrefix id)

def drop (pid : PeerId) (item : List SkbId) : Obs Unit := do
  access (setPeerMixed pid {(← access (getPeerMixed pid)) with
    txQueue := (← access (getPeerMixed pid)).txQueue.dropPeeked})
  emitPrefix (.removed pid item)

def complete (pid : PeerId) (item : List SkbId) : Obs Unit := do
  emitPrefix (.completion pid item)
  access (createDataDonePrefix pid item)

def andObs (a b : Obs Bool) : Obs Bool := do if ← a then b else pure false

def dispose (pid : PeerId) (item : List SkbId) (key : KeypairId) : Obs Bool := do
  for id in item do access (freeTxSkbPrefix id)
  access (keypairPutPrefix (some key) false)
  access (peerPutMixed (some pid))
  return true

def disposeSource (pid : PeerId) (item : List SkbId) (key : KeypairId) : M Bool := do
  for id in item do freeTxSkb id
  keypairPut (some key) false
  peerPut (some pid)
  return true

def body (pid : PeerId) (first : Option (List SkbId)) : Obs Bool := do
  let go ← andObs (liftPrefix (branch .txPacket first.isSome)) do
    let some f := first | liftPrefix (invariant "unreachable")
    let some h := f.head? | liftPrefix (invariant "an empty ring item")
    liftPrefix (branch .txNotUncrypted ((← access (getTxSkbPrefix h)).state != .uncrypted))
  if !go then return false
  let some item := first | liftPrefix (invariant "unreachable")
  let some headId := item.head? | liftPrefix (invariant "an empty ring item")
  let head ← access (getTxSkbPrefix headId)
  drop pid item
  if ← liftPrefix (branch .txCrypted (head.state == .crypted)) then complete pid item
  dispose pid item head.keypair

def bodySource (pid : PeerId) (first : Option (List SkbId)) : M Bool := do
  let go ← WG.andM (branch .txPacket first.isSome) do
    let some f := first | invariant "unreachable"
    let some h := f.head? | invariant "an empty ring item"
    branch .txNotUncrypted ((← getTxSkb h).state != .uncrypted)
  if !go then return false
  let some item := first | invariant "unreachable"
  let some headId := item.head? | invariant "an empty ring item"
  let head ← getTxSkb headId
  (do setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked})
  if ← branch .txCrypted (head.state == .crypted) then createDataDone pid item
  disposeSource pid item head.keypair

def step (pid : PeerId) : Obs Bool := do
  let (first, q) ← liftPrefix ((← access (getPeerMixed pid)).txQueue.peek)
  access (modifyPeerKeysPrefix pid fun p => {p with txQueue := q})
  body pid first

def stepSource (pid : PeerId) : M Bool := do
  let (first, q) ← (← getPeer pid).txQueue.peek
  (do setPeer pid {(← getPeer pid) with txQueue := q})
  bodySource pid first

theorem stepSource_eq (pid : PeerId) : stepSource pid = txStep pid := by
  simp only [stepSource, bodySource, disposeSource, txStep, bind_assoc]
  rfl

-- All-input erasure is independent of the conditional lifetime projection.
theorem enqueueCore_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (enqueueCore pid item) (enqueuePerDeviceAndPeer pid item) := by
  unfold enqueueCore enqueuePerDeviceAndPeer
  cases hh : item.head? <;> simp only [hh]
  repeat' first
    | with_reducible exact access_erases (setTxSkbPrefix_erases _ _)
    | with_reducible exact access_erases (getPeerMixed_erases _)
    | with_reducible exact access_erases (setPeerMixed_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply emit_bind_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)
  all_goals try simp_all

theorem enqueue_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (enqueue pid item) (enqueuePerDeviceAndPeer pid item) := by
  have ht (ret : Int) : ErasesPrefix
      (do if ret = 0 then emitPrefix (.ring (.offered item true))
          else if ret = -WG.EPIPE then emitPrefix (.ring (.offered item false))
          pure ret : Obs Int) (pure ret) := by
    intro w h
    split <;> try split
    all_goals rfl
  simpa only [enqueue, bind_pure] using erasesPrefix_bind (enqueueCore_erases pid item) ht

theorem publish_erases (item : List SkbId) (state : PacketState) :
    ErasesPrefix (publish item state) (enqueuePerPeerTx item state) := by
  unfold publish enqueuePerPeerTx
  cases hh : item.head? <;> simp only [hh]
  repeat' first
    | with_reducible exact access_erases (getTxSkbPrefix_erases _)
    | with_reducible exact access_erases (getKeypairPrefix_erases _)
    | with_reducible exact access_erases (peerGetMixed_erases _)
    | with_reducible exact access_erases (getPeerMixed_erases _)
    | with_reducible exact access_erases (setTxSkbPrefix_erases _ _)
    | with_reducible exact access_erases (cpumaskChooseOnlinePrefix_erases _)
    | with_reducible exact access_erases (peerPutMixed_erases _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply emit_bind_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)
  all_goals try simp_all

theorem create_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (create pid item) (createData pid item) := by
  unfold create createData
  cases hh : item.head? <;> simp only [hh]
  repeat' first
    | with_reducible exact enqueue_erases _ _
    | with_reducible exact publish_erases _ _
    | with_reducible exact access_erases (getPeerMixed_erases _)
    | with_reducible exact access_erases (getTxSkbPrefix_erases _)
    | with_reducible exact access_erases (keypairPutPrefix_erases _ _)
    | with_reducible exact access_erases (peerPutMixed_erases _)
    | with_reducible exact access_erases (freeTxSkbPrefix_erases _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply emit_bind_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)
  all_goals try simp_all

theorem drop_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (drop pid item)
      (do setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}) := by
  unfold drop
  apply erasesPrefix_bind (access_erases (getPeerMixed_erases pid))
  intro p
  apply erasesPrefix_bind (access_erases (getPeerMixed_erases pid))
  intro q
  have he := erasesPrefix_bind (access_erases (setPeerMixed_erases pid {p with txQueue := q.txQueue.dropPeeked}))
    (fun _ => cut_erases (.removed pid item))
  simpa only [bind_pure_unit, bind_pure] using he

theorem complete_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (complete pid item) (createDataDone pid item) :=
  emit_bind_erases _ (access_erases (createDataDonePrefix_erases pid item))

theorem andObs_erases (ha : ErasesPrefix a originalA) (hb : ErasesPrefix b originalB) :
    ErasesPrefix (andObs a b) (WG.andM originalA originalB) := by
  apply erasesPrefix_bind ha
  intro x
  cases x <;> first | exact hb | exact erasesPrefix_pure false

theorem dispose_erases (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ErasesPrefix (dispose pid item key) (disposeSource pid item key) := by
  unfold dispose disposeSource
  apply erasesPrefix_bind (erasesPrefix_forIn item () _ _ (fun id _ =>
    erasesPrefix_bind (access_erases (freeTxSkbPrefix_erases id))
      (fun _ => erasesPrefix_pure (.yield ()))))
  intro _
  apply erasesPrefix_bind (access_erases (keypairPutPrefix_erases _ _))
  intro _
  exact erasesPrefix_bind (access_erases (peerPutMixed_erases _)) (fun _ => erasesPrefix_pure true)

theorem body_erases (pid : PeerId) (first : Option (List SkbId)) :
    ErasesPrefix (body pid first) (bodySource pid first) := by
  unfold body bodySource
  apply erasesPrefix_bind
    (andObs_erases (erasesPrefix_lift _) (by
      cases first with
      | none => exact erasesPrefix_lift _
      | some item =>
        cases hh : item.head? with
        | none => simpa only [hh] using (erasesPrefix_lift (invariant "an empty ring item") : ErasesPrefix (liftPrefix (invariant "an empty ring item") : Obs Bool) _)
        | some id =>
          simp only [hh]
          exact erasesPrefix_bind (access_erases (getTxSkbPrefix_erases id)) (fun _ => erasesPrefix_lift _)))
  intro go
  cases go with
  | false => exact erasesPrefix_pure false
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases first with
    | none => exact erasesPrefix_lift _
    | some item =>
      cases hh : item.head? with
      | none => simpa only [hh] using (erasesPrefix_lift (invariant "an empty ring item") : ErasesPrefix (liftPrefix (invariant "an empty ring item") : Obs Bool) _)
      | some id =>
        simp only [hh]
        apply erasesPrefix_bind (access_erases (getTxSkbPrefix_erases id))
        intro head
        apply erasesPrefix_bind (drop_erases pid item)
        intro _
        apply erasesPrefix_bind (erasesPrefix_lift _)
        intro crypted
        cases crypted with
        | false => exact dispose_erases pid item head.keypair
        | true => exact erasesPrefix_bind (complete_erases pid item) (fun _ => dispose_erases pid item head.keypair)

theorem step_erases (pid : PeerId) : ErasesPrefix (step pid) (txStep pid) := by
  rw [← stepSource_eq]
  unfold step stepSource
  apply erasesPrefix_bind (access_erases (getPeerMixed_erases pid))
  intro p
  apply erasesPrefix_bind (erasesPrefix_lift _)
  rintro ⟨first, q⟩
  exact erasesPrefix_bind (access_erases (modifyPeerKeysPrefix_erases pid _)) (fun _ => body_erases pid first)

end Leanux.Proofs.WG.Queues.TxDisposition
