import Leanux.Proofs.Logged.ProjectsUnder
import Leanux.Proofs.WG.Queues.TxRingEntry
import Leanux.Proofs.WG.Lifetimes.TxCompletion

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

def access {S : Type} (a : PrefixT LifetimeEvent S α) : PrefixT Event S α :=
  focusPrefix Event.access accessEvent a

def nativeAccess (a : MixedM α) : Obs α := access (liftWGObserver a)

theorem access_erases {S α : Type} {a : PrefixT LifetimeEvent S α} {original : StateT S (Except Stop) α}
    (he : ErasesPrefix a original) : ErasesPrefix (access a) original :=
  focusPrefix_erases _ _ he

theorem access_projects {S : Type} {I : List LifetimeEvent → S → Prop}
    {a : PrefixT LifetimeEvent S α} (ha : PrefixPreserves I LifetimeEvent.Safe a) :
    ProjectsUnder I accessEvent (access a) a :=
  ha.projects_focus _ _ (fun _ => rfl)

theorem access_ring {S α : Type} {a : PrefixT LifetimeEvent S α} {original : StateT S (Except Stop) α}
    (he : ErasesPrefix a original) :
    ProjectsPrefix ringEvent id (access a) (liftPrefix original) :=
  projectsPrefix_focus_other _ _ _ (fun _ => rfl) he

theorem cut_erases {S : Type} (e : Event) : ErasesPrefix (emitPrefix e : PrefixT Event S Unit) (pure ()) := erasesPrefix_emit e

theorem emit_bind_erases {S α : Type} {a : PrefixT Event S α} {original : StateT S (Except Stop) α}
    (e : Event) (he : ErasesPrefix a original) :
    ErasesPrefix (do emitPrefix e; a) original := by
  simpa only [pure_bind] using erasesPrefix_bind (cut_erases e) (fun _ => he)

theorem bind_ite {m : Type → Type} [Monad m] (c : Prop) [Decidable c]
    (a b : m α) (f : α → m β) :
    (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

/-- A concrete native observer enters the actual product state once. -/
theorem nativeAccess_erases (he : ErasesStatePrefix a original) :
    ErasesPrefix (nativeAccess a) (liftWG original) :=
  access_erases (liftWGObserver_erases he)

/-- The real WG adapter commutes with a finite list traversal. -/
theorem liftWG_forIn (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β)) :
    liftWG (forIn xs init f) = forIn xs init (fun x b => liftWG (f x b)) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, liftWG_bind]
    congr 1
    funext result
    cases result <;> simp only [liftWG_pure, ih]

def enqueueCore (pid : PeerId) (item : List SkbId) : Obs Int := do
  let some first := item.head? | liftPrefix (liftWG (invariant "an empty ring item"))
  nativeAccess (setTxSkbPrefix first fun p => {p with state := .uncrypted})
  let p ← nativeAccess (getPeerMixed pid)
  if ← liftPrefix (liftWG (branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS))) then return -WG.ENOSPC
  nativeAccess (setPeerMixed pid {p with txQueue := p.txQueue.enqueue item})
  emitPrefix (.queued pid item)
  let d ← liftPrefix (liftWG getDev)
  let cpu ← liftPrefix (liftWG (cpumaskNextOnlineFrom d.encryptLastCpu))
  liftPrefix (liftWG (modifyDev fun d => {d with encryptLastCpu := cpu}))
  if ← liftPrefix (liftWG (branch .enqueueRingFull d.encryptQueue.full)) then return -WG.EPIPE
  liftPrefix (liftWG (queueDeviceWork .encryptWorker))
  liftPrefix (liftWG (modifyDev fun d => {d with encryptQueue := d.encryptQueue.produce item}))
  return 0

def enqueue (pid : PeerId) (item : List SkbId) : Obs Int := do
  let ret ← enqueueCore pid item
  if ret = 0 then emitPrefix (.ring (.offered item true))
  else if ret = -WG.EPIPE then emitPrefix (.ring (.offered item false))
  return ret

def publish (item : List SkbId) (state : PacketState) : Obs Unit := do
  let some first := item.head? | liftPrefix (liftWG (invariant "an empty ring item"))
  let pid ← nativeAccess (peerDerefPrefix (.keypair (← nativeAccess (getTxSkbPrefix first)).keypair))
  nativeAccess (peerGetMixed pid)
  if !((← nativeAccess (getPeerMixed pid)).txQueue.all.any (·.head? == some first)) then
    liftPrefix (liftWG (invariant "an item for the tx worker that is not on its peer's tx_queue"))
  nativeAccess (setTxSkbPrefix first fun p => {p with state})
  emitPrefix (.published pid first state)
  _ ← nativeAccess (cpumaskChooseOnlinePrefix pid)
  if !(← liftPrefix (liftWG getDev)).txWorkQueue.contains pid || (← liftPrefix (liftWG (peekQueuedUnit .txWorker pid))) then
    liftPrefix (liftWG (recordQueued .txWorker pid))
    liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}))
  nativeAccess (peerPutMixed (some pid))

def create (pid : PeerId) (item : List SkbId) : Obs Unit := do
  let some first := item.head? | liftPrefix (liftWG (invariant "an empty ring item"))
  let ret ← do
    if ← liftPrefix (liftWG (branch .createDataDead (← nativeAccess (getPeerMixed pid)).isDead)) then pure (-EINVAL)
    else
      let ret ← enqueue pid item
      if ← liftPrefix (liftWG (branch .createDataEpipe (ret == -WG.EPIPE))) then publish item .dead
      pure ret
  if ← liftPrefix (liftWG (branch .createDataOk (ret == 0))) then return
  if ← liftPrefix (liftWG (branch .createDataOkEpipe (ret == -WG.EPIPE))) then return
  nativeAccess (keypairPutPrefix (some (← nativeAccess (getTxSkbPrefix first)).keypair) false)
  nativeAccess (peerPutMixed (some pid))
  for id in item do nativeAccess (freeTxSkbPrefix id)

def drop (pid : PeerId) (item : List SkbId) : Obs Unit := do
  nativeAccess (setPeerMixed pid {(← nativeAccess (getPeerMixed pid)) with
    txQueue := (← nativeAccess (getPeerMixed pid)).txQueue.dropPeeked})
  emitPrefix (.removed pid item)

def complete (pid : PeerId) (item : List SkbId) : Obs Unit := do
  emitPrefix (.completion pid item)
  nativeAccess (createDataDonePrefix pid item)

def andObs {m : Type → Type} [Monad m] (a b : m Bool) : m Bool := do if ← a then b else pure false

def dispose (pid : PeerId) (item : List SkbId) (key : KeypairId) : Obs Bool := do
  for id in item do nativeAccess (freeTxSkbPrefix id)
  nativeAccess (keypairPutPrefix (some key) false)
  nativeAccess (peerPutMixed (some pid))
  return true

def disposeSource (pid : PeerId) (item : List SkbId) (key : KeypairId) : WG.M Bool := do
  for id in item do freeTxSkb id
  keypairPut (some key) false
  peerPut (some pid)
  return true

def body (pid : PeerId) (first : Option (List SkbId)) : Obs Bool := do
  let go ← andObs (liftPrefix (liftWG (branch .txPacket first.isSome))) do
    let some f := first | liftPrefix (liftWG (invariant "unreachable"))
    let some h := f.head? | liftPrefix (liftWG (invariant "an empty ring item"))
    liftPrefix (liftWG (branch .txNotUncrypted ((← nativeAccess (getTxSkbPrefix h)).state != .uncrypted)))
  if !go then return false
  let some item := first | liftPrefix (liftWG (invariant "unreachable"))
  let some headId := item.head? | liftPrefix (liftWG (invariant "an empty ring item"))
  let head ← nativeAccess (getTxSkbPrefix headId)
  drop pid item
  if ← liftPrefix (liftWG (branch .txCrypted (head.state == .crypted))) then complete pid item
  dispose pid item head.keypair

def bodySource (pid : PeerId) (first : Option (List SkbId)) : WG.M Bool := do
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
  let (first, q) ← liftPrefix (liftWG ((← nativeAccess (getPeerMixed pid)).txQueue.peek))
  nativeAccess (modifyPeerKeysPrefix pid fun p => {p with txQueue := q})
  body pid first

def stepSource (pid : PeerId) : WG.M Bool := do
  let (first, q) ← (← getPeer pid).txQueue.peek
  (do setPeer pid {(← getPeer pid) with txQueue := q})
  bodySource pid first

theorem stepSource_eq (pid : PeerId) : stepSource pid = txStep pid := by
  simp only [stepSource, bodySource, disposeSource, txStep, bind_assoc]
  rfl

-- All-input erasure is independent of the conditional lifetime projection.
theorem enqueueCore_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (enqueueCore pid item) (liftWG (enqueuePerDeviceAndPeer pid item)) := by
  unfold enqueueCore enqueuePerDeviceAndPeer
  cases hh : item.head? <;> simp only [hh, liftWG_bind, liftWG_pure, liftWG_forIn, apply_ite]
  repeat' first
    | with_reducible exact nativeAccess_erases (setTxSkbPrefix_erases _ _)
    | with_reducible exact nativeAccess_erases (getPeerMixed_erases _)
    | with_reducible exact nativeAccess_erases (setPeerMixed_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply emit_bind_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)
  all_goals try simp_all

theorem enqueue_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (enqueue pid item) (liftWG (enqueuePerDeviceAndPeer pid item)) := by
  have ht (ret : Int) : ErasesPrefix
      (do if ret = 0 then emitPrefix (.ring (.offered item true))
          else if ret = -WG.EPIPE then emitPrefix (.ring (.offered item false))
          pure ret : Obs Int) (pure ret) := by
    intro w h
    split <;> try split
    all_goals rfl
  simpa only [enqueue, bind_pure] using erasesPrefix_bind (enqueueCore_erases pid item) ht

theorem publish_erases (item : List SkbId) (state : PacketState) :
    ErasesPrefix (publish item state) (liftWG (enqueuePerPeerTx item state)) := by
  unfold publish enqueuePerPeerTx
  cases hh : item.head? <;> simp only [hh, liftWG_bind, liftWG_pure, liftWG_forIn, apply_ite]
  repeat' first
    | with_reducible exact nativeAccess_erases (getTxSkbPrefix_erases _)
    | with_reducible exact nativeAccess_erases (peerDerefPrefix_erases _)
    | with_reducible exact nativeAccess_erases (peerGetMixed_erases _)
    | with_reducible exact nativeAccess_erases (getPeerMixed_erases _)
    | with_reducible exact nativeAccess_erases (setTxSkbPrefix_erases _ _)
    | with_reducible exact nativeAccess_erases (cpumaskChooseOnlinePrefix_erases _)
    | with_reducible exact nativeAccess_erases (peerPutMixed_erases _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply emit_bind_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)
  all_goals try simp_all

theorem create_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (create pid item) (liftWG (createData pid item)) := by
  unfold create createData
  cases hh : item.head? <;> simp only [hh, liftWG_bind, liftWG_pure, liftWG_forIn, apply_ite]
  repeat' first
    | with_reducible exact enqueue_erases _ _
    | with_reducible exact publish_erases _ _
    | with_reducible exact nativeAccess_erases (getPeerMixed_erases _)
    | with_reducible exact nativeAccess_erases (getTxSkbPrefix_erases _)
    | with_reducible exact nativeAccess_erases (keypairPutPrefix_erases _ _)
    | with_reducible exact nativeAccess_erases (peerPutMixed_erases _)
    | with_reducible exact nativeAccess_erases (freeTxSkbPrefix_erases _)
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
      (liftWG (do setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked})) := by
  unfold drop
  simp only [liftWG_bind, liftWG_pure]
  apply erasesPrefix_bind (nativeAccess_erases (getPeerMixed_erases pid))
  intro p
  apply erasesPrefix_bind (nativeAccess_erases (getPeerMixed_erases pid))
  intro q
  have he := erasesPrefix_bind (nativeAccess_erases (setPeerMixed_erases pid {p with txQueue := q.txQueue.dropPeeked}))
    (fun _ => cut_erases (.removed pid item))
  simpa only [bind_pure_unit, bind_pure] using he

theorem complete_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (complete pid item) (liftWG (createDataDone pid item)) :=
  emit_bind_erases _ (nativeAccess_erases (createDataDonePrefix_erases pid item))

theorem andObs_erases {S : Type} {a b : PrefixT Event S Bool}
    {originalA originalB : StateT S (Except Stop) Bool} (ha : ErasesPrefix a originalA) (hb : ErasesPrefix b originalB) :
    ErasesPrefix (andObs a b) (andObs originalA originalB) := by
  apply erasesPrefix_bind ha
  intro x
  cases x <;> first | exact hb | exact erasesPrefix_pure false

theorem dispose_erases (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ErasesPrefix (dispose pid item key) (liftWG (disposeSource pid item key)) := by
  unfold dispose disposeSource
  simp only [liftWG_bind, liftWG_pure, liftWG_forIn]
  apply erasesPrefix_bind (erasesPrefix_forIn item () _ _ (fun id _ =>
    erasesPrefix_bind (nativeAccess_erases (freeTxSkbPrefix_erases id))
      (fun _ => erasesPrefix_pure (.yield ()))))
  intro _
  apply erasesPrefix_bind (nativeAccess_erases (keypairPutPrefix_erases _ _))
  intro _
  exact erasesPrefix_bind (nativeAccess_erases (peerPutMixed_erases _)) (fun _ => erasesPrefix_pure true)

theorem body_erases (pid : PeerId) (first : Option (List SkbId)) :
    ErasesPrefix (body pid first) (liftWG (bodySource pid first)) := by
  unfold body bodySource
  simp only [WG.andM, liftWG_bind, liftWG_pure, apply_ite]
  apply erasesPrefix_bind
    (andObs_erases (erasesPrefix_lift _) (by
      cases first with
      | none => exact erasesPrefix_lift _
      | some item =>
        cases hh : item.head? with
        | none => simpa only [hh] using (erasesPrefix_lift (liftWG (invariant "an empty ring item")) : ErasesPrefix (liftPrefix (liftWG (invariant "an empty ring item")) : Obs Bool) _)
        | some id =>
          simp only [hh, liftWG_bind]
          exact erasesPrefix_bind (nativeAccess_erases (getTxSkbPrefix_erases id)) (fun _ => erasesPrefix_lift _)))
  intro go
  cases go with
  | false => exact erasesPrefix_pure false
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases first with
    | none => exact erasesPrefix_lift _
    | some item =>
      cases hh : item.head? with
      | none => simpa only [hh] using (erasesPrefix_lift (liftWG (invariant "an empty ring item")) : ErasesPrefix (liftPrefix (liftWG (invariant "an empty ring item")) : Obs Bool) _)
      | some id =>
        simp only [hh]
        rw [liftWG_bind]
        apply erasesPrefix_bind (nativeAccess_erases (getTxSkbPrefix_erases id))
        intro head
        rw [liftWG_bind]
        apply erasesPrefix_bind (drop_erases pid item)
        intro _
        rw [liftWG_bind]
        apply erasesPrefix_bind (erasesPrefix_lift _)
        intro crypted
        cases crypted with
        | false => exact dispose_erases pid item head.keypair
        | true => simpa only [↓reduceIte, liftWG_bind] using erasesPrefix_bind (complete_erases pid item) (fun _ => dispose_erases pid item head.keypair)

theorem step_erases (pid : PeerId) : ErasesPrefix (step pid) (liftWG (txStep pid)) := by
  rw [← stepSource_eq]
  unfold step stepSource
  rw [liftWG_bind]
  apply erasesPrefix_bind (nativeAccess_erases (getPeerMixed_erases pid))
  intro p
  rw [liftWG_bind]
  apply erasesPrefix_bind (erasesPrefix_lift _)
  rintro ⟨first, q⟩
  rw [liftWG_bind]
  exact erasesPrefix_bind (nativeAccess_erases (modifyPeerKeysPrefix_erases pid _)) (fun _ => body_erases pid first)

end Leanux.Proofs.WG.Queues.TxDisposition
