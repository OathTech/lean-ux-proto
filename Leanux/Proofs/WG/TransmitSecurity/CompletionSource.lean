import Leanux.Proofs.WG.Queues.TxDisposition
import Leanux.Proofs.Logged.Capture

/-! Native TX completion receipts retain each actual packet read, the peer
whose endpoint is selected and the socket call before later accounting. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Completion
set_option pp.structureInstances false
set_option maxHeartbeats 800000
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

structure SocketReceipt where
  pid : PeerId
  id : SkbId
  packet : RunWitness DataPacket
  peer : RunWitness Peer
  ipv4 : Bool
  socket : RunWitness Int

def SocketReceipt.endpoint (r : SocketReceipt) : Endpoint :=
  r.peer.value.endpoint.getD {family := 0,addr := 0,port := 0}

def SocketReceipt.action (r : SocketReceipt) : WG.M Int :=
  if r.ipv4 then send4 r.endpoint (some r.pid) r.packet.value.bytes r.packet.value.ds true
  else send6 r.endpoint (some r.pid) r.packet.value.bytes r.packet.value.ds true

def SocketReceipt.Valid (r : SocketReceipt) : Prop :=
  r.packet.Valid (liftWG (getTxSkb r.id)) ∧
  r.peer.Valid (liftWG (getPeer r.pid)) ∧
  r.socket.Valid (liftWG r.action)

inductive Event where
  | disposition (value : TxDisposition.Event)
  | socket (value : SocketReceipt)

def disposition? : Event → Option TxDisposition.Event
  | .disposition value => some value
  | _ => none

def socket? : Event → Option SocketReceipt
  | .socket value => some value
  | _ => none

def access (a : MixedM α) : PrefixM Event α :=
  focusPrefix Event.disposition disposition? (TxDisposition.nativeAccess a)

def socket (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : PrefixM Event Int :=
  let e := peer.value.endpoint.getD {family := 0,addr := 0,port := 0}
  receiptObserved
    (if ipv4 then access (send4Prefix e (some pid) packet.value.bytes packet.value.ds true)
     else access (send6Prefix e (some pid) packet.value.bytes packet.value.ds true))
    (fun run => .socket ⟨pid,id,packet,peer,ipv4,run⟩)

def send (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket) : PrefixM Event Bool := do
  let peer ← captureObserved (access (getPeerMixed pid))
  let family := (peer.value.endpoint.map (·.family)).getD 0
  let ret ← do
    if ← liftPrefix (liftWG (branch .sendSkbInet (family == AF_INET))) then socket pid id packet peer true
    else if ← liftPrefix (liftWG (branch .sendSkbInet6 (family == AF_INET6))) then socket pid id packet peer false
    else pure (-EAFNOSUPPORT)
  let sent := ret == 0
  if ← liftPrefix (liftWG (branch .sendSkbOk sent)) then
    access (modifyPeerKeysPrefix pid fun p => {p with txBytes := p.txBytes + packet.value.bytes.length})
  return sent

def complete (pid : PeerId) (item : List SkbId) : PrefixM Event Unit := do
  emitPrefix (.disposition (.completion pid item))
  access (timersTraversalPrefix pid)
  access (timersAnyAuthenticatedPacketSentPrefix pid)
  let mut dataSent := false
  for id in item do
    let packet ← captureObserved (access (getTxSkbPrefix id))
    _ ← liftPrefix (liftWG (branch .doneSkbIterate true))
    let isKeepalive := packet.value.bytes.length == MESSAGE_DATA_LEN_0
    let sent ← send pid id packet
    if ← TxDisposition.andObs (liftPrefix (liftWG (branch .doneSendOk sent)))
        (liftPrefix (liftWG (branch .doneNotKeepalive !isKeepalive))) then dataSent := true
  _ ← liftPrefix (liftWG (branch .doneSkbIterate false))
  if ← liftPrefix (liftWG (branch .doneDataSent dataSent)) then access (timersDataSentPrefix pid)
  access (keepKeyFreshPrefix pid)

def body (pid : PeerId) (first : Option (List SkbId)) : PrefixM Event Bool := do
  let go ← TxDisposition.andObs (liftPrefix (liftWG (branch .txPacket first.isSome))) do
    let some f := first | liftPrefix (liftWG (invariant "unreachable"))
    let some h := f.head? | liftPrefix (liftWG (invariant "an empty ring item"))
    liftPrefix (liftWG (branch .txNotUncrypted ((← access (getTxSkbPrefix h)).state != .uncrypted)))
  if !go then return false
  let some item := first | liftPrefix (liftWG (invariant "unreachable"))
  let some headId := item.head? | liftPrefix (liftWG (invariant "an empty ring item"))
  let head ← access (getTxSkbPrefix headId)
  focusPrefix Event.disposition disposition? (TxDisposition.drop pid item)
  if ← liftPrefix (liftWG (branch .txCrypted (head.state == .crypted))) then complete pid item
  focusPrefix Event.disposition disposition? (TxDisposition.dispose pid item head.keypair)

def step (pid : PeerId) : PrefixM Event Bool := do
  let (first,q) ← liftPrefix (liftWG ((← access (getPeerMixed pid)).txQueue.peek))
  access (modifyPeerKeysPrefix pid fun p => {p with txQueue := q})
  body pid first

theorem access_erases {a : MixedM α} {native : WG.M α}
    (h : ErasesStatePrefix a native) : ErasesPrefix (access a) (liftWG native) :=
  focusPrefix_erases _ _ (TxDisposition.nativeAccess_erases h)

private theorem capture_bind_erases {g : PrefixM Event α} {a : Leanux.M α}
    (hg : ErasesPrefix g a) (next : RunWitness α → PrefixM Event β)
    (f : α → Leanux.M β) (hn : ∀ r, ErasesPrefix (next r) (f r.value)) :
    ErasesPrefix (captureObserved g >>= next) (a >>= f) := by
  intro w h
  rw [runPrefix_bind,runPrefix_captureObserved]
  cases run : runPrefix g w h with
  | mk result hist =>
    have erased := hg w h
    rw [run] at erased
    cases result with
    | error stop =>
      simp only [← erased,StateT.run_bind]
      rfl
    | ok out =>
      rcases out with ⟨x,v⟩
      simp only [← erased,StateT.run_bind,Except.map]
      change (runPrefix (next ⟨x,w,v⟩) v hist).1 = (f x).run v
      exact hn ⟨x,w,v⟩ v hist


private theorem receipt_erases {g : PrefixM Event α} {a : Leanux.M α}
    (hg : ErasesPrefix g a) (record : RunWitness α → Event) :
    ErasesPrefix (receiptObserved g record) a := by
  intro w h
  rw [runPrefix_receiptObserved]
  cases run : runPrefix g w h with
  | mk result hist =>
    have erased := hg w h
    rw [run] at erased
    cases result <;> exact erased

theorem socket_erases (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) :
    ErasesPrefix (socket pid id packet peer ipv4)
      (liftWG (if ipv4 then send4 (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
        (some pid) packet.value.bytes packet.value.ds true
       else send6 (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
        (some pid) packet.value.bytes packet.value.ds true)) := by
  unfold socket
  apply receipt_erases
  cases ipv4
  · exact access_erases (send6Prefix_erases _ _ _ _ _)
  · exact access_erases (send4Prefix_erases _ _ _ _ _)

private theorem modify_then_erases (pid : PeerId) (f : Peer → Peer) (x : α) :
    ErasesPrefix (access (modifyPeerKeysPrefix pid f) >>= fun _ => pure x)
      (liftWG (getPeer pid) >>= fun p => liftWG (setPeer pid (f p)) >>= fun _ => pure x) := by
  simpa only [liftWG_bind,bind_assoc] using
    erasesPrefix_bind (access_erases (modifyPeerKeysPrefix_erases pid f))
      (fun _ => erasesPrefix_pure x)

theorem send_erases (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket) :
    ErasesPrefix (send pid id packet) (liftWG (sendSkbToPeer pid packet.value.bytes packet.value.ds)) := by
  unfold send sendSkbToPeer
  simp only [liftWG_bind,liftWG_pure,apply_ite]
  apply capture_bind_erases (access_erases (getPeerMixed_erases _))
  intro peer
  repeat' first
    | exact modify_then_erases _ _ _
    | (maintenance_head socket; exact socket_erases _ _ _ _ _)
    | (maintenance_head access; exact access_erases (modifyPeerKeysPrefix_erases _ _))
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (maintenance_head ite; apply erasesPrefix_ite)
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split


private theorem emit_bind_erases (e : Event) {g : PrefixM Event α} {a : Leanux.M α}
    (hg : ErasesPrefix g a) : ErasesPrefix (emitPrefix e >>= fun _ => g) a := by
  simpa only [pure_bind] using erasesPrefix_bind (erasesPrefix_emit e) (fun _ => hg)

theorem complete_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (complete pid item) (liftWG (createDataDone pid item)) := by
  unfold complete createDataDone
  apply emit_bind_erases
  simp only [liftWG_bind,liftWG_pure,TxDisposition.liftWG_forIn,apply_ite,WG.andM,TxDisposition.andObs]
  repeat' first
    | (maintenance_head access; with_reducible exact access_erases (timersTraversalPrefix_erases _))
    | (maintenance_head access; with_reducible exact access_erases (timersAnyAuthenticatedPacketSentPrefix_erases _))
    | (maintenance_head access; with_reducible exact access_erases (timersDataSentPrefix_erases _))
    | (maintenance_head access; with_reducible exact access_erases (keepKeyFreshPrefix_erases _))
    | (maintenance_head send; with_reducible exact send_erases _ _ _)
    | (maintenance_head captureObserved; with_reducible apply capture_bind_erases (access_erases (getTxSkbPrefix_erases _)))
    | (maintenance_head liftPrefix; with_reducible exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; with_reducible exact erasesPrefix_pure _)
    | (maintenance_head TxDisposition.andObs; with_reducible apply TxDisposition.andObs_erases)
    | (maintenance_head Bind.bind; first
        | with_reducible apply capture_bind_erases (access_erases (getTxSkbPrefix_erases _))
        | with_reducible apply erasesPrefix_bind)
    | (maintenance_head ForIn.forIn; with_reducible apply erasesPrefix_forIn)
    | (maintenance_head ite; with_reducible apply erasesPrefix_ite)
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

private theorem and_erases {a b : PrefixM Event Bool} {x y : Leanux.M Bool}
    (ha : ErasesPrefix a x) (hb : ErasesPrefix b y) :
    ErasesPrefix (TxDisposition.andObs a b) (TxDisposition.andObs x y) := by
  apply erasesPrefix_bind ha
  intro bit
  cases bit <;> first | exact hb | exact erasesPrefix_pure false

theorem body_erases (pid : PeerId) (first : Option (List SkbId)) :
    ErasesPrefix (body pid first) (liftWG (TxDisposition.bodySource pid first)) := by
  unfold body TxDisposition.bodySource
  simp only [WG.andM, liftWG_bind, liftWG_pure, apply_ite]
  apply erasesPrefix_bind
    (and_erases (erasesPrefix_lift _) (by
      cases first with
      | none => exact erasesPrefix_lift _
      | some item =>
        cases hh : item.head? with
        | none => simpa only [hh] using (erasesPrefix_lift (liftWG (invariant "an empty ring item")) : ErasesPrefix (liftPrefix (liftWG (invariant "an empty ring item")) : PrefixM Event Bool) _)
        | some id =>
          simp only [hh, liftWG_bind]
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
      | none => simpa only [hh] using (erasesPrefix_lift (liftWG (invariant "an empty ring item")) : ErasesPrefix (liftPrefix (liftWG (invariant "an empty ring item")) : PrefixM Event Bool) _)
      | some id =>
        simp only [hh]
        rw [liftWG_bind]
        apply erasesPrefix_bind (access_erases (getTxSkbPrefix_erases id))
        intro head
        rw [liftWG_bind]
        apply erasesPrefix_bind (focusPrefix_erases _ _ (TxDisposition.drop_erases pid item))
        intro _
        rw [liftWG_bind]
        apply erasesPrefix_bind (erasesPrefix_lift _)
        intro crypted
        cases crypted with
        | false => exact focusPrefix_erases _ _ (TxDisposition.dispose_erases pid item head.keypair)
        | true => simpa only [↓reduceIte, liftWG_bind] using erasesPrefix_bind (complete_erases pid item) (fun _ => focusPrefix_erases _ _ (TxDisposition.dispose_erases pid item head.keypair))

theorem step_erases (pid : PeerId) : ErasesPrefix (step pid) (liftWG (txStep pid)) := by
  rw [← TxDisposition.stepSource_eq]
  unfold step TxDisposition.stepSource
  rw [liftWG_bind]
  apply erasesPrefix_bind (access_erases (getPeerMixed_erases pid))
  intro p
  rw [liftWG_bind]
  apply erasesPrefix_bind (erasesPrefix_lift _)
  rintro ⟨first, q⟩
  rw [liftWG_bind]
  exact erasesPrefix_bind (access_erases (modifyPeerKeysPrefix_erases pid _)) (fun _ => body_erases pid first)

end Leanux.Proofs.WG.TransmitSecurity.Completion
