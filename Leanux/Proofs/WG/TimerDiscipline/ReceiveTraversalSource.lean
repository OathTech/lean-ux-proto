import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalModel
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.Roaming.InitiationCallProductSource
import Leanux.Proofs.WG.Roaming.ResponseCallProductSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

def receiveTraversalPrelude (msg : List UInt8) (pid : PeerId) : WG.M Unit := do
  let peer := some pid
  if ← branch .hsWrongPacket peer.isNone then
    invariant "a wrong type of packet in the handshake queue"
  let some pid := peer | invariant "unreachable"
  let p ← getPeer pid
  setPeer pid { p with rxBytes := p.rxBytes + msg.length }
  modifyDev fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length }
  timersAnyAuthenticatedPacketReceived pid

def receiveTraversalCommon (msg : List UInt8) (pid : PeerId) : WG.M Unit := do
  receiveTraversalPrelude msg pid
  timersTraversal pid
  peerPut (some pid)

def responseBeforeCommon (pid : PeerId) : WG.M Unit := do
  if ← branch .hsRespSessionBegun (← beginSession pid) then
    timersSessionDerived pid
    timersHandshakeComplete pid
    sendKeepalive pid

theorem initiationAfterSetter_common (msg : List UInt8) (pid : PeerId) :
    initiationAfterSetter msg pid = (do sendHandshakeResponse pid; receiveTraversalCommon msg pid) := by
  have bindIf {α β : Type} (condition : Prop) [Decidable condition]
      (yes no : WG.M α) (next : α → WG.M β) :
      ((if condition then yes else no) >>= next) =
        (if condition then yes >>= next else no >>= next) := by split <;> rfl
  simp only [initiationAfterSetter, receiveTraversalCommon, receiveTraversalPrelude, bind_assoc, bindIf]

theorem responseAfterSetter_common (msg : List UInt8) (pid : PeerId) :
    responseAfterSetter msg pid = (do responseBeforeCommon pid; receiveTraversalCommon msg pid) := by
  have bindIf {α β : Type} (condition : Prop) [Decidable condition]
      (yes no : WG.M α) (next : α → WG.M β) :
      ((if condition then yes else no) >>= next) =
        (if condition then yes >>= next else no >>= next) := by split <;> rfl
  simp only [responseAfterSetter, responseBeforeCommon, receiveTraversalCommon,
    receiveTraversalPrelude, bind_assoc, bindIf, pure_bind]

def observedReceiveTraversalCommon (msg : List UInt8) (pid : PeerId) : Leanux.M DataDoneTraversalCut := do
  liftWG (receiveTraversalPrelude msg pid)
  let hook ← dataDoneCapture (liftWG (timersTraversal pid))
    (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal)
  liftWG (peerPut (some pid))
  return hook

theorem receiveTraversal_unit_drop (action : Leanux.M Unit) : (do action; pure ()) = action := by
  funext entry
  change (action.run entry >>= fun out => Except.ok ((), out.2)) = action.run entry
  cases h : action.run entry with
  | error err => rfl
  | ok pair => rcases pair with ⟨u, final⟩; cases u; rfl

theorem observedReceiveTraversalCommon_erase (msg : List UInt8) (pid : PeerId) :
    (do let _ ← observedReceiveTraversalCommon msg pid; pure ()) = liftWG (receiveTraversalCommon msg pid) := by
  simp only [observedReceiveTraversalCommon, receiveTraversalCommon, liftWG_bind_variant, bind_assoc,
    pure_bind, receiveTraversal_unit_drop]
  rw [dataDoneCapture_bind]

def observedInitiationReceiveTraversal (msg : List UInt8) (src : SkbSource) :
    Leanux.M (Option (ReceiveTraversalCut Roaming.Product.InitiationCallCut)) := do
  let candidate ← Roaming.Product.initiationCallPrefix msg src
  match candidate with
  | none => pure none
  | some cut =>
    liftWG (setPeerEndpointFromSkb cut.consumed.pid src)
    liftWG (sendHandshakeResponse cut.consumed.pid)
    let hook ← observedReceiveTraversalCommon msg cut.consumed.pid
    return some ⟨cut, hook⟩

def observedResponseReceiveTraversal (msg : List UInt8) (src : SkbSource) :
    Leanux.M (Option (ReceiveTraversalCut Roaming.Product.ResponseCallCut)) := do
  let candidate ← Roaming.Product.responseCallPrefix msg src
  match candidate with
  | none => pure none
  | some cut =>
    liftWG (setPeerEndpointFromSkb cut.consumed.input.pid src)
    liftWG (responseBeforeCommon cut.consumed.input.pid)
    let hook ← observedReceiveTraversalCommon msg cut.consumed.input.pid
    return some ⟨cut, hook⟩

theorem observedInitiationReceiveTraversal_erase (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (do let _ ← observedInitiationReceiveTraversal msg src; pure ()) = liftWG (receiveHandshakePacket msg src) := by
  rw [← Roaming.Product.receiveHandshakePacket_initiation msg src kind]
  simp only [observedInitiationReceiveTraversal, bind_assoc]
  congr 1
  funext candidate
  cases candidate with
  | none => rfl
  | some cut =>
    simp only [Roaming.Product.initiationCallSuffix, initiationAfterSetter_common, liftWG_bind_variant, bind_assoc, pure_bind,
      observedReceiveTraversalCommon_erase]

theorem observedResponseReceiveTraversal_erase (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (do let _ ← observedResponseReceiveTraversal msg src; pure ()) = liftWG (receiveHandshakePacket msg src) := by
  rw [← Roaming.Product.receiveHandshakePacket_response msg src kind]
  simp only [observedResponseReceiveTraversal, bind_assoc]
  congr 1
  funext candidate
  cases candidate with
  | none => rfl
  | some cut =>
    simp only [Roaming.Product.responseCallSuffix, responseAfterSetter_common, liftWG_bind_variant, bind_assoc, pure_bind,
      observedReceiveTraversalCommon_erase]


end Leanux.Proofs.WG.TimerDiscipline
