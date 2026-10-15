import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalModel
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.Roaming.InitiationCallSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

def receiveTraversalPrelude (msg : List UInt8) (pid : PeerId) : M Unit := do
  let peer := some pid
  if ← branch .hsWrongPacket peer.isNone then
    invariant "a wrong type of packet in the handshake queue"
  let some pid := peer | invariant "unreachable"
  let p ← getPeer pid
  setPeer pid { p with rxBytes := p.rxBytes + msg.length }
  modifyDev fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length }
  timersAnyAuthenticatedPacketReceived pid

def receiveTraversalCommon (msg : List UInt8) (pid : PeerId) : M Unit := do
  receiveTraversalPrelude msg pid
  timersTraversal pid
  peerPut (some pid)

def responseBeforeCommon (pid : PeerId) : M Unit := do
  if ← branch .hsRespSessionBegun (← beginSession pid) then
    timersSessionDerived pid
    timersHandshakeComplete pid
    sendKeepalive pid

theorem initiationAfterSetter_common (msg : List UInt8) (pid : PeerId) :
    initiationAfterSetter msg pid = (do sendHandshakeResponse pid; receiveTraversalCommon msg pid) := by
  simp only [initiationAfterSetter, receiveTraversalCommon, receiveTraversalPrelude,
    bind_assoc, bind_if, pure_bind]

theorem responseAfterSetter_common (msg : List UInt8) (pid : PeerId) :
    responseAfterSetter msg pid = (do responseBeforeCommon pid; receiveTraversalCommon msg pid) := by
  simp only [responseAfterSetter, responseBeforeCommon, receiveTraversalCommon,
    receiveTraversalPrelude, bind_assoc, bind_if, pure_bind]

def observedReceiveTraversalCommon (msg : List UInt8) (pid : PeerId) : M DataDoneTraversalCut := do
  receiveTraversalPrelude msg pid
  let hook ← dataDoneCapture (timersTraversal pid)
    (prefixClockPath (traversalPrefix pid) .timerJiffiesTraversal)
  peerPut (some pid)
  return hook

theorem receiveTraversal_unit_drop (action : M Unit) : (do action; pure ()) = action := by
  funext entry
  change (action.run entry >>= fun out => Except.ok ((), out.2)) = action.run entry
  cases h : action.run entry with
  | error err => rfl
  | ok pair => rcases pair with ⟨u, final⟩; cases u; rfl

theorem observedReceiveTraversalCommon_erase (msg : List UInt8) (pid : PeerId) :
    (do let _ ← observedReceiveTraversalCommon msg pid; pure ()) = receiveTraversalCommon msg pid := by
  simp only [observedReceiveTraversalCommon, receiveTraversalCommon, bind_assoc,
    pure_bind, receiveTraversal_unit_drop]
  rw [dataDoneCapture_bind]

def observedInitiationReceiveTraversal (msg : List UInt8) (src : SkbSource) :
    M (Option (ReceiveTraversalCut InitiationCallCut)) := do
  let candidate ← initiationCallPrefix msg src
  match candidate with
  | none => pure none
  | some cut =>
    setPeerEndpointFromSkb cut.consumed.pid src
    sendHandshakeResponse cut.consumed.pid
    let hook ← observedReceiveTraversalCommon msg cut.consumed.pid
    return some ⟨cut, hook⟩

def observedResponseReceiveTraversal (msg : List UInt8) (src : SkbSource) :
    M (Option (ReceiveTraversalCut ResponseCallCut)) := do
  let candidate ← responseCallPrefix msg src
  match candidate with
  | none => pure none
  | some cut =>
    setPeerEndpointFromSkb cut.consumed.input.pid src
    responseBeforeCommon cut.consumed.input.pid
    let hook ← observedReceiveTraversalCommon msg cut.consumed.input.pid
    return some ⟨cut, hook⟩

theorem observedInitiationReceiveTraversal_erase (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (do let _ ← observedInitiationReceiveTraversal msg src; pure ()) = receiveHandshakePacket msg src := by
  rw [← receiveHandshakePacket_initiation msg src kind]
  simp only [observedInitiationReceiveTraversal, bind_assoc]
  congr 1
  funext candidate
  cases candidate with
  | none => rfl
  | some cut =>
    simp only [initiationCallSuffix, initiationAfterSetter_common, bind_assoc, pure_bind,
      observedReceiveTraversalCommon_erase]

theorem observedResponseReceiveTraversal_erase (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (do let _ ← observedResponseReceiveTraversal msg src; pure ()) = receiveHandshakePacket msg src := by
  rw [← receiveHandshakePacket_response msg src kind]
  simp only [observedResponseReceiveTraversal, bind_assoc]
  congr 1
  funext candidate
  cases candidate with
  | none => rfl
  | some cut =>
    simp only [responseCallSuffix, responseAfterSetter_common, bind_assoc, pure_bind,
      observedReceiveTraversalCommon_erase]

end Leanux.Proofs.WG.TimerDiscipline
