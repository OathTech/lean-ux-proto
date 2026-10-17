import Leanux.Proofs.WG.TimerDiscipline.PartialExchangeArmModel
import Leanux.Proofs.WG.TimerDiscipline.ArmingOffSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

def partialExchangeArmState : WGWorld := {dev := some partialExchangeArmDevice}

def partialExchangeArmAfter (ambient : Ambient) : Ambient :=
  {ambient with steps := (((ambient.steps.push {
    decision := .retransmitGiveUp, outcome := true, operands := some (19,MAX_TIMER_HANDSHAKES),
    netRx := ambient.netRxSection}).push {
    decision := .retransmitZeroKeyNotPending, outcome := true, netRx := ambient.netRxSection}).push {
    decision := .modTimerRunning, outcome := true, netRx := ambient.netRxSection}).push {
    decision := .modTimerAlive, outcome := true, netRx := ambient.netRxSection}}

/-- The actual give-up callback can arm zero-key while the exchange remains
CREATED_INITIATION, with no keypair allocated and no key slot populated.
This is a local callback execution, not a reachable runner history. -/
theorem giveUp_arms_without_session_creation_run
    (ambient : Ambient) (mode : ambient.armRecords = false) :
    ∃ final,
      ((expiredRetransmitHandshake 0).run partialExchangeArmState).run ambient =
        .ok (((),final),partialExchangeArmAfter ambient) ∧
      final.keypairCounter = 0 ∧ final.timerEnqueues = 1 ∧
      final.dev.map (fun d => d.keypairs.isEmpty) = some true ∧
      ((Campaign2.snapshot final (partialExchangeArmAfter ambient)).peerAt 0).map
        (fun p => (p.handshakeState,p.keypairPrevious,p.keypairCurrent,p.keypairNext,p.timerZeroKeyMaterial)) =
        some (HANDSHAKE_CREATED_INITIATION,none,none,none,some ZERO_KEY_MATERIAL_TICKS.toUInt64) := by
  let final := wheelPlacementState partialExchangeArmState 0 partialExchangeArmPeer .zeroKeyMaterial
    ZERO_KEY_MATERIAL_TICKS.toUInt64 0
  refine ⟨final,?_,?_,?_,?_,?_⟩
  · simp [expiredRetransmitHandshake, getPeer, getDev, setPeer, modifyDev,
      branchCmp, AmbientM.branchCmp, branch, AmbientM.branch,
      delTimer, purgeStagedPackets, Peer.timerPending, Peer.timer,
      Peer.setTimer, Peer.setWheel, modPeerTimer, modPeerTimerGuard,
      WG.andM, callerJiffies, armTimer, getAmbient, mode,
      partialExchangeArmState,partialExchangeArmDevice,partialExchangeArmPeer,
      partialExchangeArmAfter,MAX_TIMER_HANDSHAKES,REKEY_TIMEOUT]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

end Leanux.Proofs.WG.TimerDiscipline
