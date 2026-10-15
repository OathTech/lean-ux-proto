import Leanux.Proofs.WG.TimerDiscipline.Model

/-! Supplied-record premises and exact timer rearm observations. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2
structure RetransmitArmInput where
  callerData : List UInt8
  rejected : List UInt8
  accepted : UInt8
  armData : List UInt8

def RetransmitArmInput.caller (input : RetransmitArmInput) : UInt64 :=
  (input.callerData.foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0).toUInt64
def RetransmitArmInput.delay (input : RetransmitArmInput) : Nat :=
  REKEY_TIMEOUT_TICKS + jitterValue input.accepted
def RetransmitArmInput.now (input : RetransmitArmInput) : UInt64 := recordWord64 input.armData 0
def RetransmitArmInput.unit (input : RetransmitArmInput) : Nat := recordWord input.armData 2
def RetransmitArmInput.Valid (input : RetransmitArmInput) : Prop :=
  input.callerData.length = 8 ∧
  (∀ byte ∈ input.rejected, ¬jitterAccepted byte) ∧ jitterAccepted input.accepted ∧
  input.armData.length = 24 ∧
  recordWord64 input.armData 1 = input.caller + input.delay.toUInt64 ∧
  0 ≤ (input.now - input.caller).toInt64 ∧ (input.now - input.caller).toInt64 ≤ 1
def RetransmitArmInput.records (input : RetransmitArmInput) (rest : List HiddenRecord) :=
  { site := HiddenSite.timerJiffiesHandshakeInitiated.info.id, bytes := input.callerData } ::
    jitterStream .retransmit input.rejected input.accepted
      ({ site := HiddenSite.modTimerArm.info.id, bytes := input.armData } :: rest)

def retransmitReadySteps (netSection : Nat) (steps : Array Step) :=
  (steps.push { decision := .modTimerRunning, outcome := true, netRx := netSection }).push
    { decision := .modTimerAlive, outcome := true, netRx := netSection }
def retransmitReadyUnits (pid : PeerId) (input : RetransmitArmInput)
    (units : List (Nat × Nat × PeerTimer)) :=
  if input.unit = 0 then units
  else (input.unit, pid, .retransmitHandshake) :: units.filter (·.1 != input.unit)

def retransmitReadyView (entry : Snapshot) (d : Device) (pid : PeerId) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord) : Snapshot :=
  { entry with
    wg := { entry.wg with
      device := some {d with peers := d.peers.insert pid (p.setTimer .retransmitHandshake (some (input.caller + input.delay.toUInt64)))}
      jiffiesLast := some input.now
      timerUnits := retransmitReadyUnits pid input entry.wg.timerUnits }
    ambient := { entry.ambient with
      hidden := some rest
      steps := retransmitReadySteps entry.ambient.netRxSection entry.ambient.steps } }

def retransmitSkippedSteps (running : Bool) (netSection : Nat) (steps : Array Step) :=
  let first := steps.push { decision := .modTimerRunning, outcome := running, netRx := netSection }
  if running then first.push { decision := .modTimerAlive, outcome := false, netRx := netSection }
  else first

def retransmitSkippedView (entry : Snapshot) (d : Device) (input : RetransmitArmInput)
    (rest : List HiddenRecord) : Snapshot :=
  {entry with ambient := {entry.ambient with
    hidden := some ({site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest)
    steps := retransmitSkippedSteps d.running entry.ambient.netRxSection entry.ambient.steps}}

end Leanux.Proofs.WG.TimerDiscipline
