import Leanux.Proofs.WG.TimerDiscipline.Model

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Supplied bytes at the original caller-read and mod_timer arm sites. -/
structure GiveUpArmInput where
  callerData : List UInt8
  armData : List UInt8

def GiveUpArmInput.caller (input : GiveUpArmInput) : UInt64 :=
  (input.callerData.foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0).toUInt64

def GiveUpArmInput.now (input : GiveUpArmInput) : UInt64 := recordWord64 input.armData 0

def GiveUpArmInput.unit (input : GiveUpArmInput) : Nat := recordWord input.armData 2

/-- Static record checks: exact payload sizes, the caller-derived expiry, and
its permitted signed zero-or-one-tick gap to mod_timer's own read. -/
def GiveUpArmInput.Valid (input : GiveUpArmInput) : Prop :=
  input.callerData.length = 8 ∧ input.armData.length = 24 ∧
  recordWord64 input.armData 1 = input.caller + ZERO_KEY_MATERIAL_TICKS.toUInt64 ∧
  0 ≤ (input.now - input.caller).toInt64 ∧ (input.now - input.caller).toInt64 ≤ 1

def GiveUpArmInput.records (input : GiveUpArmInput) (rest : List HiddenRecord) : List HiddenRecord :=
  { site := HiddenSite.timerJiffiesRetransmitZeroKey.info.id, bytes := input.callerData } ::
  { site := HiddenSite.modTimerArm.info.id, bytes := input.armData } :: rest

def absentGiveUpSteps (p : Peer) (netSection : Nat) (steps : Array Step) : Array Step :=
  (((steps.push { decision := .retransmitGiveUp, outcome := true, operands := some (p.timerHandshakeAttempts, MAX_TIMER_HANDSHAKES), netRx := netSection }).push
    { decision := .retransmitZeroKeyNotPending, outcome := true, netRx := netSection }).push
    { decision := .modTimerRunning, outcome := true, netRx := netSection }).push
    { decision := .modTimerAlive, outcome := true, netRx := netSection }

def absentGiveUpDevice (d : Device) (pid : PeerId) (p : Peer) (input : GiveUpArmInput) : Device :=
  let purged := giveUpDevice d pid p
  { purged with peers := purged.peers.insert pid ((giveUpPeer p).setTimer .zeroKeyMaterial
      (some (input.caller + ZERO_KEY_MATERIAL_TICKS.toUInt64))) }

/-- A zero address adds no registration; a nonzero address replaces all old
registrations with that address, exactly as armTimer does. -/
def absentGiveUpUnits (pid : PeerId) (input : GiveUpArmInput)
    (units : List (Nat × Nat × PeerTimer)) : List (Nat × Nat × PeerTimer) :=
  if input.unit = 0 then units
  else (input.unit, pid, .zeroKeyMaterial) :: units.filter (·.1 != input.unit)

def absentGiveUpView (entry : Snapshot) (d : Device) (pid : PeerId) (p : Peer)
    (input : GiveUpArmInput) (rest : List HiddenRecord) : Snapshot :=
  { entry with
    wg := { entry.wg with device := some (absentGiveUpDevice d pid p input), jiffiesLast := some input.now, timerUnits := absentGiveUpUnits pid input entry.wg.timerUnits }
    ambient := { entry.ambient with hidden := some rest, steps := absentGiveUpSteps p entry.ambient.netRxSection entry.ambient.steps } }

end Leanux.Proofs.WG.TimerDiscipline
