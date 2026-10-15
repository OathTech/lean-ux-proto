import Leanux.Proofs.WG.TimerDiscipline.SendReadyModel
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchModel
import Leanux.Proofs.WG.Index.DrawRecords

set_option autoImplicit false

/-! Pure records and effects of one named original send-worker dispatch. -/
namespace Leanux.Proofs.WG.TimerDiscipline.WorkerReady
open Leanux Leanux.WG Campaign2 Noise SendReady

def retainedPutSteps (refs netRx : Nat) (steps : Array Step) : Array Step :=
  (((((steps.push {decision := .peerPutNull, outcome := false, netRx}).push
    {decision := .refcountSubPositive, outcome := true, operands := some (refs,0), netRx}).push
    {decision := .refcountSubToZero, outcome := false, operands := some (refs,1), netRx}).push
    {decision := .refcountSubNonpositive, outcome := false, netRx}).push
    {decision := .refcountSubUnderflow, outcome := false, netRx}).push
    {decision := .peerKrefPutReleased, outcome := false, netRx}

def sentPeer (p : Peer) (msg bytes : List UInt8) (input : RetransmitArmInput) : Peer :=
  (initiationTailPeer p msg bytes).setTimer .retransmitHandshake
    (some (input.caller + input.delay.toUInt64))
def sentDevice (d : Device) (pid : PeerId) (p : Peer) (msg bytes : List UInt8)
    (input : RetransmitArmInput) : Device :=
  {initiationTailDevice d pid p msg bytes with
    peers := (initiationTailDevice d pid p msg bytes).peers.insert pid (sentPeer p msg bytes input)}

/-- The actual named section encloses rate/last-sent, creation, send and rearm
records. Site names remain tied to the original hidden-input definitions. -/
def records (start rate last ephemeral clock tailClock stop : List UInt8)
    (collisions : List Index.Draw) (fresh : Index.Draw) (input : RetransmitArmInput)
    (rest : List HiddenRecord) : List HiddenRecord :=
  {site := (HiddenSite.sectionStart .sendWorker).info.id, bytes := start} ::
    {site := HiddenSite.birthdateExpired.info.id, bytes := rate} ::
    {site := HiddenSite.initLastSent.info.id, bytes := last} ::
    {site := HiddenSite.initEphemeral.info.id, bytes := ephemeral} ::
    {site := HiddenSite.tai64nNow.info.id, bytes := clock} ::
    Index.drawStream collisions fresh
      ({site := HiddenSite.initLastSentAgain.info.id, bytes := tailClock} ::
        input.records ({site := (HiddenSite.sectionStop .sendWorker).info.id, bytes := stop} :: rest))

/-- Exact ordered Device writes: dequeue, creation, MAC/timer/last-sent updates,
retransmit arm, and finally the retained worker reference decrement. -/
def result (pid : PeerId) (d : Device) (p createdPeer : Peer)
    (last ephemeral clock tailClock : List UInt8) (index : Nat)
    (input : RetransmitArmInput) : Device :=
  let made := sendCreationResult pid (dequeuedSendDevice d pid p)
    {p with handshakePending := false} last ephemeral clock index
  let sent := sentDevice made.2 pid createdPeer made.1 tailClock input
  let peer := sentPeer createdPeer made.1 tailClock input
  {sent with peers := sent.peers.insert pid {peer with refcount := peer.refcount - 1}}

end Leanux.Proofs.WG.TimerDiscipline.WorkerReady
