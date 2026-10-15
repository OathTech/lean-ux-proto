import Leanux.Proofs.WG.TimerDiscipline.RetransmitReadyModel
import Leanux.Proofs.WG.Noise.InitiationReadyModel

set_option autoImplicit false

/-! Pure ordered effects and supplied-input observations for original initiation
send and retransmit rearm. No actual execution witness appears in readiness. -/
namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Campaign2 Noise

def noEndpointSendSteps (netRx : Nat) (steps : Array Step) : Array Step :=
  (((steps.push {decision := .sendBufNoMem, outcome := false, netRx}).push
    {decision := .sendSkbInet, outcome := false, netRx}).push
    {decision := .sendSkbInet6, outcome := false, netRx}).push
    {decision := .sendSkbOk, outcome := false, netRx}

def initiationTailClock (bytes : List UInt8) : Int64 :=
  (bytes.foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0).toUInt64.toInt64

def initiationMacPeer (p : Peer) (msg : List UInt8) : Peer :=
  {p with lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length-32)), haveSentMac1 := true}
def initiationTailPeer (p : Peer) (msg bytes : List UInt8) : Peer :=
  {((initiationMacPeer p msg).setTimer .sendKeepalive none) with lastSentHandshake := initiationTailClock bytes}
def initiationTailDevice (d : Device) (pid : PeerId) (p : Peer) (msg bytes : List UInt8) : Device :=
  let mac := initiationMacPeer p msg
  let deleted := mac.setTimer .sendKeepalive none
  {d with peers := ((d.peers.insert pid mac).insert pid deleted).insert pid (initiationTailPeer p msg bytes)}
def initiationTailSteps (netRx : Nat) (steps : Array Step) : Array Step :=
  (steps.push {decision := .addMacCookieValid, outcome := false, netRx}).push
    {decision := .traversalKeepalive, outcome := false, operands := some (0,0), netRx}
def initiationPacket (p : Peer) (msg : List UInt8) : List UInt8 :=
  let body := msg.take (msg.length-32)
  body ++ blake2s 16 p.cookieMac1Key body ++ List.replicate 16 0

def initiationEntryPeer (p : Peer) (bytes : List UInt8) : Peer :=
  {p with lastSentHandshake := initiationTailClock bytes}
def initiationEntryDevice (d : Device) (pid : PeerId) (p : Peer) (bytes : List UInt8) : Device :=
  {d with peers := d.peers.insert pid (initiationEntryPeer p bytes)}

def sendCreationResult (pid : PeerId) (d : Device) (p : Peer)
    (last ephemeral clock : List UInt8) (index : Nat) : List UInt8 × Device :=
  InitiationReady.result pid (initiationEntryDevice d pid p last) (initiationEntryPeer p last)
    ephemeral clock index

end Leanux.Proofs.WG.TimerDiscipline.SendReady
