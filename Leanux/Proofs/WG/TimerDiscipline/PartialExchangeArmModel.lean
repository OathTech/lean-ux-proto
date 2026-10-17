import Leanux.Proofs.WG.Campaign2.View
import Leanux.WG.Timers

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- A local partial-exchange fixture, not a claimed reachable runner trace. -/
def partialExchangeArmPeer : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 0
  handshakeState := HANDSHAKE_CREATED_INITIATION
  timerHandshakeAttempts := 19 }

def partialExchangeArmDevice : Device := {
  ifindex := 0, ifname := "wg0", running := true
  peers := ({} : Std.TreeMap PeerId Peer).insert 0 partialExchangeArmPeer }

/-- Complete WireGuard fixture projection. Ambient is intentionally not fixed. -/
def partialExchangeArmView : Campaign2.State := {
  device := some partialExchangeArmDevice, nlSock7 := {}, nlSock8 := {}
  peerCounter := 0, keypairCounter := 0, netIfindexNext := 4, ratelimiter := {}
  sent := [], timerClk := none, timerEnqueues := 0, timerPassStep := none, timerUnits := []
  netRxRaised := false, queuedThisCall := [], jiffiesLast := none, dstCacheRecords := true
  portBound := fun _ => false, fixtureNetDevices := [], lastUnderLoad := none, routing := {} }

end Leanux.Proofs.WG.TimerDiscipline
