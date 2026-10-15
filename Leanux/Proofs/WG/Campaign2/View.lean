import Leanux.Kernel.Defs

/-! Campaign 2's data-only observation. No file-descriptor, pipe, epoll or
seccomp state is retained. Ambient records and scheduling observations are
explicitly separate from WireGuard-owned state. This is not an executable
replacement mirror: execution is connected in `Bridge`. -/
namespace Leanux.Proofs.WG.Campaign2
open Leanux

/-- The WireGuard fields currently stored alongside other subsystem stores. -/
structure Core where
  device : Option WG.Device
  nlSock7 : WG.NlSock
  nlSock8 : WG.NlSock
  peerCounter : Nat
  keypairCounter : Nat
  netIfindexNext : Nat
  ratelimiter : Ratelimiter

/-- WireGuard state, network fixture, routing, transmit and timer data. -/
structure State extends Core where
  listenerV4 : List (Nat × List UInt8)
  listenerV6 : List (Nat × List UInt8)
  sent : List SentDatagram
  timerUnits : List (Nat × Nat × WG.PeerTimer)
  netRxRaised : Bool
  napiBeforePut : List Bool
  napiAmbiguous : Nat
  queuedThisCall : List Nat
  jiffiesLast : Option UInt64
  armRecords : Bool
  dstCacheRecords : Bool
  addrs4 : List Nat
  addrs6 : List Nat
  defaultRoute4 : Bool
  defaultRoute6 : Bool
  defaultRoute4Accessed : Bool
  ipv4Gen : Nat
  ipv6Gen : Nat
  routesPending : Bool
  routes : List (Nat × Nat × Nat)
  portBound : Nat → Bool
  fixtureNetDevices : List (String × Nat × Option String)
  lastUnderLoad : Option Int64

/-- Inputs and observations owned by execution, not the WireGuard device. -/
structure Context where
  env : EnvSite → Nat → Bool
  timing : Timing
  envCalls : List (EnvSite × Nat)
  steps : Array Step
  extraOut : List (String × Lean.Json)
  senderInbox : List InboxDatagram
  hidden : Option (List HiddenRecord)
  hiddenPlaceholders : Bool
  placeholderCount : Nat
  floodExact : Bool
  suspended : List Activation
  unitPeers : List (Nat × Nat × Nat)
  pendingWork : List Nat
  foreignCreator : Bool
  netnsCHolders : List Nat
  netRxSections : Nat
  netRxSection : Nat
  steerValues : List (String × Option (List UInt8))
  fired : Array String
  allocArmed : List String
  allocSteered : List String

structure Snapshot where
  wg : State
  ambient : Context

def Snapshot.peerAt (s : Snapshot) (pid : WG.PeerId) : Option WG.Peer :=
  s.wg.device.bind fun d => d.peers[pid]?

def Snapshot.tagAt (s : Snapshot) (pid : WG.PeerId) : Option Nat :=
  (s.peerAt pid).map WG.Peer.handshakeState

abbrev Outcome (α : Type) := Except Stop (α × Snapshot)

end Leanux.Proofs.WG.Campaign2
