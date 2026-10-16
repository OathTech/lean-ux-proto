import Leanux.Kernel.Defs

/-! Campaign 2's data-only observation. No file-descriptor, pipe, epoll or
seccomp state is retained. Ambient records and scheduling observations are
explicitly separate from WireGuard-owned state. This is not an executable
replacement mirror: execution is connected in `Bridge`. -/
namespace Leanux.Proofs.WG.Campaign2
open Leanux

/-- The WireGuard device, sockets and counters observed by the campaign. -/
structure Core where
  device : Option WG.Device
  nlSock7 : WG.NlSock
  nlSock8 : WG.NlSock
  peerCounter : Nat
  keypairCounter : Nat
  netIfindexNext : Nat
  ratelimiter : Ratelimiter

/-- WireGuard-owned state, routing, transmit and timer data. -/
structure State extends Core where
  sent : List SentDatagram
  timerClk : Option UInt64
  timerEnqueues : Nat
  timerPassStep : Option UInt64
  timerUnits : List (Nat × Nat × WG.PeerTimer)
  netRxRaised : Bool
  queuedThisCall : List Nat
  jiffiesLast : Option UInt64
  dstCacheRecords : Bool
  portBound : Nat → Bool
  fixtureNetDevices : List (String × Nat × Option String)
  lastUnderLoad : Option Int64
  routing : Net.Routing

/-- Inputs and observations owned by execution, not the WireGuard device. -/
structure Context where
  env : EnvSite → Nat → Bool
  timing : Timing
  envCalls : List (EnvSite × Nat)
  steps : Array Step
  extraOut : List (String × Lean.Json)
  hidden : Option (List HiddenRecord)
  hiddenPlaceholders : Bool
  placeholderCount : Nat
  suspended : List Activation
  unitPeers : List (Nat × Nat × Nat)
  pendingWork : List Nat
  netRxSections : Nat
  netRxSection : Nat
  steerValues : List (String × Option (List UInt8))
  armRecords : Bool
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
