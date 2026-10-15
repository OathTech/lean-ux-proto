import Leanux.Kernel.Defs

namespace Binary.WorldParts
open Leanux

/-! Exhaustive decomposition only: this file does not define the physical
    relation or assume that any part is represented. The round-trip theorem
    prevents a residual ghost World from hiding unaccounted fields. Each
    component still needs its own memory/environment/history equations. -/

/-- Kernel-owned state, including routing and pending work. Suspended activations
    need relations to saved task contexts as well as scheduling history. Kernel
    object ids/counters require naming and baseline equations, not raw bytes. -/
structure Physical where
  k : Kernel
  suspended : List Activation
  pendingWork : List Nat
  netRxRaised : Bool
  addrs4 : List Nat
  addrs6 : List Nat
  defaultRoute4 : Bool
  defaultRoute6 : Bool
  defaultRoute4Accessed : Bool
  ipv4Gen : Nat
  ipv6Gen : Nat
  lastUnderLoad : Option Int64

def physical (w : World) : Physical := {
  k := w.k
  suspended := w.suspended
  pendingWork := w.pendingWork
  netRxRaised := w.netRxRaised
  addrs4 := w.addrs4
  addrs6 := w.addrs6
  defaultRoute4 := w.defaultRoute4
  defaultRoute6 := w.defaultRoute6
  defaultRoute4Accessed := w.defaultRoute4Accessed
  ipv4Gen := w.ipv4Gen
  ipv6Gen := w.ipv6Gen
  lastUnderLoad := w.lastUnderLoad }

/-- Fixed configuration and external oracles supplied by the harness. Mutable
    record/schedule suffixes are in History, not unconstrained functions here. -/
structure Supplied where
  env : EnvSite → Nat → Bool
  timing : Timing
  hiddenPlaceholders : Bool
  floodExact : Bool
  foreignCreator : Bool
  armRecords : Bool
  dstCacheRecords : Bool
  routes : List (Nat × Nat × Nat)
  portBound : Nat → Bool
  fixtureNetDevices : List (String × Nat × Option String)
  allocArmed : List String
  allocSteered : List String

def supplied (w : World) : Supplied := {
  env := w.env
  timing := w.timing
  hiddenPlaceholders := w.hiddenPlaceholders
  floodExact := w.floodExact
  foreignCreator := w.foreignCreator
  armRecords := w.armRecords
  dstCacheRecords := w.dstCacheRecords
  routes := w.routes
  portBound := w.portBound
  fixtureNetDevices := w.fixtureNetDevices
  allocArmed := w.allocArmed
  allocSteered := w.allocSteered }

/-- State outside the WireGuard boundary: external receive queues, emitted
    datagrams awaiting delivery, namespace holders and deferred fixture routing.
    These need a fixed incoming fixture state and its actual event history;
    they are not permitted to absorb kernel-owned fields. -/
structure Fixture where
  listenerV4 : List (Nat × List UInt8)
  listenerV6 : List (Nat × List UInt8)
  senderInbox : List InboxDatagram
  sent : List SentDatagram
  netnsCHolders : List Nat
  routesPending : Bool

def fixture (w : World) : Fixture := {
  listenerV4 := w.listenerV4
  listenerV6 := w.listenerV6
  senderInbox := w.senderInbox
  sent := w.sent
  netnsCHolders := w.netnsCHolders
  routesPending := w.routesPending }

/-- Observations, record/schedule cursors and execution progress. These must
    be derived from a fixed incoming history and actual subsequent events.
    Copies of past user outputs are observations, not current user-memory bytes. -/
structure History where
  envCalls : List (EnvSite × Nat)
  steps : Array Step
  emitted : Std.HashSet String
  translatedLen : Option Nat
  userOut : Option ByteArray
  userFds : Option (Nat × Nat)
  extraOut : List (String × Lean.Json)
  hidden : Option (List HiddenRecord)
  placeholderCount : Nat
  napiBeforePut : List Bool
  napiAmbiguous : Nat
  netRxSections : Nat
  netRxSection : Nat
  steerValues : List (String × Option (List UInt8))
  queuedThisCall : List Nat
  fired : Array String

def history (w : World) : History := {
  envCalls := w.envCalls
  steps := w.steps
  emitted := w.emitted
  translatedLen := w.translatedLen
  userOut := w.userOut
  userFds := w.userFds
  extraOut := w.extraOut
  hidden := w.hidden
  placeholderCount := w.placeholderCount
  napiBeforePut := w.napiBeforePut
  napiAmbiguous := w.napiAmbiguous
  netRxSections := w.netRxSections
  netRxSection := w.netRxSection
  steerValues := w.steerValues
  queuedThisCall := w.queuedThisCall
  fired := w.fired }

/-- Last recorded time and address-to-owner associations. These require
    provenance and lifetime equations. The four key placeholders inside Kernel
    are handled separately by FixtureKnowledge, never as physical zero bytes. -/
structure Knowledge where
  unitPeers : List (Nat × Nat × Nat)
  timerUnits : List (Nat × Nat × WG.PeerTimer)
  jiffiesLast : Option UInt64

def knowledge (w : World) : Knowledge := {
  unitPeers := w.unitPeers
  timerUnits := w.timerUnits
  jiffiesLast := w.jiffiesLast }

structure Parts where
  physical : Physical
  supplied : Supplied
  fixture : Fixture
  history : History
  knowledge : Knowledge

def split (w : World) : Parts :=
  ⟨physical w, supplied w, fixture w, history w, knowledge w⟩

def assemble (p : Parts) : World := {
  k := p.physical.k
  env := p.supplied.env
  timing := p.supplied.timing
  envCalls := p.history.envCalls
  steps := p.history.steps
  emitted := p.history.emitted
  translatedLen := p.history.translatedLen
  userOut := p.history.userOut
  userFds := p.history.userFds
  extraOut := p.history.extraOut
  listenerV4 := p.fixture.listenerV4
  listenerV6 := p.fixture.listenerV6
  senderInbox := p.fixture.senderInbox
  sent := p.fixture.sent
  hidden := p.history.hidden
  hiddenPlaceholders := p.supplied.hiddenPlaceholders
  placeholderCount := p.history.placeholderCount
  floodExact := p.supplied.floodExact
  suspended := p.physical.suspended
  unitPeers := p.knowledge.unitPeers
  timerUnits := p.knowledge.timerUnits
  pendingWork := p.physical.pendingWork
  foreignCreator := p.supplied.foreignCreator
  netnsCHolders := p.fixture.netnsCHolders
  netRxRaised := p.physical.netRxRaised
  napiBeforePut := p.history.napiBeforePut
  napiAmbiguous := p.history.napiAmbiguous
  netRxSections := p.history.netRxSections
  netRxSection := p.history.netRxSection
  steerValues := p.history.steerValues
  queuedThisCall := p.history.queuedThisCall
  jiffiesLast := p.knowledge.jiffiesLast
  armRecords := p.supplied.armRecords
  dstCacheRecords := p.supplied.dstCacheRecords
  fired := p.history.fired
  addrs4 := p.physical.addrs4
  addrs6 := p.physical.addrs6
  defaultRoute4 := p.physical.defaultRoute4
  defaultRoute6 := p.physical.defaultRoute6
  defaultRoute4Accessed := p.physical.defaultRoute4Accessed
  ipv4Gen := p.physical.ipv4Gen
  ipv6Gen := p.physical.ipv6Gen
  routesPending := p.fixture.routesPending
  routes := p.supplied.routes
  portBound := p.supplied.portBound
  fixtureNetDevices := p.supplied.fixtureNetDevices
  allocArmed := p.supplied.allocArmed
  allocSteered := p.supplied.allocSteered
  lastUnderLoad := p.physical.lastUnderLoad
}

/-- Every World field is included, including functions and history fields. -/
theorem assemble_split (w : World) : assemble (split w) = w := by
  cases w
  rfl

/-- Component equality determines the entire World. This is field coverage,
    not yet functionality of a machine-to-World relation. -/
theorem split_injective {a b : World} (equal : split a = split b) : a = b := by
  simpa only [assemble_split] using congrArg assemble equal

#print axioms assemble_split
#print axioms split_injective
end Binary.WorldParts
