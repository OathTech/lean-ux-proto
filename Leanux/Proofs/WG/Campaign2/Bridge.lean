import Leanux.Proofs.WG.Campaign2.View

/-! The sole common connection to the current concrete execution state.
Contracts quantify every concrete realization; no omitted subsystem is filled
with defaults. Normal-return and total-return contracts remain distinct.
After the subsystem split, retype this projection and the original actions;
do not retain a compatibility copy of the old state. -/
namespace Leanux.Proofs.WG.Campaign2
open Leanux

def core (k : Kernel) : Core where
  device := k.wg
  nlSock7 := k.nlSock7
  nlSock8 := k.nlSock8
  peerCounter := k.peerCounter
  keypairCounter := k.keypairCounter
  netIfindexNext := k.netIfindexNext
  ratelimiter := k.ratelimiter

def snapshot (w : World) : Snapshot where
  wg := { toCore := core w.k
          listenerV4 := w.listenerV4
          listenerV6 := w.listenerV6
          sent := w.sent
          timerUnits := w.timerUnits
          netRxRaised := w.netRxRaised
          napiBeforePut := w.napiBeforePut
          napiAmbiguous := w.napiAmbiguous
          queuedThisCall := w.queuedThisCall
          jiffiesLast := w.jiffiesLast
          armRecords := w.armRecords
          dstCacheRecords := w.dstCacheRecords
          addrs4 := w.addrs4
          addrs6 := w.addrs6
          defaultRoute4 := w.defaultRoute4
          defaultRoute6 := w.defaultRoute6
          defaultRoute4Accessed := w.defaultRoute4Accessed
          ipv4Gen := w.ipv4Gen
          ipv6Gen := w.ipv6Gen
          routesPending := w.routesPending
          routes := w.routes
          portBound := w.portBound
          fixtureNetDevices := w.fixtureNetDevices
          lastUnderLoad := w.lastUnderLoad
        }
  ambient := {
    env := w.env
    timing := w.timing
    envCalls := w.envCalls
    steps := w.steps
    extraOut := w.extraOut
    senderInbox := w.senderInbox
    hidden := w.hidden
    hiddenPlaceholders := w.hiddenPlaceholders
    placeholderCount := w.placeholderCount
    floodExact := w.floodExact
    suspended := w.suspended
    unitPeers := w.unitPeers
    pendingWork := w.pendingWork
    foreignCreator := w.foreignCreator
    netnsCHolders := w.netnsCHolders
    netRxSections := w.netRxSections
    netRxSection := w.netRxSection
    steerValues := w.steerValues
    fired := w.fired
    allocArmed := w.allocArmed
    allocSteered := w.allocSteered
  }

def observeResult (out : Except Stop (α × World)) : Outcome α :=
  out.map fun (x, w) => (x, snapshot w)

/-- Every successful original run, with only projected state in the predicates. -/
def Ensures (a : M α) (P : Snapshot → Prop) (Q : α → Snapshot → Prop) : Prop :=
  ∀ w x w', P (snapshot w) → a.run w = .ok (x, w') → Q x (snapshot w')

/-- Success for every concrete realization, not existence of one good run. -/
def Returns (a : M α) (P : Snapshot → Prop) (Q : α → Snapshot → Prop) : Prop :=
  ∀ w, P (snapshot w) → ∃ x w', a.run w = .ok (x, w') ∧ Q x (snapshot w')

/-- Relate entry observations to the exact success or failure of an original run. -/
def Observes (a : M α) (P : Snapshot → Prop)
    (Q : Snapshot → Outcome α → Prop) : Prop :=
  ∀ w, P (snapshot w) → Q (snapshot w) (observeResult (a.run w))

/-- Compare two original computations from the same concrete entry state.
Their internal binds retain their actual intermediate states. -/
def AgreesOn (P : Snapshot → Prop) (a b : M α) : Prop :=
  ∀ w, P (snapshot w) → observeResult (a.run w) = observeResult (b.run w)

/-- Observe a computation on a copy; no state is reconstructed from a snapshot. -/
def inspect (a : M α) : M (Outcome α) := fun w =>
  .ok (observeResult (a.run w), w)

/-- Record the current projection inside an original sequential computation. -/
def read : M Snapshot := fun w => .ok (snapshot w, w)

end Leanux.Proofs.WG.Campaign2
