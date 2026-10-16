import Leanux.Proofs.WG.Campaign2.ProductView

/-! Native contracts observe the actual WireGuard and Ambient states. Product
contracts also observe the fixture fields of the original campaign view and
leave the other product components quantified. No execution state is reconstructed from a
snapshot, and normal-return, total-return and exact-outcome claims stay distinct. -/
namespace Leanux.Proofs.WG.Campaign2
open Leanux

def core (g : WGWorld) : Core where
  device := g.dev
  nlSock7 := g.nlSock7
  nlSock8 := g.nlSock8
  peerCounter := g.peerCounter
  keypairCounter := g.keypairCounter
  netIfindexNext := g.netIfindexNext
  ratelimiter := g.ratelimiter

def snapshot (g : WGWorld) (ambient : Ambient) : Snapshot where
  wg := {
    toCore := core g
    sent := g.sent
    timerClk := g.timerClk
    timerEnqueues := g.timerEnqueues
    timerPassStep := g.timerPassStep
    timerUnits := g.timerUnits
    netRxRaised := g.netRxRaised
    queuedThisCall := g.queuedThisCall
    jiffiesLast := g.jiffiesLast
    dstCacheRecords := g.dstCacheRecords
    portBound := g.portBound
    fixtureNetDevices := g.fixtureNetDevices
    lastUnderLoad := g.lastUnderLoad
    routing := g.routing
  }
  ambient := {
    env := ambient.env
    timing := ambient.timing
    envCalls := ambient.envCalls
    steps := ambient.steps
    extraOut := ambient.extraOut
    hidden := ambient.hidden
    hiddenPlaceholders := ambient.hiddenPlaceholders
    placeholderCount := ambient.placeholderCount
    suspended := ambient.suspended
    unitPeers := ambient.unitPeers
    pendingWork := ambient.pendingWork
    netRxSections := ambient.netRxSections
    netRxSection := ambient.netRxSection
    steerValues := ambient.steerValues
    armRecords := ambient.armRecords
    fired := ambient.fired
    allocArmed := ambient.allocArmed
    allocSteered := ambient.allocSteered
  }

def observeResult (out : Except Stop ((α × WGWorld) × Ambient)) : Outcome α :=
  out.map fun ((x, g), ambient) => (x, snapshot g ambient)

/-- Every successful native run, with only projected state in the predicates. -/
def Ensures (a : WG.M α) (P : Snapshot → Prop) (Q : α → Snapshot → Prop) : Prop :=
  ∀ g ambient x g' ambient', P (snapshot g ambient) →
    (a.run g).run ambient = .ok ((x, g'), ambient') → Q x (snapshot g' ambient')

/-- Success for every concrete native realization, not existence of one good run. -/
def Returns (a : WG.M α) (P : Snapshot → Prop) (Q : α → Snapshot → Prop) : Prop :=
  ∀ g ambient, P (snapshot g ambient) → ∃ x g' ambient',
    (a.run g).run ambient = .ok ((x, g'), ambient') ∧ Q x (snapshot g' ambient')

/-- Relate entry observations to the exact success or failure of a native run. -/
def Observes (a : WG.M α) (P : Snapshot → Prop)
    (Q : Snapshot → Outcome α → Prop) : Prop :=
  ∀ g ambient, P (snapshot g ambient) →
    Q (snapshot g ambient) (observeResult ((a.run g).run ambient))

/-- Compare native computations from the same actual entry states. -/
def AgreesOn (P : Snapshot → Prop) (a b : WG.M α) : Prop :=
  ∀ g ambient, P (snapshot g ambient) →
    observeResult ((a.run g).run ambient) = observeResult ((b.run g).run ambient)

/-- Observe a native computation on a copy, retaining both original states. -/
def inspect (a : WG.M α) : WG.M (Outcome α) := fun g ambient =>
  .ok ((observeResult ((a.run g).run ambient), g), ambient)

/-- Record the native projection inside an original sequential computation. -/
def read : WG.M Snapshot := fun g ambient => .ok ((snapshot g ambient, g), ambient)

namespace Product

/-- Observe the actual product's native components and original fixture view. -/
def snapshot (w : World) : Snapshot where
  toSnapshot := Campaign2.snapshot w.wg w.ambient
  fixture := {
    listenerV4 := w.fixture.listenerV4
    listenerV6 := w.fixture.listenerV6
    napiBeforePut := w.fixture.napiBeforePut
    napiAmbiguous := w.fixture.napiAmbiguous
    routesPending := w.fixture.routesPending
    routes := w.fixture.routes
    senderInbox := w.fixture.senderInbox
    netnsCHolders := w.fixture.netnsCHolders
  }

def observeResult (out : Except Stop (α × World)) : Outcome α :=
  out.map fun (x, w) => (x, snapshot w)

/-- Arbitrary successful product runs, including product-level callbacks. -/
def Ensures (a : Leanux.M α) (P : Snapshot → Prop) (Q : α → Snapshot → Prop) : Prop :=
  ∀ w x w', P (snapshot w) → a.run w = .ok (x, w') → Q x (snapshot w')

/-- Success for every actual product realization of the projected precondition. -/
def Returns (a : Leanux.M α) (P : Snapshot → Prop) (Q : α → Snapshot → Prop) : Prop :=
  ∀ w, P (snapshot w) → ∃ x w', a.run w = .ok (x, w') ∧ Q x (snapshot w')

/-- Observe the exact outcome while retaining arbitrary product inputs. -/
def Observes (a : Leanux.M α) (P : Snapshot → Prop)
    (Q : Snapshot → Outcome α → Prop) : Prop :=
  ∀ w, P (snapshot w) → Q (snapshot w) (observeResult (a.run w))

/-- Compare original product computations from the same concrete entry state. -/
def AgreesOn (P : Snapshot → Prop) (a b : Leanux.M α) : Prop :=
  ∀ w, P (snapshot w) → observeResult (a.run w) = observeResult (b.run w)

/-- Observe a product computation on a copy of its actual entry state. -/
def inspect (a : Leanux.M α) : Leanux.M (Outcome α) := fun w =>
  .ok (observeResult (a.run w), w)

/-- Record the projection without changing any product component. -/
def read : Leanux.M Snapshot := fun w => .ok (snapshot w, w)

end Product
end Leanux.Proofs.WG.Campaign2
