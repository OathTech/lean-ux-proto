import Leanux.Proofs.WG.HandshakeSecurity.StagingSelectionFrames
import Leanux.Runner

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG

/-- The immutable send-side identity needed to connect slot chronology to
encryption. Reference counts, nonces and validity bits are outside this view. -/
structure KeyCore where
  allocation : Nat
  initiator : Bool
  sendingKey : Key
  deriving DecidableEq

def keyCore (k : Keypair) : KeyCore := ⟨k.internalId, k.iAmTheInitiator, k.sending.key⟩

def current (w : WGWorld) (pid : PeerId) : Option KeyCore := do
  let d ← w.dev
  let p ← d.peers[pid]?
  let kid ← p.keypairCurrent
  (d.keypairs[kid]?).map keyCore

/-- A responder allocation may be current only after its confirmation has
already been recorded. Establishing this at every real driver cut remains a
transport obligation; this predicate is not asserted as a runner hypothesis. -/
def Authorized (confirmed : List Nat) (w : WGWorld) : Prop :=
  ∀ pid core, current w pid = some core → core.initiator = false →
    core.allocation ∈ confirmed

theorem initial (net bare : Bool) : Authorized [] (Runner.initialWG net bare) := by
  intro pid core resident _
  simp only [current, Runner.initialWG] at resident
  split at resident <;> simp at resident

end Leanux.Proofs.WG.HandshakeSecurity.Responder
