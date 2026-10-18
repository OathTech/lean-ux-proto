import Leanux.WG.Keypair

/-! T5's peer-allocation and slot projection. Endpoint, counters, timers,
references and unrelated device state do not enter this claim. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation
open Leanux Leanux.WG

structure Slots where
  identity : Nat
  current : Option KeypairId
  previous : Option KeypairId
  next : Option KeypairId
  deriving DecidableEq

def slots (p : Peer) : Slots := ⟨p.internalId, p.keypairCurrent, p.keypairPrevious, p.keypairNext⟩

def slotsAt (w : WGWorld) (pid : PeerId) : Option Slots :=
  (w.dev.bind fun d => d.peers[pid]?).map slots

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation
