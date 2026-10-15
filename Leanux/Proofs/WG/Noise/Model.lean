import Leanux.WG.Types

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

structure Slots where
  previous : Option KeypairId
  current : Option KeypairId
  next : Option KeypairId
  deriving DecidableEq, Repr

def slots (p : Peer) : Slots :=
  ⟨p.keypairPrevious, p.keypairCurrent, p.keypairNext⟩

/-- All three arms of noise.c's add_new_keypair, including an initiator
displacing a pending responder session. -/
def rotate (s : Slots) (initiator : Bool) (newKey : KeypairId) : Slots :=
  if initiator then
    ⟨if s.next.isSome then s.next else s.current, some newKey, none⟩
  else ⟨none, s.current, some newKey⟩

def confirm (s : Slots) (received : KeypairId) : Bool × Slots :=
  if s.next == some received then
    (true, ⟨s.current, some received, none⟩)
  else (false, s)

end Leanux.Proofs.WG.Noise
