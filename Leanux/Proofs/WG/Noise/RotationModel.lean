import Leanux.Proofs.WG.Noise.ClearModel

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- One original peer-store write; paired fields stay in a single write. -/
inductive RotationWrite where
  | next (value : Option KeypairId)
  | previous (value : Option KeypairId)
  | previousCurrent
  | current (value : Option KeypairId)
  | nextPrevious (next previous : Option KeypairId)
  | currentNext (current next : Option KeypairId)

def RotationWrite.apply : RotationWrite → Peer → Peer
  | .next value, p => { p with keypairNext := value }
  | .previous value, p => { p with keypairPrevious := value }
  | .previousCurrent, p => { p with keypairPrevious := p.keypairCurrent }
  | .current value, p => { p with keypairCurrent := value }
  | .nextPrevious nval pval, p => { p with keypairNext := nval, keypairPrevious := pval }
  | .currentNext cval nval, p => { p with keypairCurrent := cval, keypairNext := nval }

def rotationWriteDevice (d : Device) (pid : PeerId) (write : RotationWrite) (p : Peer) : Device :=
  { d with peers := d.peers.insert pid (write.apply p) }

inductive RotationAction where
  | write (change : RotationWrite)
  | put (key : Option KeypairId)

/-- Only put occurrences contribute to the static reference budget. -/
def rotationReleases : List RotationAction → List (Option KeypairId)
  | [] => []
  | .write _ :: rest => rotationReleases rest
  | .put key :: rest => key :: rotationReleases rest

def rotationPeer : List RotationAction → Peer → Peer
  | [], p => p
  | .write change :: rest, p => rotationPeer rest (change.apply p)
  | .put _ :: rest, p => rotationPeer rest p

/-- Each write reads the then-current peer; each put retains its exact table,
reference and store effects. No relation is assumed between aliased identities. -/
inductive RotationRun (pid : PeerId) : Device → List RotationAction → Device → Prop
  | nil (d : Device) : RotationRun pid d [] d
  | write (d final : Device) (change : RotationWrite) (p : Peer) (rest : List RotationAction)
      (resident : d.peers[pid]? = some p)
      (tail : RotationRun pid (rotationWriteDevice d pid change p) rest final) :
      RotationRun pid d (.write change :: rest) final
  | put (d middle final : Device) (key : Option KeypairId) (rest : List RotationAction)
      (release : ClearPut key d middle) (tail : RotationRun pid middle rest final) :
      RotationRun pid d (.put key :: rest) final

def rotateWithNext (p : Peer) (newKey : KeypairId) : List RotationAction :=
  [.write (.nextPrevious none p.keypairNext), .put p.keypairCurrent,
    .put p.keypairPrevious, .write (.current (some newKey))]

def rotateWithoutNext (p : Peer) (newKey : KeypairId) : List RotationAction :=
  [.write (.previous p.keypairCurrent), .put p.keypairPrevious,
    .write (.current (some newKey))]

def rotateResponder (p : Peer) (newKey : KeypairId) : List RotationAction :=
  [.write (.next (some newKey)), .put p.keypairNext,
    .write (.previous none), .put p.keypairPrevious]

def rotationPlan (p : Peer) (initiator : Bool) (newKey : KeypairId) : List RotationAction :=
  if initiator then
    if p.keypairNext.isSome then rotateWithNext p newKey else rotateWithoutNext p newKey
  else rotateResponder p newKey

def confirmationPlan (p : Peer) (received : KeypairId) : List RotationAction :=
  [.write .previousCurrent, .put p.keypairPrevious,
    .write (.currentNext (some received) none)]

/-- A failed next-slot comparison performs no writes; matching confirmation
executes the three original actions. -/
def ConfirmationEffect (pid : PeerId) (received : KeypairId) (d : Device) (p : Peer) (ok : Bool) (final : Device) : Prop :=
  if p.keypairNext = some received then
    ok = true ∧ RotationRun pid d (confirmationPlan p received) final
  else ok = false ∧ final = d

end Leanux.Proofs.WG.Noise
