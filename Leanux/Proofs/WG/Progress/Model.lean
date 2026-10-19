import Leanux.Proofs.WG.Campaign2.View
import Leanux.WG.PtrRing

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

abbrev TurnResult := ForInStep (Option Unit × Unit)

def turnContinue : TurnResult := .yield (none, ())
def turnReturn : TurnResult := .done (some (), ())

def NoDispatchWork (worker : Worker) (d : Device) (pending : List Nat) : Prop :=
  match worker with
  | .encryptWorker => d.encryptQueue.empty = true ∧ pending.contains worker.index = false
  | .decryptWorker => d.decryptQueue.empty = true ∧ pending.contains worker.index = false
  | .receiveWorker => d.handshakeQueue.empty = true ∧ pending.contains worker.index = false
  | .txWorker => d.txWorkQueue = []
  | _ => True

/-- The original recordless dispatch priority. -/
def placeholderSelection (d : Device) (pending : List Nat) : Option Worker :=
  [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun worker =>
    match worker with
    | .receiveWorker => !d.handshakeQueue.empty || pending.contains worker.index
    | .decryptWorker => !d.decryptQueue.empty || pending.contains worker.index
    | .encryptWorker => !d.encryptQueue.empty || pending.contains worker.index
    | _ => !d.txWorkQueue.isEmpty

end Leanux.Proofs.WG.Progress
