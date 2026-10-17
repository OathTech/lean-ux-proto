import Leanux.Proofs.WG.Campaign2.View
import Leanux.WG.PtrRing

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

abbrev TurnResult := ForInStep (Option Unit × Unit)

def turnContinue : TurnResult := .yield (none, ())
def turnReturn : TurnResult := .done (some (), ())

def NoDispatchWork (worker : Worker) (d : Device) : Prop :=
  match worker with
  | .encryptWorker => d.encryptQueue.empty = true
  | .decryptWorker => d.decryptQueue.empty = true
  | .receiveWorker => d.handshakeQueue.empty = true
  | .txWorker => d.txWorkQueue = []
  | _ => True

/-- The original recordless dispatch priority. -/
def placeholderSelection (d : Device) : Option Worker :=
  [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun worker =>
    match worker with
    | .receiveWorker => !d.handshakeQueue.empty
    | .decryptWorker => !d.decryptQueue.empty
    | .encryptWorker => !d.encryptQueue.empty
    | _ => !d.txWorkQueue.isEmpty

end Leanux.Proofs.WG.Progress
