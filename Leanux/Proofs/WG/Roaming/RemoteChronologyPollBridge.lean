import Leanux.Proofs.WG.Roaming.RemoteChronologyMapModel
import Leanux.Proofs.WG.Roaming.RemoteChronologyClassificationSource
import Leanux.Proofs.WG.Roaming.RemotePollSource
import Leanux.Proofs.WG.Queues.ObservePollSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Poll
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

def Tracks {E : Type} (effect : Effect E) (entry : RemoteMap)
    (h : List E) (w : World) : Prop :=
  Last effect entry h (destinationAt w.wg)

noncomputable def historyEffect : Effect RxHistory.Event :=
  fun e pid => Driver.effect (.rx e) pid

noncomputable def localEffect : Effect RxJoint.Event :=
  fun e pid => historyEffect (RxHistory.promote e) pid


/-- Chronology of precisely the suffix appended to this actual input history. -/
def Relative {E α : Type} (effect : Effect E) (observed : PrefixM E α) : Prop :=
  ∀ w h, ∃ suffix, (runPrefix observed w h).2 = h ++ suffix ∧
    match (runPrefix observed w h).1 with
    | .error _ => True
    | .ok (_,final) => Last effect (destinationAt w.wg) suffix (destinationAt final.wg)

/-- A fixed journal prefix is ignored without changing or replaying it. -/
def SuffixTracks {E : Type} (effect : Effect E) (entry : RemoteMap)
    (base h : List E) (w : World) : Prop :=
  ∃ suffix, h = base ++ suffix ∧ Tracks effect entry suffix w

end Leanux.Proofs.WG.Roaming.RemoteChronology.Poll
