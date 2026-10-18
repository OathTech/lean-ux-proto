import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DataCompletionRules
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.WG Lifetimes Queues

theorem preserves (P : WGWorld → Prop) (pid : PeerId) (item : List SkbId)
    (traversal : Preserves P (timersTraversal pid))
    (authenticated : Preserves P (timersAnyAuthenticatedPacketSent pid))
    (send : ∀ bytes ds, Preserves P (sendSkbToPeer pid bytes ds))
    (dataSent : Preserves P (timersDataSent pid))
    (fresh : Preserves P (keepKeyFresh pid)) :
    Preserves P (createDataDone pid item) := by
  have read (id : SkbId) : Preserves P (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a packet v b pre run
    exact (Packets.getTxSkb_current id w v packet a b run).1 ▸ pre
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  rw [← TimerDiscipline.dataDoneSource_eq]
  routing_tx_source [TimerDiscipline.dataDoneSource,TimerDiscipline.dataDoneStep,TimerDiscipline.dataDoneFinish]
    using [read,traversal,authenticated,send,dataSent,fresh,ambient]

end Leanux.Proofs.WG.Noise.DataCompletionRules
