import Leanux.Proofs.WG.Roaming.RemoteDriverSource
import Leanux.Proofs.WG.Roaming.RemotePollHistorySource
import Leanux.Proofs.WG.Roaming.RemoteOriginFocusSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver
open Leanux Leanux.WG Queues Leanux.Proofs.Logged

theorem covered_focus {α : Type} (entry : RemoteMap) (observed : RxHistory.Obs α)
    (appends : Appends observed)
    (covered : ∀initial,PrefixPreserves (RemotePoll.Covered initial RemotePoll.rxCause)
      (fun _=>True) observed) :
    PrefixPreserves (Inv entry) Safe (focus observed) :=
  RemoteOrigin.focused_covered entry Cause EventValid Event.rx rxEvent (fun _=>rfl)
    (fun _=>True.intro) (fun w : World=>destinationAt w.wg) RemotePoll.rxCause
    (by intro e f same pid remote origin; cases e <;> simp only [rxEvent,Option.some.injEq,reduceCtorEq] at same
        subst f; exact origin)
    observed appends covered

end Leanux.Proofs.WG.Roaming.RemoteDriver
