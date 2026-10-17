import Leanux.Proofs.WG.Progress.CookieControlSource
import Leanux.Proofs.WG.Progress.ScheduleTurn

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

namespace CookieFull

theorem turn_finished (w : World) (d : Device) (device : w.wg.dev = some d)
    (hiddenEmpty : w.ambient.hidden = some []) (suspendedEmpty : w.ambient.suspended = []) :
    (scheduleTurn none).run w = .ok (turnReturn,w) := by
  have peek : (peekHiddenSite : Leanux.M (Option Nat)).run w = .ok (none,w) := by
    simpa only [List.dropWhile_nil, List.head?_nil, Option.map_none, ← hiddenEmpty] using cookiePeek_run w [] hiddenEmpty
  have filter : (w.ambient.suspended.filterM Activation.consistent).run w = .ok ([],w) := by
    rw [suspendedEmpty]; rfl
  exact turn_no_candidates none w w none d (by simp [hiddenEmpty]) peek (by simp) device
    (by simp) filter

end CookieFull
end Leanux.Proofs.WG.Progress
