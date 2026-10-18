import Leanux.Proofs.WG.Index.TablePeerFrames
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Table/cursor projection of landed AllowedIps.free_storeView. The native
traversal retains every actual Stop; no trie-shape premise is required. -/
theorem free_spec_tableCursor_variant (initial : Option TimerDiscipline.TableCursor) :
    Ensures WG.free (fun g => g.dev.map TimerDiscipline.tableCursor = initial)
      (fun _ g => g.dev.map TimerDiscipline.tableCursor = initial) := by
  intro g ambient result final after pre run
  have effect := (Framing.hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.free_storeView (Framing.wgStoreView g))
    g ambient result final after rfl run
  have same := congrArg
    (fun v : Framing.WGStoreView × (PeerId → Option Peer) =>
      v.1.dev.map TimerDiscipline.tableCursor) effect
  have cursor : final.dev.map TimerDiscipline.tableCursor =
      g.dev.map TimerDiscipline.tableCursor := by
    change final.dev.map (fun d => (d.indexTable, d.nextKeypairId)) =
      g.dev.map (fun d => (d.indexTable, d.nextKeypairId))
    simpa [AllowedIps.clearStoreView, AllowedIps.clearStoreProjection,
      AllowedIps.resetAllowedips, Framing.wgStoreView,
      TimerDiscipline.tableCursor, Option.map_map, Function.comp_def] using same
  exact cursor.trans pre

end Leanux.Proofs.WG.Index
