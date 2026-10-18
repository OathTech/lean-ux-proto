import Leanux.Proofs.WG.Index.BulkRemovalFrames
import Leanux.Proofs.WG.Index.PeerRemovalClaims
import Leanux.Proofs.WG.Index.BulkRemovalSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Bulk removal preserves numeric and embedded-owner uniqueness and the
hashed-keypair allocation bound on normal return. Both saved-peer loops and
their real cleanup run; no residency, trie shape, queue or readiness premise
is imposed, and successful completion is not asserted. -/
theorem peerRemoveAll_tables :
    Campaign2.Ensures peerRemoveAll View.TablesSafe (fun _ => View.TablesSafe) := by
  change Ensures peerRemoveAll TablesSafeWG (fun _ => TablesSafeWG)
  apply peerRemoveAll_preserves TablesSafeWG _ _ peerRemoveAfterDead_tables
  · intro g a result final after safe run
    exact tablesSafe_of_cursor g final
      (free_spec_tableCursor_variant _ g a result final after rfl run) safe
  · intro pid g a result final after safe run
    exact tablesSafe_of_cursor g final
      (peerMakeDead_spec_tableCursor_variant pid _ g a result final after rfl run) safe

end Leanux.Proofs.WG.Index
