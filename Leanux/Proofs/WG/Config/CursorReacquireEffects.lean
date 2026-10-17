import Leanux.Proofs.WG.Config.MiddlePageEffects

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Reacquire the already-held cursor, then release its previous reference.
The ordered map writes retain the same extensional held-reference invariant;
no overflow or native execution claim is made by this pure effect fact. -/
theorem cursorHeld_reacquired (base current : Device) (id : PeerId) (p : Peer)
    (held : CursorHeld base current (some id)) (resident : base.peers[id]? = some p) :
    CursorHeld base (cursorHandoff current (some id) (some id)) (some id) := by
  have atId : current.peers[id]? = some {p with refcount := p.refcount+1} := by
    simpa [resident] using held.2 id
  constructor
  · simpa [cursorHandoff,cursorAcquired,cursorReleased,atId,Index.releasedPeerDevice] using held.1
  · intro key
    by_cases same : id = key
    · subst key
      simp [cursorHandoff,cursorAcquired,cursorReleased,atId,Index.releasedPeerDevice,resident]
    · simp [cursorHandoff,cursorAcquired,cursorReleased,atId,Index.releasedPeerDevice,
        Std.TreeMap.getElem?_insert,same,held.2 key]

end Leanux.Proofs.WG.Config
