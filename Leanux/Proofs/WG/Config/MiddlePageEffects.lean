import Leanux.Proofs.WG.Config.MiddlePageModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Initial acquisition establishes the held-reference invariant. -/
theorem cursorHeld_acquired (d : Device) (id : PeerId) (p : Peer)
    (resident : d.peers[id]? = some p) :
    CursorHeld d (cursorAcquired d (some id)) (some id) := by
  constructor
  · simp [cursorAcquired,resident]
  · intro key
    by_cases same : id = key
    · subst key; simp [cursorAcquired,resident]
    · simp [cursorAcquired,resident,Std.TreeMap.getElem?_insert,same]

/-- A distinct new cursor is acquired before the held cursor is released.
All outer fields and lookup-wise baseline records are retained, including
IDs absent from the dump list. No structural TreeMap equality is asserted. -/
theorem cursorHeld_handoff (base current : Device) (old : PeerId) (next : Option PeerId)
    (p : Peer) (held : CursorHeld base current (some old))
    (resident : base.peers[old]? = some p) (positive : 0 < p.refcount)
    (newResident : ∀ id, next = some id → id ≠ old ∧ ∃ q, base.peers[id]? = some q) :
    CursorHeld base (cursorHandoff current (some old) next) next := by
  have oldAt : current.peers[old]? = some {p with refcount := p.refcount+1} := by
    simpa [resident] using held.2 old
  have nonzero : p.refcount ≠ 0 := by omega
  cases next with
  | none =>
    constructor
    · simpa [cursorHandoff,cursorReleased,cursorAcquired,oldAt,Index.releasedPeerDevice,nonzero] using held.1
    · intro id
      by_cases same : old = id
      · subst id
        simp [cursorHandoff,cursorReleased,cursorAcquired,oldAt,Index.releasedPeerDevice,nonzero,resident]
      · simp [cursorHandoff,cursorReleased,cursorAcquired,oldAt,Index.releasedPeerDevice,nonzero,
          Std.TreeMap.getElem?_insert,same,held.2 id]
  | some next =>
    obtain ⟨different,q,found⟩ := newResident next rfl
    have nextAt : current.peers[next]? = some q := by
      simpa [found,Ne.symm different] using held.2 next
    constructor
    · simpa [cursorHandoff,cursorAcquired,nextAt,cursorReleased,Std.TreeMap.getElem?_insert,
        different,oldAt,Index.releasedPeerDevice,nonzero] using held.1
    · intro id
      by_cases isOld : old = id
      · subst id
        simp [cursorHandoff,cursorAcquired,nextAt,cursorReleased,Std.TreeMap.getElem?_insert,
          different,oldAt,Index.releasedPeerDevice,nonzero,resident]
      · by_cases isNext : next = id
        · subst id
          simp [cursorHandoff,cursorAcquired,nextAt,cursorReleased,Std.TreeMap.getElem?_insert,
            different,oldAt,Index.releasedPeerDevice,nonzero,found,isOld,Std.TreeMap.getElem_insert]
        · simp [cursorHandoff,cursorAcquired,nextAt,cursorReleased,Std.TreeMap.getElem?_insert,
            different,oldAt,Index.releasedPeerDevice,nonzero,isOld,isNext,held.2 id]

end Leanux.Proofs.WG.Config
