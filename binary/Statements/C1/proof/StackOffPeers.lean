import StatementC1Vacuity
import PairRequire
import PairExcept

/-! The stack-window finding of the trunk's proof, kept as a regression test.
Not part of the package build; from `binary/`:

    ../scripts/in-bundle lake env lean Statements/C1/proof/StackOffPeers.lean

Under revisions 2 and 3 `insertReady` kept the stack window apart from
`L.heap`, which holds only a peer's reference count (offset 1056) and list
head (1096). A window lying inside a peer object between those words met the
premises, and the landed `NodeInit.boundary` (`node-init.stack-separation`:
`add`'s stack bytes apart from every peer as a whole 1520-byte object) then
failed. The trunk package (`task/binary-c1-wp2`, `C1TrunkCut`) proved its cut
from an explicit hypothesis, `C1Trunk.StackOffPeers`.

Revision 4 adds `c1.stack-peers` to `insertReady`. `stackOffPeers` below is
the trunk's hypothesis, its statement copied from `C1TrunkCut` at `bccece9c`,
proved from the statement files: take the new clause out of `insertReady`
and apply the soundness of `spansApart` to the window span and the peer's
span. The two `#guard`s are the trunk's own layout: the heap separation
holds of it and the new clause refuses it. -/
namespace Binary.Statements.C1.Regression
open Binary Binary.Pair Binary.TrustBase Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- `C1Trunk.StackOffPeers`, verbatim. -/
def StackOffPeers : Prop :=
  ∀ (L : Statements.C1.Layout) (A : Allocator) (c : Context) (s : MachineState)
    (family key cidr pid : Nat) (ra : UInt64),
    insertReady L A c s family key cidr pid ra = .ok () →
    ∀ peer ∈ L.peers, ∀ x,
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth) x →
      ¬Pair.Span.contains (peer.2,Layouts.peerSize) x

theorem stackOffPeers : StackOffPeers := by
  intro L A c s family key cidr pid ra checked peer member x inside
  unfold insertReady at checked
  obtain ⟨-,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨-,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨-,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨_,-,checked⟩ := bind_ok checked
  obtain ⟨-,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨-,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨-,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨_,-,checked⟩ := bind_ok checked
  obtain ⟨-,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨apart,-⟩ := require_bind_ok _ _ _ _ checked
  exact spansApart_sound apart (List.mem_singleton.mpr rfl) (List.mem_map.mpr ⟨peer,member,rfl⟩)
    (by simpa only [Pair.Span.contains, BitVec.ofNat_toNat, BitVec.setWidth_eq] using inside)

#print axioms stackOffPeers

-- the trunk's layout: one peer at 0x10000, a stack pointer 600 bytes into it, a window of 208 bytes
#guard spansApart (Layout.heap ⟨0x1000,[(1,0x10000)],[(0x20000,0x1000)],0⟩) [(0x10000+600-208,216)]
#guard !spansApart [(0x10000+600-208,208)] ([((1 : Nat),0x10000)].map fun (_,a) => (a,Layouts.peerSize))
end Binary.Statements.C1.Regression
