import C1Trunk

/-! Result C1, package 2 closed at the interface's exact types (added at the
integration, after revision 4 of the statement).

The package proved its cut, and with it the trunk and the child path, from
an explicit hypothesis, `C1Trunk.StackOffPeers`: the insertion's stack window
is apart from every peer as a whole object. Revisions 2 and 3 of the
statement did not give it. Revision 4 adds the clause `c1.stack-peers` to
`insertReady`, and `stackOffPeers` below takes that clause out and applies
the soundness of `spansApart`
(the same proof as the regression file `Statements/C1/proof/StackOffPeers.lean`,
here against the package's own definition). The three conditional theorems
of `C1Trunk` then close. -/
namespace Binary.Statements.C1.Proof
open Binary Binary.Pair Binary.TrustBase Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- The trunk's hypothesis, from the entry clause `c1.stack-peers`. -/
theorem stackOffPeers : C1Trunk.StackOffPeers := by
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

/-- PACKAGE 2. The trunk to the cut in the strengthened form (`C1Cut`). -/
theorem trunkToNodePlus : TrunkPlusHolds := trunkToNodePlus_of_stackOffPeers stackOffPeers
/-- PACKAGE 2. The interface's trunk. -/
theorem trunkHolds : TrunkHolds := trunkHolds_of_stackOffPeers stackOffPeers
/-- PACKAGE 2. Child attachment. -/
theorem pathChild : PathChild := pathChild_of_stackOffPeers stackOffPeers

#print axioms stackOffPeers
#print axioms trunkToNodePlus
#print axioms trunkHolds
#print axioms pathChild
end Binary.Statements.C1.Proof
