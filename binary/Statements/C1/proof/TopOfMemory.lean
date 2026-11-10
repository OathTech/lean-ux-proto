import C1Invariant

/-! The finding behind `C1Interfaces.NodeBelowTop`, executed. Not part of the
package build; from `binary/`:

    ../scripts/in-bundle lake env lean Statements/C1/proof/TopOfMemory.lean

An arena whose last span ends at 2^64 passes every check the statements make
of an arena (`spansApart`, which bounds a span by `≤ 2^64`), and the object
at `2^64 - 72` meets every decidable clause of `AllocResult` (non-NULL,
aligned, inside an arena span, apart from the nodes handed out). The landed
interpretation check refuses that object, so `assertAt`, and with it the
landed relation, cannot hold once it is handed out. -/
open Binary Binary.Pair Binary.Pair.Allowedips Binary.Statements.C1

def top : Nat := 2^64 - 72
def arena : List Pair.Span := [(0x100000,0x1000),(top,72)]
def objects : List Pair.Span := [(0x200000,AllowedipsMutationLayout.tableSize),(0x300000,Layouts.peerSize)]
def names (node : Nat) : Allowedips.Names := ⟨0x200000,⟨[(0,node)],[(0,0x300000)]⟩,1⟩
def verdict (node : Nat) : String := match validate (names node) Root.nodeOffsets with
  | .ok _ => "accepted" | .error e => s!"refused: {e.message}"

-- the statements' checks of the arena, and `AllocResult`'s decidable clauses for `top`
#eval spansApart objects arena                                              -- true
#eval top != 0 && top % 8 == 0 && arena.any (fun span => span.1 ≤ top && top+nodeSize ≤ span.1+span.2)  -- true
-- the landed interpretation check, for the object below the top and for the top one
#eval verdict (top-8)   -- accepted
#eval verdict top       -- refused
