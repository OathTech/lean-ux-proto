import C1Invariant

/-! The top-of-memory finding, kept as a regression test. Not part of the
package build; from `binary/`:

    ../scripts/in-bundle lake env lean Statements/C1/proof/TopOfMemory.lean

An arena whose last span ends at 2^64 passes every check the statements make
of an arena (`spansApart`, which bounds a span by `≤ 2^64`), and the object
at `2^64 - 72` meets every decidable clause of revision 2's `AllocResult`
(non-NULL, aligned, inside an arena span, apart from the nodes handed out).
The landed interpretation check refuses that object, so `assertAt`, and with
it the landed relation, cannot hold once it is handed out: under revision 2
the headline was not provable with the landed relation.

Revision 3 adds `a + nodeSize < 2^64` to `AllocResult`'s success clause.
`result3` below is that clause's decidable part, conjunct for conjunct; the
file fails to elaborate (`#guard`) unless the top-of-memory object is
excluded by it, the object eight bytes lower is admitted, and the bound
agrees with the landed check on both. -/
open Binary Binary.Pair Binary.Pair.Allowedips Binary.Statements.C1

def top : Nat := 2^64 - 72
def arena : List Pair.Span := [(0x100000,0x1000),(top,72)]
def objects : List Pair.Span := [(0x200000,AllowedipsMutationLayout.tableSize),(0x300000,Layouts.peerSize)]
def names (node : Nat) : Allowedips.Names := ⟨0x200000,⟨[(0,node)],[(0,0x300000)]⟩,1⟩
def verdict (node : Nat) : String := match validate (names node) Root.nodeOffsets with
  | .ok _ => "accepted" | .error e => s!"refused: {e.message}"

/-- The decidable conjuncts of revision 2's success clause (no object handed out yet). -/
def result2 (a : Nat) : Bool :=
  a != 0 && a % 8 == 0 && arena.any (fun span => span.1 ≤ a && a+nodeSize ≤ span.1+span.2)
/-- The decidable conjuncts of revision 3's success clause: the bound is new. -/
def result3 (a : Nat) : Bool :=
  a != 0 && a % 8 == 0 && decide (a + nodeSize < 2^64) &&
    arena.any (fun span => span.1 ≤ a && a+nodeSize ≤ span.1+span.2)

-- the statements' checks of the arena still pass: the arena is not what excludes the object
#guard spansApart objects arena
-- revision 2 admitted the top-of-memory object; revision 3 excludes it
#guard result2 top
#guard !result3 top
-- the bound is the only conjunct that excludes it, and it is not too strong:
-- an object eight bytes lower (in an arena widened to hold it) is admitted by both
#guard top + nodeSize == 2^64
#guard (top-8) != 0 && (top-8) % 8 == 0 && decide ((top-8) + nodeSize < 2^64)
-- the landed interpretation check agrees with the bound on both objects
#guard verdict (top-8) == "accepted"
#guard verdict top != "accepted"
#eval verdict top       -- refused: NULL/wrapping object
#eval s!"revision 2 AllocResult admits top: {result2 top}; revision 3: {result3 top}"
