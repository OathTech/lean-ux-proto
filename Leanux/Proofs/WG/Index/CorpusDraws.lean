import Leanux.Proofs.WG.Index.DrawRecords

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

/-- The first two index_draw payloads in corpus/wireguard/s2_index_collision.json. -/
def corpusCollisionDraw : Draw := ⟨0x0d, 0x0c, 0x0b, 0x0a⟩

/-- The third index_draw payload in corpus/wireguard/s2_index_collision.json. -/
def corpusFreshDraw : Draw := ⟨0x44, 0x33, 0x22, 0x11⟩

theorem corpusCollisionDraw_value : corpusCollisionDraw.value = 0x0a0b0c0d := by decide
theorem corpusFreshDraw_value : corpusFreshDraw.value = 0x11223344 := by decide

def corpusInsertPair (first second : PeerId) : M (Nat × Nat) := do
  let a ← indexInsert (.handshake first)
  let b ← indexInsert (.handshake second)
  return (a, b)

theorem insertPair_returns (first second : PeerId) (different : first ≠ second)
    (collision fresh : Draw) (drawsDiffer : (collision.value == fresh.value) = false)
    (d : Device) (empty : d.indexTable = []) (rest : List HiddenRecord) :
    Returns (corpusInsertPair first second)
      (fun w => w.k.wg = some d ∧ w.hidden = some
        (collision.record :: collision.record :: fresh.record :: rest))
      (fun result w => result = (collision.value, fresh.value) ∧
        w.k.wg = some { d with indexTable :=
          [{ index := fresh.value, owner := .handshake second },
           { index := collision.value, owner := .handshake first }] } ∧
        w.hidden = some rest) := by
  let middle := { d with indexTable :=
    [{ index := collision.value, owner := IndexOwner.handshake first }] }
  have ha := indexInsert_records (.handshake first) d [] collision
    (collision.record :: fresh.record :: rest)
    (by simp) (by simp [removeOwner, empty])
  have hb := indexInsert_records (.handshake second) middle [collision] fresh rest
    (by simp [middle, removeOwner, different])
    (by simp [middle, removeOwner, different, drawsDiffer])
  intro w pre
  obtain ⟨a, v, arun, avalue, adev, ahidden⟩ := ha w pre
  have vdev : v.k.wg = some middle := by simpa [middle, removeOwner, empty] using adev
  obtain ⟨b, u, brun, bvalue, bdev, bhidden⟩ := hb v ⟨vdev, ahidden⟩
  refine ⟨(a, b), u, ?_, ?_, ?_, bhidden⟩
  · simp only [corpusInsertPair, StateT.run_bind]
    rw [arun]
    change ((fun out => Except.ok ((a, out.1), out.2)) =<< (indexInsert (.handshake second)).run v) = _
    rw [brun]
    rfl
  · exact Prod.ext avalue bvalue
  · simpa [middle, removeOwner, different] using bdev

theorem corpusInsertPair_returns (first second : PeerId) (different : first ≠ second)
    (d : Device) (empty : d.indexTable = []) (rest : List HiddenRecord) :
    Returns (corpusInsertPair first second)
      (fun w => w.k.wg = some d ∧ w.hidden = some
        (corpusCollisionDraw.record :: corpusCollisionDraw.record :: corpusFreshDraw.record :: rest))
      (fun result w => result = (0x0a0b0c0d, 0x11223344) ∧
        w.k.wg = some { d with indexTable :=
          [{ index := 0x11223344, owner := .handshake second },
           { index := 0x0a0b0c0d, owner := .handshake first }] } ∧
        w.hidden = some rest) := by
  simpa only [corpusCollisionDraw_value, corpusFreshDraw_value] using
    insertPair_returns first second different corpusCollisionDraw corpusFreshDraw
      (by decide) d empty rest

end Leanux.Proofs.WG.Index
