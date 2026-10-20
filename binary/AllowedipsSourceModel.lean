import Leanux.WG.AllowedIps

/-! Binary-local endpoint and record definitions. Copied without changing their
formulas from Leanux/Proofs/WG/AllowedIps/{MutationMirror,ListsMirror,
ExactMutation,ArithmeticMirror}.lean at eba3c2b6. These definitions describe
segments; they do not prove that WG.add reaches a segment or returns from it.
This module deliberately imports only the operational mirror. -/
namespace Binary.Pair.Allowedips.Model
open Leanux

def rootSlot (v4 : Bool) : WG.Slot := if v4 then .root4 else .root6

def rootWidth (v4 : Bool) : Nat := if v4 then 32 else 128

def rootValue (d : WG.Device) (v4 : Bool) : Option Nat :=
  if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6

def rootWrite (d : WG.Device) (v4 : Bool) (value : Option Nat) : WG.Device :=
  { d with peerAllowedips := if v4 then { d.peerAllowedips with root4 := value }
      else { d.peerAllowedips with root6 := value } }

def emptyInstalled (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let n := WG.newNode addr cidr (rootWidth v4) (some pid)
  rootWrite { d with
    nextNode := d.nextNode + 1
    nodes := (d.nodes.insert d.nextNode n).insert d.nextNode { n with parent := rootSlot v4 }
    peers := d.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [d.nextNode] } }
    v4 (some d.nextNode)

def unlist (id : Nat) (p : WG.Peer) : WG.Peer :=
  { p with allowedipsList := WG.listRemove p.allowedipsList id }

def delStep (id : Nat) (peers : Std.TreeMap Nat WG.Peer) (entry : Nat × WG.Peer) :=
  if entry.2.allowedipsList.contains id then peers.insert entry.1 (unlist id entry.2) else peers

def delFold (id : Nat) (xs : List (Nat × WG.Peer)) (peers : Std.TreeMap Nat WG.Peer) :=
  xs.foldl (delStep id) peers

def unlisted (d : WG.Device) (id : Nat) : WG.Device :=
  { d with peers := delFold id d.peers.toList d.peers }

def exactInstalled (d : WG.Device) (id : Nat) (old : WG.AipNode) (pid : Nat) (p : WG.Peer) : WG.Device :=
  { d with
    nodes := d.nodes.insert id { old with peer := some pid }
    peers := (unlisted d id).peers.insert pid
      { unlist id p with allowedipsList := (unlist id p).allowedipsList ++ [id] } }

def record (w : Ambient) (d : Decision) (outcome : Bool) : Ambient :=
  { w with steps := w.steps.push { decision := d, outcome, netRx := w.netRxSection } }

/-- The complete bookkeeping of `commonBits`, including its unsupported-width
return of zero. The two supported families are selected by its callers. -/
def commonRecords (w : Ambient) (width x : Nat) : Ambient :=
  let w := record w .commonBits32 (width == 32)
  if width == 32 then w else
  let w := record w .commonBits128 (width == 128)
  if width == 128 then record w .fls128High (x / 2 ^ 64 != 0) else w

-- The two map lemmas below are copied from ListsMirror at the same commit.
private theorem delFold_get (id : Nat) (xs : List (Nat × WG.Peer))
    (original current : Std.TreeMap Nat WG.Peer)
    (hs : ∀ x ∈ xs, original[x.1]? = some x.2) (q : Nat) :
    (delFold id xs current)[q]? =
      if xs.any (fun x => x.1 == q && x.2.allowedipsList.contains id)
      then (original[q]?).map (unlist id) else current[q]? := by
  induction xs generalizing current with
  | nil => rfl
  | cons x xs ih =>
    simp only [delFold, List.foldl_cons]
    rw [show xs.foldl (delStep id) (delStep id current x) =
      delFold id xs (delStep id current x) from rfl, ih _ (fun y hy => hs y (by simp [hy]))]
    have hx := hs x (by simp)
    by_cases ht : xs.any (fun x => x.1 == q && x.2.allowedipsList.contains id) = true
    · simp only [List.any_cons, ht, Bool.or_true, ite_true]
    · by_cases he : x.1 = q
      · subst q
        by_cases hc : x.2.allowedipsList.contains id = true
        · simp only [List.any_cons, ht, hc, beq_self_eq_true, Bool.true_and, Bool.or_false, Bool.false_eq_true, ite_true, ite_false, delStep, hx, Option.map_some, Std.TreeMap.getElem?_insert_self]
        · simp only [List.any_cons, ht, hc, beq_self_eq_true, Bool.true_and, Bool.or_false, Bool.false_eq_true, ite_false, delStep]
      · simp only [List.any_cons, ht, show (x.1 == q) = false from by simp [he], Bool.false_and, Bool.false_or, Bool.false_eq_true, ite_false]
        unfold delStep
        split <;> simp [Std.TreeMap.getElem?_insert, he]

theorem unlisted_get (d : WG.Device) (id pid : Nat) :
    (unlisted d id).peers[pid]? = (d.peers[pid]?).map (unlist id) := by
  rw [show (unlisted d id).peers = delFold id d.peers.toList d.peers from rfl,
    delFold_get id d.peers.toList d.peers d.peers
      (fun x hx => Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hx)]
  cases hp : d.peers[pid]? with
  | none =>
    have hn : ¬ d.peers.toList.any (fun x => x.1 == pid && x.2.allowedipsList.contains id) = true := by
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      rintro ⟨⟨j,p⟩, hj, he, _⟩
      change j = pid at he
      subst j
      have := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hj
      simp [hp] at this
    simp only [hn, Bool.false_eq_true, ite_false, Option.map_none]
  | some p =>
    by_cases hc : p.allowedipsList.contains id = true
    · have hy : d.peers.toList.any (fun x => x.1 == pid && x.2.allowedipsList.contains id) = true := by
        simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
        exact ⟨(pid,p), Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hp, rfl, hc⟩
      simp only [hy, ite_true, Option.map_some]
    · have hu : unlist id p = p := by
        have hf : p.allowedipsList.filter (· != id) = p.allowedipsList := by
          apply List.filter_eq_self.mpr
          intro a ha
          have hn : id ∉ p.allowedipsList := by simpa using hc
          simp only [bne_iff_ne]
          exact fun he => hn (he ▸ ha)
        simp [unlist, WG.listRemove, hf]
      simp only [Option.map_some, hu]
      split <;> rfl

end Binary.Pair.Allowedips.Model
