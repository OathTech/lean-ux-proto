import Leanux.Proofs.WG.AllowedIps.MutationMirror

/-! Exact source-snapshot list deletion. The fold retains saved peer values;
it does not replace snapshot reads with current-store getters. -/
set_option pp.structureInstances false
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def unlist (id : Nat) (p : WG.Peer) : WG.Peer :=
  { p with allowedipsList := WG.listRemove p.allowedipsList id }

def delStep (id : Nat) (peers : Std.TreeMap Nat WG.Peer) (entry : Nat × WG.Peer) :=
  if entry.2.allowedipsList.contains id then peers.insert entry.1 (unlist id entry.2) else peers

def delFold (id : Nat) (xs : List (Nat × WG.Peer)) (peers : Std.TreeMap Nat WG.Peer) :=
  xs.foldl (delStep id) peers

def unlisted (d : WG.Device) (id : Nat) : WG.Device :=
  { d with peers := delFold id d.peers.toList d.peers }

theorem listDel_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d) (id : Nat) :
    ⦃fun w => ⌜w = k⌝⦄ WG.listDel id
    ⦃⇓ result w => ⌜result = () ∧ w = { k with dev := some (unlisted d id) }⌝⦄ := by
  mvcgen [WG.listDel, WG.getDev, invariant, AmbientM.invariant, WG.setPeer, WG.modifyDev]
  invariants
  | inv1 => (fun cursor w => ⌜w = { k with dev := some { d with
      peers := delFold id cursor.1.prefix d.peers } }⌝, ExceptConds.false)
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [delFold, delStep, unlist, unlisted, List.foldl_append]
  rw [← hd]

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

theorem unlisted_identity (d : WG.Device) (id pid : Nat) :
    ((unlisted d id).peers[pid]?).map WG.Peer.internalId =
      (d.peers[pid]?).map WG.Peer.internalId := by
  rw [unlisted_get]
  cases d.peers[pid]? <;> rfl

end Leanux.Proofs.WG.AllowedIps
