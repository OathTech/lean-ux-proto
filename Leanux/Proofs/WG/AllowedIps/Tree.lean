import Leanux.Proofs.WG.AllowedIps.Prefix

/-!
# A pure allowed-IP tree

Nodes retain the mirror's unmasked addresses and node identifiers. Validity
contains address bounds and local edge conditions only. Lookup correctness is
derived against the independent flat list of owned prefixes. The relation to
the mirror's node store and its mutation history is a separate obligation.
-/

namespace Leanux.Proofs.WG.AllowedIps

structure NodeData where
  id : Nat
  addr : Nat
  cidr : Nat
  peer : Option Nat

structure Entry where
  id : Nat
  addr : Nat
  cidr : Nat
  peer : Nat
  deriving DecidableEq

def NodeData.entry (n : NodeData) (peer : Nat) : Entry :=
  ⟨n.id, n.addr, n.cidr, peer⟩

def NodeData.own (n : NodeData) : Option Entry := n.peer.map n.entry

def NodeData.entries (n : NodeData) : List Entry := n.own.toList

def Entry.Matches (width key : Nat) (e : Entry) : Prop :=
  prefixBits width e.cidr e.addr = prefixBits width e.cidr key

/-- A canonical prefix key ignores the stored address's host bits. -/
def Entry.prefixKey (width : Nat) (e : Entry) : Nat × Nat :=
  (e.cidr, prefixBits width e.cidr e.addr)

inductive Tree where
  | empty
  | node (n : NodeData) (left right : Tree)

def Tree.root : Tree → Option Nat
  | .empty => none
  | .node n _ _ => some n.id

def Tree.entries : Tree → List Entry
  | .empty => []
  | .node n l r => n.entries ++ l.entries ++ r.entries

def Tree.bindings (width : Nat) (t : Tree) : List ((Nat × Nat) × Nat) :=
  t.entries.map fun e => (e.prefixKey width, e.peer)

/-- Immediate-child conditions, with no assertion about lookup or history. -/
def Child (width : Nat) (parent : NodeData) (branch : Nat) : Tree → Prop
  | .empty => True
  | .node n _ _ => parent.cidr < n.cidr ∧
      prefixBits width parent.cidr n.addr = prefixBits width parent.cidr parent.addr ∧
      bit width parent.cidr n.addr = branch

def Tree.Valid (width : Nat) : Tree → Prop
  | .empty => True
  | .node n l r => n.addr < 2 ^ width ∧ n.cidr ≤ width ∧
      l.Valid width ∧ r.Valid width ∧ Child width n 0 l ∧ Child width n 1 r

def Tree.Compressed : Tree → Prop
  | .empty => True
  | .node n l r => l.Compressed ∧ r.Compressed ∧
      (n.peer = none → l.root.isSome ∧ r.root.isSome)

def Tree.lookup (width key : Nat) : Tree → Option Entry
  | .empty => none
  | .node n l r =>
      if prefixBits width n.cidr n.addr = prefixBits width n.cidr key then
        if n.cidr = width then n.own
        else (if bit width n.cidr key = 0 then l.lookup width key
          else r.lookup width key).or n.own
      else none

/-- A flat-list longest-prefix specification, independent of tree traversal. -/
def Winner (width key : Nat) (entries : List Entry) : Option Entry → Prop
  | none => ∀ e ∈ entries, ¬ e.Matches width key
  | some e => e ∈ entries ∧ e.Matches width key ∧
      ∀ other ∈ entries, other.Matches width key → other.cidr ≤ e.cidr

theorem NodeData.mem_entries_fields {n : NodeData} {e : Entry} (he : e ∈ n.entries) :
    e.addr = n.addr ∧ e.cidr = n.cidr := by
  cases hp : n.peer <;> simp [NodeData.entries, NodeData.own, hp] at he
  subst e
  exact ⟨rfl, rfl⟩

theorem NodeData.own_winner (n : NodeData) (width key : Nat)
    (h : prefixBits width n.cidr n.addr = prefixBits width n.cidr key) :
    Winner width key n.entries n.own := by
  cases hp : n.peer <;>
    simp [Winner, NodeData.entries, NodeData.own, hp, NodeData.entry, Entry.Matches, h]

theorem Winner.congr_entries {xs ys : List Entry} {a : Option Entry}
    (h : Winner width key xs a) (he : ∀ e, e ∈ xs ↔ e ∈ ys) : Winner width key ys a := by
  cases a with
  | none => exact fun e hm => h e ((he e).mpr hm)
  | some e => exact ⟨(he e).mp h.1, h.2.1,
      fun other hm => h.2.2 other ((he other).mpr hm)⟩

theorem Winner.append_none {xs ys : List Entry} {a : Option Entry}
    (hx : Winner width key xs a) (hy : Winner width key ys none) :
    Winner width key (xs ++ ys) a := by
  cases a with
  | none =>
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hx e he
      · exact hy e he
  | some e =>
      refine ⟨List.mem_append_left _ hx.1, hx.2.1, ?_⟩
      intro other ho hm
      rcases List.mem_append.mp ho with ho | ho
      · exact hx.2.2 other ho hm
      · exact False.elim (hy other ho hm)

theorem Winner.or_of_dominates {xs ys : List Entry} {a b : Option Entry}
    (hx : Winner width key xs a) (hy : Winner width key ys b)
    (hd : ∀ x ∈ xs, ∀ y ∈ ys, y.cidr ≤ x.cidr) :
    Winner width key (xs ++ ys) (a.or b) := by
  cases a with
  | none =>
      cases b with
      | none => exact hx.append_none hy
      | some e =>
          refine ⟨List.mem_append_right _ hy.1, hy.2.1, ?_⟩
          intro other ho hm
          rcases List.mem_append.mp ho with ho | ho
          · exact False.elim (hx other ho hm)
          · exact hy.2.2 other ho hm
  | some e =>
      refine ⟨List.mem_append_left _ hx.1, hx.2.1, ?_⟩
      intro other ho hm
      rcases List.mem_append.mp ho with ho | ho
      · exact hx.2.2 other ho hm
      · exact hd e hx.1 other ho

theorem Tree.entries_bounds {t : Tree} (hv : t.Valid width) {e : Entry}
    (he : e ∈ t.entries) : e.addr < 2 ^ width ∧ e.cidr ≤ width := by
  induction t with
  | empty => simp [Tree.entries] at he
  | node n l r ihl ihr =>
      rcases hv with ⟨ha, hc, hl, hr, _, _⟩
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · obtain ⟨haddr, hcidr⟩ := NodeData.mem_entries_fields he
          simpa [haddr, hcidr] using And.intro ha hc
        · exact ihl hl he
      · exact ihr hr he

def Tree.RootCovers (width : Nat) (e : Entry) : Tree → Prop
  | .empty => False
  | .node n _ _ => n.cidr ≤ e.cidr ∧
      prefixBits width n.cidr e.addr = prefixBits width n.cidr n.addr

theorem Tree.entries_rootCovers {t : Tree} (hv : t.Valid width) {e : Entry}
    (he : e ∈ t.entries) : t.RootCovers width e := by
  induction t with
  | empty => simp [Tree.entries] at he
  | node n l r ihl ihr =>
      rcases hv with ⟨ha, hc, hl, hr, el, er⟩
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · obtain ⟨haddr, hcidr⟩ := NodeData.mem_entries_fields he
          exact ⟨by omega, by rw [haddr]⟩
        · cases l with
          | empty => simp [Tree.entries] at he
          | node c ll lr =>
              have hh := ihl hl he
              exact ⟨Nat.le_trans (Nat.le_of_lt el.1) hh.1,
                (prefix_eq_of_le (Nat.le_of_lt el.1) hl.2.1 hh.2).trans el.2.1⟩
      · cases r with
        | empty => simp [Tree.entries] at he
        | node c rl rr =>
            have hh := ihr hr he
            exact ⟨Nat.le_trans (Nat.le_of_lt er.1) hh.1,
              (prefix_eq_of_le (Nat.le_of_lt er.1) hr.2.1 hh.2).trans er.2.1⟩

theorem Child.entries_properties {t : Tree} (hv : t.Valid width)
    (hc : Child width n branchBit t) {e : Entry} (he : e ∈ t.entries) :
    n.cidr < e.cidr ∧
      prefixBits width n.cidr e.addr = prefixBits width n.cidr n.addr ∧
      bit width n.cidr e.addr = branchBit := by
  cases t with
  | empty => simp [Tree.entries] at he
  | node c l r =>
      have hh := Tree.entries_rootCovers hv he
      exact ⟨Nat.lt_of_lt_of_le hc.1 hh.1,
        (prefix_eq_of_le (Nat.le_of_lt hc.1) hv.2.1 hh.2).trans hc.2.1,
        (bit_eq_of_prefix_eq hc.1 hv.2.1 hh.2).trans hc.2.2⟩

theorem Tree.no_match_of_root_mismatch {n : NodeData} {l r : Tree}
    (hv : (Tree.node n l r).Valid width)
    (hm : prefixBits width n.cidr n.addr ≠ prefixBits width n.cidr key) :
    Winner width key (Tree.node n l r).entries none := by
  intro e he hmatch
  have hh := Tree.entries_rootCovers hv he
  have hb := Tree.entries_bounds hv he
  exact hm (hh.2.symm.trans (prefix_eq_of_le hh.1 hb.2 hmatch))

theorem Child.no_match_of_wrong_branch {t : Tree} (hv : t.Valid width)
    (hc : Child width n branchBit t) (hbit : bit width n.cidr key ≠ branchBit) :
    Winner width key t.entries none := by
  intro e he hm
  have hp := hc.entries_properties hv he
  have hb := Tree.entries_bounds hv he
  exact hbit ((bit_eq_of_prefix_eq hp.1 hb.2 hm).symm.trans hp.2.2)

theorem Child.dominates_own {t : Tree} (hv : t.Valid width)
    (hc : Child width n branchBit t) :
    ∀ e ∈ t.entries, ∀ own ∈ n.entries, own.cidr ≤ e.cidr := by
  intro e he own ho
  have hp := hc.entries_properties hv he
  have hf := NodeData.mem_entries_fields ho
  omega

theorem Child.empty_of_full {t : Tree} (hv : t.Valid width)
    (hc : Child width n branchBit t) (hfull : n.cidr = width) : t = .empty := by
  cases t with
  | empty => rfl
  | node c l r =>
      have hlt := hc.1
      have hle := hv.2.1
      omega

/-- Local edge conditions suffice for sound, maximal longest-prefix lookup. -/
theorem Tree.lookup_spec {t : Tree} (hv : t.Valid width) (key : Nat) :
    Winner width key t.entries (t.lookup width key) := by
  induction t with
  | empty => simp [Tree.entries, Tree.lookup, Winner]
  | node n l r ihl ihr =>
      have hn := hv
      rcases hv with ⟨ha, hc, hl, hr, el, er⟩
      by_cases hm : prefixBits width n.cidr n.addr = prefixBits width n.cidr key
      · have own := n.own_winner width key hm
        by_cases hf : n.cidr = width
        · have le := el.empty_of_full hl hf
          have re := er.empty_of_full hr hf
          subst l
          subst r
          simpa only [Tree.lookup, ite_eq_left hm, ite_eq_left hf, Tree.entries, List.append_nil] using own
        · by_cases hb : bit width n.cidr key = 0
          · have other := er.no_match_of_wrong_branch (key := key) hr (by omega)
            have chosen := (ihl hl).or_of_dominates own (el.dominates_own hl)
            have merged := chosen.append_none other
            have reordered := merged.congr_entries (ys := (Tree.node n l r).entries)
              (fun e => by simp only [Tree.entries, List.mem_append]; grind)
            simpa [Tree.lookup, hm, hf, hb] using reordered
          · have other := el.no_match_of_wrong_branch hl hb
            have chosen := (ihr hr).or_of_dominates own (er.dominates_own hr)
            have merged := chosen.append_none other
            have reordered := merged.congr_entries (ys := (Tree.node n l r).entries)
              (fun e => by simp only [Tree.entries, List.mem_append]; grind)
            simpa [Tree.lookup, hm, hf, hb] using reordered
      · simpa [Tree.lookup, hm] using Tree.no_match_of_root_mismatch hn hm

theorem Child.prefixKey_ne_own {t : Tree} (hv : t.Valid width)
    (hc : Child width n branchBit t) {e own : Entry}
    (he : e ∈ t.entries) (ho : own ∈ n.entries) :
    e.prefixKey width ≠ own.prefixKey width := by
  intro h
  have hp := hc.entries_properties hv he
  have hf := NodeData.mem_entries_fields ho
  have heq := congrArg Prod.fst h
  change e.cidr = own.cidr at heq
  omega

theorem Child.prefixKey_ne_sibling {l r : Tree} (hl : l.Valid width) (hr : r.Valid width)
    (el : Child width n 0 l) (er : Child width n 1 r) {a b : Entry}
    (ha : a ∈ l.entries) (hb : b ∈ r.entries) :
    a.prefixKey width ≠ b.prefixKey width := by
  intro h
  have pa := el.entries_properties hl ha
  have pb := er.entries_properties hr hb
  have ba := Tree.entries_bounds hl ha
  have hc := congrArg Prod.fst h
  have hp := congrArg Prod.snd h
  change a.cidr = b.cidr at hc
  change prefixBits width a.cidr a.addr = prefixBits width b.cidr b.addr at hp
  rw [← hc] at hp
  have heq := bit_eq_of_prefix_eq pa.1 ba.2 hp
  omega

/-- No canonical prefix occurs twice, even though node addresses are unmasked
and the validity conditions make no global uniqueness assertion. -/
theorem Tree.prefixKeys_nodup {t : Tree} (hv : t.Valid width) :
    (t.entries.map (Entry.prefixKey width)).Nodup := by
  induction t with
  | empty => simp [Tree.entries]
  | node n l r ihl ihr =>
      rcases hv with ⟨_, _, hl, hr, el, er⟩
      have hn : (n.entries.map (Entry.prefixKey width)).Nodup := by
        cases hp : n.peer <;> simp [NodeData.entries, NodeData.own, hp]
      simp only [Tree.entries, List.map_append, List.nodup_append]
      refine ⟨⟨hn, ihl hl, ?_⟩, ihr hr, ?_⟩
      · intro a ha b hb heq
        obtain ⟨own, ho, rfl⟩ := List.mem_map.mp ha
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
        exact el.prefixKey_ne_own hl he ho heq.symm
      · intro a ha b hb heq
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨own, ho, rfl⟩ := List.mem_map.mp ha
          exact er.prefixKey_ne_own hr he ho heq.symm
        · obtain ⟨other, ho, rfl⟩ := List.mem_map.mp ha
          exact Child.prefixKey_ne_sibling hl hr el er ho he heq

theorem eq_of_nodup_map {α β : Type} {f : α → β} {xs : List α}
    (hn : (xs.map f).Nodup) {x y : α} (hx : x ∈ xs) (hy : y ∈ xs)
    (he : f x = f y) : x = y := by
  induction xs with
  | nil => simp at hx
  | cons z zs ih =>
      have hd := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        rcases List.mem_cons.mp hy with hy | hy
        · exact hy.symm
        · exact False.elim (hd.1 (List.mem_map.mpr ⟨y, hy, he.symm⟩))
      · rcases List.mem_cons.mp hy with hy | hy
        · subst y
          exact False.elim (hd.1 (List.mem_map.mpr ⟨x, hx, he⟩))
        · exact ih hd.2 hx hy

/-- Canonical-prefix uniqueness makes the independently specified winner
unique, including the absence of any matching binding. -/
theorem Winner.unique {xs : List Entry} {a b : Option Entry}
    (hn : (xs.map (Entry.prefixKey width)).Nodup)
    (ha : Winner width key xs a) (hb : Winner width key xs b) : a = b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (ha b hb.1 hb.2.1)
  | some a =>
      cases b with
      | none => exact False.elim (hb a ha.1 ha.2.1)
      | some b =>
          have hc : a.cidr = b.cidr :=
            Nat.le_antisymm (hb.2.2 a ha.1 ha.2.1) (ha.2.2 b hb.1 hb.2.1)
          have hp : a.prefixKey width = b.prefixKey width := by
            apply Prod.ext
            · exact hc
            · change prefixBits width a.cidr a.addr = prefixBits width b.cidr b.addr
              have ham := ha.2.1
              have hbm := hb.2.1
              unfold Entry.Matches at ham hbm
              rw [← hc] at hbm ⊢
              exact ham.trans hbm.symm
          exact congrArg some (eq_of_nodup_map hn ha.1 hb.1 hp)

theorem Tree.winner_iff_lookup {t : Tree} (hv : t.Valid width) {answer : Option Entry} :
    Winner width key t.entries answer ↔ answer = t.lookup width key := by
  constructor
  · intro h
    exact h.unique (Tree.prefixKeys_nodup hv) (Tree.lookup_spec hv key)
  · intro h
    rw [h]
    exact Tree.lookup_spec hv key

def Tree.height : Tree → Nat
  | .empty => 0
  | .node _ l r => max l.height r.height + 1

def Tree.HeightBound (width : Nat) : Tree → Prop
  | .empty => True
  | .node n l r => (Tree.node n l r).height + n.cidr ≤ width + 1

theorem Tree.heightBound {t : Tree} (hv : t.Valid width) : t.HeightBound width := by
  induction t with
  | empty => trivial
  | node n l r ihl ihr =>
      rcases hv with ⟨_, hc, hl, hr, el, er⟩
      have hleft : l.height + n.cidr ≤ width := by
        cases l with
        | empty => simpa [Tree.height] using hc
        | node c ll lr =>
            have hh := ihl hl
            have hlt := el.1
            change (Tree.node c ll lr).height + c.cidr ≤ width + 1 at hh
            omega
      have hright : r.height + n.cidr ≤ width := by
        cases r with
        | empty => simpa [Tree.height] using hc
        | node c rl rr =>
            have hh := ihr hr
            have hlt := er.1
            change (Tree.node c rl rr).height + c.cidr ≤ width + 1 at hh
            omega
      change max l.height r.height + 1 + n.cidr ≤ width + 1
      omega

/-- Strict CIDR growth bounds every path without assuming compression. -/
theorem Tree.height_le {t : Tree} (hv : t.Valid width) : t.height ≤ width + 1 := by
  cases t with
  | empty => simp [Tree.height]
  | node n l r =>
      have h := Tree.heightBound hv
      change (Tree.node n l r).height + n.cidr ≤ width + 1 at h
      omega

end Leanux.Proofs.WG.AllowedIps
