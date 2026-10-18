import PairCountTarget
import PairCallRelation

namespace Binary.Pair.Trie
open Leanux Leanux.WG
set_option maxRecDepth 2048

theorem word_of_loadInt {m : DataMem} {base size value : Nat} (path : String)
    (bound : base+size ≤ 2^64) (read : m.loadInt (.ofNat 64 base) size = some (value : Int)) :
    word m path base size = .ok value := by
  unfold word
  rw [ite_eq_left bound]
  cases bytes : m.loadBytes (.ofNat 64 base) size with
  | none => simp [Mem.loadInt,bytes] at read
  | some bs =>
    have equal : Int.ofBytes bs = (value : Int) := by simpa only [Mem.loadInt,bytes,Option.map_some,Option.some.injEq] using read
    simp only [equal,Int.toNat_natCast]

theorem mapM_map_result (xs : List α) (f : α → Except ε β) (g : β → γ) :
    xs.mapM (fun x => (f x).map g) = (xs.mapM f).map (List.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,ih]
    cases f x <;> cases xs.mapM f <;> rfl

/-- Generic decoder update: retain node reads and transform decoded counts.
Validation is independent of memory and is reused without re-proving it. -/
theorem reconstruct_map_counts (names : Names) (o : AllowedipsProbe.Offsets)
    (before after : DataMem) (f : Nat → Nat → Nat)
    (nodes : ∀ id base, (id,base) ∈ names.nodes → decodeNode names o after base = decodeNode names o before base)
    (counts : ∀ id base, (id,base) ∈ names.peers →
      word after s!"peer[{id}].refcount" (base+o.peerRefcount) 4 =
        (word before s!"peer[{id}].refcount" (base+o.peerRefcount) 4).map (f id)) :
    reconstruct names o after = (reconstruct names o before).map (fun state =>
      {state with counts := state.counts.map fun (id,count) => (id,f id count)}) := by
  have ns : names.nodes.mapM (m := Decode) (fun (id,a) => do return (id, ← decodeNode names o after a)) =
      names.nodes.mapM (m := Decode) (fun (id,a) => do return (id, ← decodeNode names o before a)) := by
    apply mapM_same
    rintro ⟨id,base⟩ member
    simp only [nodes id base member]
  have ps : names.peers.mapM (m := Decode) (fun (id,a) => do return (id, ← word after s!"peer[{id}].refcount" (a+o.peerRefcount) 4)) =
      (names.peers.mapM (m := Decode) (fun (id,a) => do return (id, ← word before s!"peer[{id}].refcount" (a+o.peerRefcount) 4))).map
        (List.map fun (id,count) => (id,f id count)) := by
    rw [←mapM_map_result]
    apply mapM_same
    rintro ⟨id,base⟩ member
    simp only []
    rw [counts id base member]
    cases word before s!"peer[{id}].refcount" (base+o.peerRefcount) 4 <;> rfl
  unfold reconstruct
  rw [ns,ps]
  cases validate names o with
  | error e => rfl
  | ok value =>
    cases names.nodes.mapM (m := Decode) (fun (id,a) => do return (id, ← decodeNode names o before a)) <;>
      cases names.peers.mapM (m := Decode) (fun (id,a) => do return (id, ← word before s!"peer[{id}].refcount" (a+o.peerRefcount) 4)) <;> rfl

/-- Reconstruct one changed peer word from its executed load equation and
frame every other decoded word. The conclusion uses the actual source map
update, including its identity ordering. -/
theorem reconstruct_peer_update {names o before after d id peer} {count : Nat}
    (related : Corresponds names o before d) (present : d.peers.get? id = some peer)
    (nodes : ∀ node base, (node,base) ∈ names.nodes → decodeNode names o after base = decodeNode names o before base)
    (changed : ∀ base, (id,base) ∈ names.peers →
      after.loadInt (.ofNat 64 (base+o.peerRefcount)) 4 = some (count : Int))
    (others : ∀ pid base, (pid,base) ∈ names.peers → pid≠id →
      word after s!"peer[{pid}].refcount" (base+o.peerRefcount) 4 =
        word before s!"peer[{pid}].refcount" (base+o.peerRefcount) 4) :
    Corresponds names o after {d with peers := d.peers.insert id {peer with refcount := count}} := by
  have fields := reconstruct_fields related
  have update := reconstruct_map_counts names o before after (fun pid old => if pid=id then count else old) nodes (by
    intro pid base named
    by_cases same : pid=id
    · subst pid
      obtain ⟨⟨pid',old⟩,_,identity,read⟩ := fields.peers.left (id,base) named
      have bounds := fields.peerRange id base named
      have layout := fields.layout.2.2.2.2.2.2.2.2
      have mapped := word_of_loadInt (base := base+o.peerRefcount) (size := 4) s!"peer[{id}].refcount" (by
        rw [layout]
        have size : Layouts.peer_refcount+4 ≤ Layouts.peerSize := by decide
        omega) (changed base named)
      simp only [mapped,read,Except.map,↓reduceIte]
    · rw [others pid base named same]
      cases word before s!"peer[{pid}].refcount" (base+o.peerRefcount) 4 <;> simp [same,Except.map])
  unfold Corresponds
  rw [update,related]
  exact congrArg Except.ok (target_replaceCount d id count peer present).symm

#print axioms reconstruct_peer_update
end Binary.Pair.Trie
