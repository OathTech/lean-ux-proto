import C1Interfaces
import PairAllowedipsAssert

/-! Result C1, work package 3: re-establishing `Inv` at the common exit.
`Inv` is `Related`: an interpretation with the layout's table and peers,
the landed relation and structural check against the mirror's final world,
and the bookkeeping conjuncts. The bookkeeping comes from `StepFacts` and the
invariant at entry (`StepFacts.final`); a path supplies the interpretation,
its reconstruction, `heap`, the arena membership and `Idle`
(`inv_of_relation`). -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- `Inv` from its parts, for a device equal to the mirror's up to `target`. -/
theorem inv_of_relation {L : Layout} {A : Allocator} {w' : World} {m : DataMem}
    {names : Allowedips.Names} {dev d' : Device} {stream : List HiddenRecord}
    (table : names.table = L.table) (peers : names.trie.peers = L.peers)
    (device : w'.wg.dev = some d') (same : Allowedips.target d' = Allowedips.target dev)
    (related : Allowedips.Corresponds names Root.nodeOffsets m dev)
    (shape : heap names (Allowedips.target dev) m = .ok ())
    (armedAfter : armed w' = true) (records : w'.ambient.hidden = some stream)
    (sites : ∀ record ∈ stream, record.site ∈ allocSites.map (·.2))
    (apart : spansApart (objectsOf L) L.arena = true)
    (arena : ∀ node ∈ names.trie.nodes, InArena L node.2)
    (idle : A.Idle m (names.trie.nodes.map (·.2)) stream) : Inv L A w' m := by
  refine ⟨names,stream,table,peers,?_,armedAfter,records,sites,apart,arena,idle⟩
  apply assertAt_of_related device
  · unfold Allowedips.Corresponds at related ⊢
    rw [same]; exact related
  · rw [same]; exact shape

/-- What `StepFacts` and the invariant at entry say of the mirror's final
world, apart from its device: a device equal to `step`'s up to `target`, the
sites armed, the pending records the entry's without the consumed ones, each
an allocation record of the three sites. -/
theorem StepFacts.final {L : Layout} {A : Allocator} {m : DataMem} {w w' : World}
    {family key cidr pid : Nat} {answer : Int} {d : Device} {stream : List HiddenRecord}
    {placed : Option NodeId} {exact : Bool} {st : Step}
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (inv : Inv L A w m) :
    (∃ d', w'.wg.dev = some d' ∧ Allowedips.target d' = Allowedips.target st.device) ∧
    armed w' = true ∧ w'.ambient.hidden = some (stream.drop st.consumed) ∧
    ∀ record ∈ stream.drop st.consumed, record.site ∈ allocSites.map (·.2) := by
  obtain ⟨_,stream0,_,_,_,_,records,sites,_⟩ := inv
  have same : stream0 = stream := Option.some.inj (records.symm.trans facts.records)
  subst same
  exact ⟨facts.after,facts.armedAfter,facts.recordsAfter,
    fun record member => sites record (List.mem_of_mem_drop member)⟩

/-- The records of a case with two allocations: the stream starts with a
record of site 78 and one of site 79, and what is left afterwards is the
stream without its first two records. -/
theorem StepFacts.two_records {w w' : World} {family key cidr pid : Nat} {answer : Int} {d : Device}
    {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool} {st : Step}
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .split ∨ st.case = .splitNoMem) :
    ∃ first second rest, stream = first :: second :: rest ∧ first.site = 78 ∧ second.site = 79 ∧
      stream.drop st.consumed = rest ∧
      (first.bytes.head? = some 0 ∨ first.bytes.head? = some 1) ∧
      (second.bytes.head? = some 0 ∨ second.bytes.head? = some 1) := by
  have sites := facts.sites
  have expected : st.case.sites = [78,79] := by rcases case with h|h <;> rw [h] <;> rfl
  rw [expected] at sites
  have outcomes := facts.outcomes
  match stream, sites, outcomes with
  | first :: second :: rest, sites, outcomes =>
    match consumed : st.consumed, sites, outcomes with
    | 0, sites, _ => simp at sites
    | 1, sites, _ => simp at sites
    | n+2, sites, outcomes =>
      simp only [List.take_succ_cons,List.map_cons,List.cons.injEq] at sites
      obtain ⟨one,two,tail⟩ := sites
      have none : rest.take n = [] := List.map_eq_nil_iff.mp tail
      refine ⟨first,second,rest,rfl,one,two,?_,?_,?_⟩
      · simp only [List.drop_succ_cons]
        rcases List.take_eq_nil_iff.mp none with zero|empty
        · rw [zero]; rfl
        · rw [empty]; simp
      · exact outcomes first (by simp [List.take_succ_cons])
      · exact outcomes second (by simp [List.take_succ_cons])
  | [first], sites, _ => cases h : st.consumed <;> simp [h] at sites
  | [], sites, _ => simp at sites

#print axioms inv_of_relation
#print axioms StepFacts.final
#print axioms StepFacts.two_records
end Binary.Statements.C1.Proof
