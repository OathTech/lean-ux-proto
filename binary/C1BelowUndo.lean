import C1BelowStep
import AllowedipsSourceModel
import AllowedipsRootOwners
import AllowedipsPlacementSimulation
import PairAllowedipsHeapFrame
import PairAllowedipsFrame
import AllowedipsAllocationValidate

/-! Result C1, work package 3: the data side of the rollback (case
`splitNoMem`). The mirror's device afterwards is the device before with the
allocation counter advanced: the node was allocated, listed, unlisted and
freed. So the interpretation is the old one with its counter advanced, and
the relation holds for any memory that agrees with the cut's on the bytes
the old interpretation reads. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1 Binary.Pair.Allowedips.Model

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- The interpretation with its allocation counter moved to `counter`. -/
def recount (names : Allowedips.Names) (counter : Nat) : Allowedips.Names := {names with nextNode := counter}

theorem validate_recount {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {counter : Nat}
    (grows : names.nextNode ≤ counter) (valid : validate names o = .ok ()) :
    validate (recount names counter) o = .ok () := by
  have below := ids_below_counter valid
  unfold validate at valid
  obtain ⟨_,trieValid,valid⟩ := bind_ok valid
  obtain ⟨table,valid⟩ := check_ok _ _ _ _ valid
  obtain ⟨_,aligns,valid⟩ := bind_ok valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,tables,_⟩ := bind_ok valid
  have counterNew : forIn (m:=Decode) names.trie.nodes () (fun (pair : Nat×Nat) _ => do
      unless pair.1<counter do throw (⟨"names.nextNode",pair.1,"identity beyond allocation counter"⟩ : DecodeError)
      pure (.yield ()))=.ok () := by
    apply forIn_yield
    intro pair member
    have small : pair.1<counter := Nat.lt_of_lt_of_le (below pair member) grows
    simp only [small,ite_true]
    rfl
  unfold validate
  change (do
    Trie.validate names.trie o
    unless 0<names.table && names.table%8==0 && names.table+AllowedipsMutationLayout.tableSize<2^64 do
      throw (⟨"table",names.table,"NULL, unaligned or wrapping table"⟩ : DecodeError)
    let _ ← forIn (m:=Decode) names.trie.nodes () _
    let _ ← forIn (m:=Decode) names.trie.nodes () _
    let _ ← forIn (m:=Decode) _ () _
    pure ())=.ok ()
  rw [trieValid,ok_bind]
  apply check_of _ _ _ _ table
  rw [aligns,ok_bind]
  refine (congrArg (fun x => x >>= _) counterNew).trans ?_
  rw [ok_bind]
  exact (congrArg (fun x => x >>= fun _ => (pure () : Decode Unit)) tables).trans rfl

theorem decodeNode_recount (names : Allowedips.Names) (o : AllowedipsProbe.Offsets) (m : DataMem)
    (counter id a : Nat) :
    Allowedips.decodeNode (recount names counter) o m id a = Allowedips.decodeNode names o m id a := rfl

theorem peerList_recount (names : Allowedips.Names) (m : DataMem) (counter head fuel link previous : Nat)
    (seen : List Nat) :
    peerList (recount names counter) m head fuel link previous seen =
      peerList names m head fuel link previous seen := by
  induction fuel generalizing link previous seen with
  | zero => rfl
  | succ fuel ih =>
    unfold peerList
    simp only [ih]
    rfl

theorem decodePeer_recount (names : Allowedips.Names) (o : AllowedipsProbe.Offsets) (m : DataMem)
    (counter id a : Nat) :
    decodePeer (recount names counter) o m id a = decodePeer names o m id a := by
  unfold decodePeer
  simp only [peerList_recount]
  rfl

theorem reconstruct_recount {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem}
    {state : State} {counter : Nat} (grows : names.nextNode ≤ counter)
    (run : Allowedips.reconstruct names o m = .ok state) :
    Allowedips.reconstruct (recount names counter) o m = .ok {state with nextNode := counter} := by
  unfold Allowedips.reconstruct at run ⊢
  obtain ⟨_,valid,run⟩ := bind_ok run
  obtain ⟨w4,r4,run⟩ := bind_ok run
  obtain ⟨p4,q4,run⟩ := bind_ok run
  obtain ⟨w6,r6,run⟩ := bind_ok run
  obtain ⟨p6,q6,run⟩ := bind_ok run
  obtain ⟨seq,rs,run⟩ := bind_ok run
  obtain ⟨nodes,rn,run⟩ := bind_ok run
  obtain ⟨peers,rp,run⟩ := bind_ok run
  cases Except.ok.inj run
  rw [validate_recount grows valid,ok_bind]
  simp only [decodeNode_recount,decodePeer_recount]
  change (do
    let w ← word m "table.root4" (names.table+AllowedipsMutationLayout.root4) 8
    let root4 ← Trie.pointer names.trie.nodes "table.root4" w
    let w' ← word m "table.root6" (names.table+AllowedipsMutationLayout.root6) 8
    let root6 ← Trie.pointer names.trie.nodes "table.root6" w'
    let seq ← word m "table.seq" (names.table+AllowedipsMutationLayout.seq) 8
    let nodes ← names.trie.nodes.mapM fun (id,a) => Allowedips.decodeNode names o m id a
    let peers ← names.trie.peers.mapM fun (id,a) => decodePeer names o m id a
    (pure ⟨{root4,root6,seq := seq.toUInt64},nodes,peers,counter⟩ : Decode State)) = _
  rw [r4,ok_bind,q4,ok_bind,r6,ok_bind,q6,ok_bind,rs,ok_bind,rn,ok_bind,rp,ok_bind]
  rfl

theorem heap_recount (names : Allowedips.Names) (state : State) (m : DataMem) (counter : Nat) :
    Allowedips.heap (recount names counter) {state with nextNode := counter} m =
      Allowedips.heap names state m := rfl

/-- `C1Step.delete` is the landed model of `listDel`. -/
theorem delete_unlisted (d : Device) (id : NodeId) : delete d id = unlisted d id := by
  have fold : ∀ (xs : List (Nat × Peer)) (acc : Device),
      xs.foldl (fun d (entry : Nat × Peer) => if entry.2.allowedipsList.contains id then
        {d with peers := d.peers.insert entry.1 {entry.2 with allowedipsList := listRemove entry.2.allowedipsList id}}
        else d) acc = {acc with peers := delFold id xs acc.peers} := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
      intro acc
      rw [List.foldl_cons,ih]
      simp only [delFold,List.foldl_cons,delStep,unlist]
      split <;> rfl
  exact fold d.peers.toList d

private theorem unlist_absent {id : Nat} {p : Peer} (absent : id ∉ p.allowedipsList) : unlist id p = p := by
  have kept : p.allowedipsList.filter (· != id) = p.allowedipsList := by
    apply List.filter_eq_self.mpr
    intro a present
    simp only [bne_iff_ne]
    exact fun same => absent (same ▸ present)
  simp [unlist,WG.listRemove,kept]

private theorem unlist_appended {id : Nat} {p : Peer} (absent : id ∉ p.allowedipsList) :
    unlist id {p with allowedipsList := p.allowedipsList ++ [id]} = p := by
  have kept : p.allowedipsList.filter (· != id) = p.allowedipsList := by
    apply List.filter_eq_self.mpr
    intro a present
    simp only [bne_iff_ne]
    exact fun same => absent (same ▸ present)
  simp [unlist,WG.listRemove,kept]

/-- The mirror's device after the rollback is the device before it with the
allocation counter advanced: the node was allocated, listed, unlisted, freed. -/
theorem target_rollbackDevice {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem}
    {d : Device} (family key cidr pid : Nat)
    (related : Allowedips.Corresponds names o m (bump d)) :
    Allowedips.target (rollbackDevice d family key cidr pid) =
      {Allowedips.target (bump d) with nextNode := (bump d).nextNode + 1} := by
  have below := target_nodes_below related
  have unowned := fresh_not_owned related
  have absent : ∀ (q : Nat) (p : Peer), (bump d).peers[q]? = some p → (bump d).nextNode ∉ p.allowedipsList := by
    intro q p present
    exact unowned (q,p.refcount,p.allowedipsList)
      (List.mem_map.mpr ⟨(q,p),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present,rfl⟩)
  have vacant : (bump d).nodes[(bump d).nextNode]? = none := by
    cases present : (bump d).nodes[(bump d).nextNode]? with
    | none => rfl
    | some node =>
      exact absurd (below ((bump d).nextNode,node) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present))
        (Nat.lt_irrefl _)
  have shape : ∃ listed, attached d family key cidr pid =
        {alloc (bump d) (newNode key cidr (widthOf family) (some pid)) with peers := listed} ∧
      ∀ q : Nat, (listed[q]?).map (unlist (bump d).nextNode) = (bump d).peers[q]? := by
    unfold attached addTail
    cases present : (alloc (bump d) (newNode key cidr (widthOf family) (some pid))).peers.get? pid with
    | none =>
      refine ⟨(bump d).peers,rfl,fun q => ?_⟩
      cases other : (bump d).peers[q]? with
      | none => rfl
      | some p => simp only [Option.map_some,unlist_absent (absent q p other)]
    | some owner =>
      have held : (bump d).peers[pid]? = some owner := present
      refine ⟨_,rfl,fun q => ?_⟩
      change ((((bump d).peers.insert pid _)[q]?).map _) = _
      rw [Std.TreeMap.getElem?_insert]
      by_cases same : pid = q
      · subst same
        simp only [Nat.compare_eq_eq,↓reduceIte,Option.map_some,held]
        exact congrArg some (unlist_appended (absent pid owner held))
      · simp only [Nat.compare_eq_eq,same,↓reduceIte]
        cases other : (bump d).peers[q]? with
        | none => rfl
        | some p => simp only [Option.map_some,unlist_absent (absent q p other)]
  obtain ⟨listed,form,restored⟩ := shape
  have peers : (unlisted (attached d family key cidr pid) (bump d).nextNode).peers.Equiv (bump d).peers := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro q
    change (unlisted (attached d family key cidr pid) (bump d).nextNode).peers[q]? = (bump d).peers[q]?
    rw [unlisted_get,form]
    exact restored q
  have nodes : (((bump d).nodes.insert (bump d).nextNode (newNode key cidr (widthOf family) (some pid))).erase
      (bump d).nextNode).Equiv (bump d).nodes := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro q
    change (((bump d).nodes.insert _ _).erase _)[q]? = (bump d).nodes[q]?
    rw [Std.TreeMap.getElem?_erase]
    by_cases same : (bump d).nextNode = q
    · subst same
      simp only [Nat.compare_eq_eq,↓reduceIte,vacant]
    · simp only [Nat.compare_eq_eq,same,↓reduceIte,Std.TreeMap.getElem?_insert]
  unfold rollbackDevice Allowedips.target
  rw [delete_unlisted]
  have peersEq := peers.toList_eq
  have nodesEq := nodes.toList_eq
  rw [form] at peersEq ⊢
  simp only [unlisted,alloc] at peersEq ⊢
  rw [peersEq,nodesEq]

/-- THE ROLLBACK'S DATA SIDE. If memory agrees with the cut's on every byte
the old interpretation reads, the old interpretation with its counter
advanced relates it to `step`'s device for case `splitNoMem`. -/
theorem rollback_relation {names : Allowedips.Names} {m m' : DataMem} {d : Device}
    (family key cidr pid : Nat)
    (related : Allowedips.Corresponds names Root.nodeOffsets m (bump d))
    (shape : Allowedips.heap names (Allowedips.target (bump d)) m = .ok ())
    (same : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ a, span.contains a → m.get? a = m'.get? a) :
    Allowedips.Corresponds (recount names (names.nextNode+1)) Root.nodeOffsets m'
        (rollbackDevice d family key cidr pid) ∧
      Allowedips.heap (recount names (names.nextNode+1))
        (Allowedips.target (rollbackDevice d family key cidr pid)) m' = .ok () := by
  have outside : EqualOutside (fun a => m.get? a ≠ m'.get? a) m m' := fun a h => Classical.not_not.mp h
  have run : Allowedips.reconstruct names Root.nodeOffsets m' = .ok (Allowedips.target (bump d)) :=
    (reconstruct_frame names Root.nodeOffsets outside
      (fun span member a inside differ => differ (same span member a inside))).symm.trans related
  have counter : (bump d).nextNode = names.nextNode := (reconstruct_fields related).nextNode
  unfold Allowedips.Corresponds
  rw [target_rollbackDevice family key cidr pid related,counter]
  refine ⟨reconstruct_recount (Nat.le_succ _) run,?_⟩
  rw [heap_recount]
  exact (heap_frame names Root.nodeOffsets _ outside
    (fun span member a inside differ => differ (same span (Placement.metadata_read member) a inside))).symm.trans shape

#print axioms validate_recount
#print axioms reconstruct_recount
#print axioms delete_unlisted
#print axioms target_rollbackDevice
#print axioms rollback_relation
end Binary.Statements.C1.Proof
