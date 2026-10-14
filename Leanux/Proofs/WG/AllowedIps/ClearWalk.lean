import Leanux.Proofs.WG.AllowedIps.RoutingInvariant
import Leanux.Proofs.Framing.WGAllowedIps

/-! Source-order stack helpers for allowed-IP clearing. Root-list removal
pushes left then right; subtree enumeration pushes in the reverse order.
Coverage is extensional and never identifies those two traversal orders. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1500000
set_option pp.structureInstances false

def pushed (children : List (Option NodeId)) (stack : List NodeId) : List NodeId :=
  children.foldl (fun s c => match c with | none => s | some id => id :: s) stack

def pushChild (c : Option NodeId) (stack : List NodeId) : M (ForInStep (List NodeId)) := do
  if ← branch .pushRcuNonNull c.isSome then
    if let some c := c then return .yield (c :: stack)
  return .yield stack

def pushChildren (children : List (Option NodeId)) (initial : List NodeId) : M (List NodeId) :=
  forIn children initial pushChild

theorem pushed_mem (children : List (Option NodeId)) (stack : List NodeId) (id : Nat) :
    id ∈ pushed children stack ↔ id ∈ stack ∨ some id ∈ children := by
  induction children generalizing stack with
  | nil => simp [pushed]
  | cons c cs ih =>
    simp only [pushed, List.foldl_cons]
    change id ∈ pushed cs _ ↔ _
    rw [ih]
    cases c <;> simp <;> grind

theorem pushChild_wp (c : Option NodeId) (stack : List NodeId) (k : Kernel) :
    ⦃fun w => ⌜w.k = k⌝⦄ pushChild c stack
    ⦃⇓ result w => ⌜result = .yield (match c with | none => stack | some id => id :: stack) ∧ w.k = k⌝⦄ := by
  cases c <;> mvcgen [pushChild, branch]

theorem pushChildren_wp (children : List (Option NodeId)) (initial : List NodeId) (k : Kernel) :
    ⦃fun w => ⌜w.k = k⌝⦄ pushChildren children initial
    ⦃⇓ result w => ⌜result = pushed children initial ∧ w.k = k⌝⦄ := by
  mvcgen [pushChildren, pushChild_wp]
  invariants
  | inv1 => (fun cursor w => ⌜cursor.2 = pushed cursor.1.prefix initial ∧ w.k = k⌝, ExceptConds.false)
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [pushed, List.foldl_append]

def rootRemoveStep (_ : Nat) (state : Option Unit × List NodeId) :
    M (ForInStep (Option Unit × List NodeId)) := do
  match state.2 with
  | [] => do
    _ ← branch .rootRemoveLenPositive false
    return .done (some (), state.2)
  | id :: rest =>
    _ ← branch .rootRemoveLenPositive true
    _ ← branch .rootRemovePopped true
    let n ← getNode id
    let stack ← pushChildren n.bit.toList rest
    if ← branch .rootRemoveHasPeer n.peer.isSome then
      let some pid := n.peer | invariant "unreachable"
      if !(← getPeer pid).allowedipsList.contains id then invariant "trie node missing from its peer's list"
      listDel id
    return .yield (none, stack)

def rootRemoveSource (root : NodeId) : M Unit := do
  let out ← forIn [0:(← getDev).nodes.size + 1] (none, [root]) rootRemoveStep
  match out.1 with
  | some x => pure x
  | none => invariant "root_remove_peer_lists did not terminate"

theorem rootRemoveSource_eq (root : NodeId) : rootRemoveSource root = rootRemovePeerLists root := by
  unfold rootRemoveSource rootRemoveStep pushChildren pushChild rootRemovePeerLists
  simp only [bind_assoc]
  congr 1
  funext d
  congr 1
  funext out
  cases out.1 <;> rfl

/-- A resident list reference resolves to the actual raw node owner. Other
raw owner labels may have no resident peer. -/
def ListsOwned (d : Device) : Prop :=
  ∀ (pid : PeerId) (p : Peer), d.peers[pid]? = some p → ∀ id ∈ p.allowedipsList,
    ∃ n : AipNode, d.nodes[id]? = some n ∧ n.peer = some pid

theorem RoutingInvariant.listsOwned (hi : RoutingInvariant d t4 t6) : ListsOwned d := by
  intro pid p hp id hid
  obtain ⟨e, he, rfl, rfl⟩ := (hi.lists pid p hp).2 id |>.mp hid
  rcases List.mem_append.mp he with he | he
  · obtain ⟨n, hn⟩ := hi.forest.2.2.1.resident (Tree.entry_mem_nodeIds he)
    exact ⟨n, hn, by simpa [hn] using hi.forest.2.2.1.entry_owner he⟩
  · obtain ⟨n, hn⟩ := hi.forest.2.2.2.resident (Tree.entry_mem_nodeIds he)
    exact ⟨n, hn, by simpa [hn] using hi.forest.2.2.2.entry_owner he⟩

/-- Every processed child is either processed already or still pending. This
supports coverage even though the two source walks use opposite stack orders. -/
def Frontier (nodes : Std.TreeMap Nat AipNode) (root : NodeId)
    (visited stack : List NodeId) : Prop :=
  root ∈ visited ++ stack ∧ ∀ id ∈ visited, ∀ n : AipNode, nodes[id]? = some n →
    ∀ child, some child ∈ n.bit.toList → child ∈ visited ++ stack

theorem Frontier.start (nodes : Std.TreeMap Nat AipNode) (root : NodeId) : Frontier nodes root [] [root] := by
  simp [Frontier]

theorem Frontier.step {nodes : Std.TreeMap Nat AipNode} {root id : NodeId}
    {visited stack : List NodeId} {n : AipNode} (hf : Frontier nodes root visited (id :: stack))
    (hn : nodes[id]? = some n) : Frontier nodes root (id :: visited) (pushed n.bit.toList stack) := by
  have move (q : Nat) (hq : q ∈ visited ++ id :: stack) :
      q ∈ (id :: visited) ++ pushed n.bit.toList stack := by
    simp only [List.mem_append, List.mem_cons] at hq ⊢
    rcases hq with h | rfl | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr ((pushed_mem _ _ _).mpr (Or.inl h))
  refine ⟨move _ hf.1, ?_⟩
  intro q hq nq hqnode c hc
  rcases List.mem_cons.mp hq with rfl | hq
  · rw [hn] at hqnode
    cases hqnode
    exact List.mem_append_right _ ((pushed_mem _ _ _).mpr (Or.inr hc))
  · exact move _ (hf.2 q hq nq hqnode c hc)

theorem RepAt.closed_coverage {nodes : Std.TreeMap Nat AipNode} {width : Nat}
    {parent : Slot} {t : Tree} {visited : List NodeId} (hr : RepAt nodes width parent t)
    (closed : ∀ id ∈ visited, ∀ n : AipNode, nodes[id]? = some n →
      ∀ c, some c ∈ n.bit.toList → c ∈ visited)
    (root : ∀ id, t.root = some id → id ∈ visited) :
    ∀ id ∈ t.nodeIds, id ∈ visited := by
  induction t generalizing parent with
  | empty => simp [Tree.nodeIds]
  | node n l r il ir =>
    have hn : n.id ∈ visited := root n.id rfl
    have hl : ∀ id, l.root = some id → id ∈ visited := by
      intro id hid
      apply closed n.id hn _ hr.1 id
      simp [encode, hid]
    have hright : ∀ id, r.root = some id → id ∈ visited := by
      intro id hid
      apply closed n.id hn _ hr.1 id
      simp [encode, hid]
    intro id hid
    simp only [Tree.nodeIds, List.mem_cons, List.mem_append] at hid
    rcases hid with rfl | h | h
    · exact hn
    · exact il hr.2.1 hl id h
    · exact ir hr.2.2 hright id h

/-- Current resident lists still refer to the fixed node snapshot and exclude
all nodes already processed by the original walk. -/
def ClearProgress (nodes : Std.TreeMap Nat AipNode) (visited : List NodeId) (d : Device) : Prop :=
  d.nodes = nodes ∧ ∀ (pid : PeerId) (p : Peer), d.peers[pid]? = some p →
    ∀ id ∈ p.allowedipsList, id ∉ visited ∧ ∃ n : AipNode, nodes[id]? = some n ∧ n.peer = some pid

theorem ClearProgress.start (h : ListsOwned d) : ClearProgress d.nodes [] d := by
  exact ⟨rfl, fun pid p hp id hid => ⟨by simp, h pid p hp id hid⟩⟩

theorem ClearProgress.unlisted {nodes : Std.TreeMap Nat AipNode} {visited : List NodeId}
    {d : Device} (h : ClearProgress nodes visited d) (id : NodeId) :
    ClearProgress nodes (id :: visited) (unlisted d id) := by
  refine ⟨h.1, ?_⟩
  intro pid p hp q hq
  rw [unlisted_get] at hp
  cases hx : d.peers[pid]? with
  | none => simp [hx] at hp
  | some old =>
    simp only [hx, Option.map_some, Option.some.injEq] at hp
    subst p
    have hh : q ∈ old.allowedipsList ∧ q ≠ id := by
      simpa [unlist, WG.listRemove] using hq
    have ho := h.2 pid old hx q hh.1
    exact ⟨by simp [hh.2, ho.1], ho.2⟩

theorem ClearProgress.unowned {nodes : Std.TreeMap Nat AipNode} {visited : List NodeId}
    {d : Device} (h : ClearProgress nodes visited d) (id : NodeId) (n : AipNode)
    (hn : nodes[id]? = some n) (hp : n.peer = none) :
    ClearProgress nodes (id :: visited) d := by
  refine ⟨h.1, ?_⟩
  intro pid p hpeer q hq
  have ho := h.2 pid p hpeer q hq
  refine ⟨?_, ho.2⟩
  simp only [List.mem_cons, not_or]
  refine ⟨?_, ho.1⟩
  intro he
  subst q
  obtain ⟨nn, hh, hhpeer⟩ := ho.2
  rw [hn] at hh
  cases hh
  simp [hp] at hhpeer

/-- A proof-only state for the actual loop, with no totality requirement. -/
def ClearWalkInv (nodes : Std.TreeMap Nat AipNode) (root : NodeId)
    (state : Option Unit × List NodeId) (w : World) : Prop :=
  ∃ d visited, w.k.wg = some d ∧ ClearProgress nodes visited d ∧
    Frontier nodes root visited state.2 ∧ (state.1.isSome = true → state.2 = [])

theorem ClearWalkInv.finish (h : ClearWalkInv nodes root state w) (hs : state.2 = [])
    (hk : v.k.wg = w.k.wg) : ClearWalkInv nodes root (some (), []) v := by
  obtain ⟨d, seen, hd, hp, hf, _⟩ := h
  exact ⟨d, seen, hk.trans hd, hp, by simpa [hs] using hf, fun _ => rfl⟩

theorem ClearWalkInv.after_unlist {nodes : Std.TreeMap Nat AipNode} {root id : NodeId}
    {state : Option Unit × List NodeId} {w v : World} {rest : List NodeId} {d : Device} {n : AipNode}
    (h : ClearWalkInv nodes root state w) (hs : state.2 = id :: rest)
    (hd : w.k.wg = some d) (hn : d.nodes[id]? = some n)
    (hout : v.k.wg = some (unlisted d id)) :
    ClearWalkInv nodes root (none, pushed n.bit.toList rest) v := by
  obtain ⟨old, seen, hold, hp, hf, _⟩ := h
  have he : old = d := Option.some.inj (hold.symm.trans hd)
  subst old
  have hnode : nodes[id]? = some n := by rw [← hp.1]; exact hn
  refine ⟨unlisted d id, id :: seen, hout, hp.unlisted id, ?_, by simp⟩
  exact Frontier.step (by simpa [hs] using hf) hnode

theorem ClearWalkInv.after_unowned {nodes : Std.TreeMap Nat AipNode} {root id : NodeId}
    {state : Option Unit × List NodeId} {w v : World} {rest : List NodeId} {d : Device} {n : AipNode}
    (h : ClearWalkInv nodes root state w) (hs : state.2 = id :: rest)
    (hd : w.k.wg = some d) (hn : d.nodes[id]? = some n) (hnone : n.peer = none)
    (hout : v.k.wg = some d) :
    ClearWalkInv nodes root (none, pushed n.bit.toList rest) v := by
  obtain ⟨old, seen, hold, hp, hf, _⟩ := h
  have he : old = d := Option.some.inj (hold.symm.trans hd)
  subst old
  have hnode : nodes[id]? = some n := by rw [← hp.1]; exact hn
  refine ⟨d, id :: seen, hout, hp.unowned id n hnode hnone, ?_, by simp⟩
  exact Frontier.step (by simpa [hs] using hf) hnode

theorem rootRemoveStep_spec (nodes : Std.TreeMap Nat AipNode) (root : NodeId)
    (i : Nat) (state : Option Unit × List NodeId) :
    ⦃fun w => ⌜ClearWalkInv nodes root state w⌝⦄ rootRemoveStep i state
    ⦃⇓? result w => ⌜ClearWalkInv nodes root result.value w⌝⦄ := by
  have hl := listDel_wp
  have hc := pushChildren_wp
  mvcgen [rootRemoveStep, branch, getNode, getPeer, getDev, getK, invariant, hl, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all only [ForInStep.value]
  all_goals solve
    | apply ClearWalkInv.finish <;> first | assumption | rfl
    | apply ClearWalkInv.after_unlist <;> first | assumption | simp_all
    | apply ClearWalkInv.after_unowned <;> first | assumption | simp_all

/-- Normal completion supplies an empty pending stack. Exhaustion and missing
references remain Stops, with no returned failed World. -/
theorem rootRemove_spec (d : Device) (ho : ListsOwned d) (root : NodeId) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ rootRemoveSource root
    ⦃⇓? _ w => ⌜∃ out seen, w.k.wg = some out ∧ ClearProgress d.nodes seen out ∧
      Frontier d.nodes root seen []⌝⦄ := by
  have hs := rootRemoveStep_spec d.nodes root
  mvcgen [rootRemoveSource, getDev, getK, invariant, hs]
  invariants
  | inv1 => (fun cursor w => ⌜ClearWalkInv d.nodes root cursor.2 w⌝, ExceptConds.true)
  all_goals try dsimp +zetaDelta only at *
  case vc2.step.post.success =>
    rename_i r
    cases r <;> simp [ForInStep.value]
  case vc4.h_1.pre =>
    exact ⟨d, [], by assumption, ClearProgress.start ho, Frontier.start _ _, by simp⟩
  case vc5.h_1.post.success.h_1 =>
    rename_i before hbefore dd hdd state x hx finish hi
    obtain ⟨out, seen, hout, hp, hf, done⟩ := hi
    have hempty := done (by simp [hx])
    exact ⟨out, seen, hout, hp, by simpa [hempty] using hf⟩

/-- On a normal return, every node represented below this root has disappeared
from every resident peer list. Raw absent owners are permitted at entry; their
actual getter failure is not turned into a successful clear. -/
theorem rootRemove_lists (w v : World) (d : Device) (hd : w.k.wg = some d)
    (ho : ListsOwned d) (root : NodeId) (hr : t.root = some root)
    (hrep : RepAt d.nodes width parent t)
    (he : (rootRemovePeerLists root).run w = .ok ((), v)) :
    ∃ out, v.k.wg = some out ∧ out.nodes = d.nodes ∧
      ∀ (pid : PeerId) (p : Peer), out.peers[pid]? = some p →
        ∀ id ∈ t.nodeIds, id ∉ p.allowedipsList := by
  have hh := (hoare_iff_triple _ _ _).mpr (rootRemove_spec d ho root) w () v hd
    (by simpa only [rootRemoveSource_eq] using he)
  obtain ⟨out, seen, hout, hp, hf⟩ := hh
  have coverage : ∀ id ∈ t.nodeIds, id ∈ seen := hrep.closed_coverage
    (by simpa [Frontier] using hf.2)
    (by intro id hid; have hid' : id = root := Option.some.inj (hid.symm.trans hr); subst id; simpa using hf.1)
  refine ⟨out, hout, hp.1, ?_⟩
  intro pid p hpeer id hid hlist
  exact (hp.2 pid p hpeer id hlist).1 (coverage id hid)


/-- Full Kernel/device context and complete peer records, with only resident
allowed-IP lists hidden. Device and peer absence are retained. -/
def clearListView (w : World) : Kernel × (PeerId → Option Peer) :=
  ({w.k with wg := w.k.wg.map (fun d => {d with peers := {}})},
    fun pid => w.k.wg.bind (fun d => d.peers[pid]?.map (fun p => {p with allowedipsList := []})))

theorem listDel_clearListView (id : NodeId) : SameView clearListView (listDel id) := by
  intro w result v hr
  cases hd : w.k.wg with
  | none => simp [listDel, getDev, getK, invariant, hd] at hr
  | some d =>
    obtain ⟨r, finish, he, hh⟩ := (total_iff_run _ _ _).mp (listDel_wp w.k d hd id) w rfl
    rw [hr] at he
    cases he
    unfold clearListView
    rw [hh.2]
    apply Prod.ext
    · simp [unlisted, hd]
    · funext pid
      simp only [Option.bind_some, unlisted_get, Option.map_map, hd]
      cases d.peers[pid]? <;> rfl

theorem rootRemove_clearListView (root : NodeId) : SameView clearListView (rootRemovePeerLists root) := by
  apply SameView.of_wp
  intro initial
  have hn := fun id => (SameView.of_sameKernel (fun k =>
    ({k with wg := k.wg.map (fun d => {d with peers := {}})},
      fun pid : PeerId => k.wg.bind (fun d => d.peers[pid]?.map (fun p => {p with allowedipsList := []}))))
      (getNode_sameKernel id)).wp (fun s => s = initial)
  have hd := fun id => (listDel_clearListView id).wp (fun s => s = initial)
  have hl (α β : Type) := list_view_spec clearListView (α := α) (β := β) (fun s => s = initial)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, rootRemovePeerLists,
    hn, hd, getPeer, getDev, getK, invariant, branch]
  all_goals try exact ((⇓? _ w => ⌜clearListView w = initial⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [clearListView, ExceptConds.true, ExceptConds.const]


end Leanux.Proofs.WG.AllowedIps
