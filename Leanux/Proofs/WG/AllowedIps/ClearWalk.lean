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

def pushChild (c : Option NodeId) (stack : List NodeId) : WG.M (ForInStep (List NodeId)) := do
  if ← branch .pushRcuNonNull c.isSome then
    if let some c := c then return .yield (c :: stack)
  return .yield stack

def pushChildren (children : List (Option NodeId)) (initial : List NodeId) : WG.M (List NodeId) :=
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

theorem pushChild_wp (c : Option NodeId) (stack : List NodeId) (k : WGStoreView) :
    ⦃fun w => ⌜wgStoreView w = k⌝⦄ pushChild c stack
    ⦃⇓ result w => ⌜result = .yield (match c with | none => stack | some id => id :: stack) ∧ wgStoreView w = k⌝⦄ := by

  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hw
  refine ⟨_, w, record ambient .pushRcuNonNull c.isSome, ?_, rfl, hw⟩
  cases c <;> rfl

theorem pushChildren_wp (children : List (Option NodeId)) (initial : List NodeId) (k : WGStoreView) :
    ⦃fun w => ⌜wgStoreView w = k⌝⦄ pushChildren children initial
    ⦃⇓ result w => ⌜result = pushed children initial ∧ wgStoreView w = k⌝⦄ := by

  induction children generalizing initial with
  | nil =>
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hw
    exact ⟨initial, w, ambient, rfl, rfl, hw⟩
  | cons c cs ih =>
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hw
    obtain ⟨result, current, nextAmbient, he, hv, hk⟩ :=
      (total_iff_run_ambient _ _ _).mp (pushChild_wp c initial k) w ambient hw
    subst result
    obtain ⟨result, out, finalAmbient, htail, hr, hs⟩ :=
      (total_iff_run_ambient _ _ _).mp (ih _) current nextAmbient hk
    refine ⟨result, out, finalAmbient, ?_, hr, hs⟩
    simp only [pushChildren, List.forIn_cons, StateT.run_bind, he]
    exact htail

def rootRemoveStep (_ : Nat) (state : Option Unit × List NodeId) :
    WG.M (ForInStep (Option Unit × List NodeId)) := do
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

def rootRemoveSource (root : NodeId) : WG.M Unit := do
  let out ← forIn [0:(← getDev).nodes.size + 1] (none, [root]) rootRemoveStep
  match out.1 with
  | some x => pure x
  | none => invariant "root_remove_peer_lists did not terminate"

theorem rootRemoveSource_eq (root : NodeId) : rootRemoveSource root = rootRemovePeerLists root := by
  unfold rootRemoveSource rootRemoveStep pushChildren pushChild rootRemovePeerLists
  simp only []
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
    (state : Option Unit × List NodeId) (w : WGWorld) : Prop :=
  ∃ d visited, w.dev = some d ∧ ClearProgress nodes visited d ∧
    Frontier nodes root visited state.2 ∧ (state.1.isSome = true → state.2 = [])

theorem ClearWalkInv.finish (h : ClearWalkInv nodes root state w) (hs : state.2 = [])
    (hk : v.dev = w.dev) : ClearWalkInv nodes root (some (), []) v := by
  obtain ⟨d, seen, hd, hp, hf, _⟩ := h
  exact ⟨d, seen, hk.trans hd, hp, by simpa [hs] using hf, fun _ => rfl⟩

theorem ClearWalkInv.after_unlist {nodes : Std.TreeMap Nat AipNode} {root id : NodeId}
    {state : Option Unit × List NodeId} {w v : WGWorld} {rest : List NodeId} {d : Device} {n : AipNode}
    (h : ClearWalkInv nodes root state w) (hs : state.2 = id :: rest)
    (hd : w.dev = some d) (hn : d.nodes[id]? = some n)
    (hout : v.dev = some (unlisted d id)) :
    ClearWalkInv nodes root (none, pushed n.bit.toList rest) v := by
  obtain ⟨old, seen, hold, hp, hf, _⟩ := h
  have he : old = d := Option.some.inj (hold.symm.trans hd)
  subst old
  have hnode : nodes[id]? = some n := by rw [← hp.1]; exact hn
  refine ⟨unlisted d id, id :: seen, hout, hp.unlisted id, ?_, by simp⟩
  exact Frontier.step (by simpa [hs] using hf) hnode

theorem ClearWalkInv.after_unowned {nodes : Std.TreeMap Nat AipNode} {root id : NodeId}
    {state : Option Unit × List NodeId} {w v : WGWorld} {rest : List NodeId} {d : Device} {n : AipNode}
    (h : ClearWalkInv nodes root state w) (hs : state.2 = id :: rest)
    (hd : w.dev = some d) (hn : d.nodes[id]? = some n) (hnone : n.peer = none)
    (hout : v.dev = some d) :
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

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result out ambient' hi hr
  obtain ⟨d, seen, hd, hp, hf, hdone⟩ := hi
  have start : ClearWalkInv nodes root state w := ⟨d, seen, hd, hp, hf, hdone⟩
  cases hs : state.2 with
  | nil =>
    simp [rootRemoveStep, hs, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact start.finish hs rfl
  | cons id rest =>
    cases hn : d.nodes[id]? with
    | none =>
      have hread (a : Ambient) :
          ((liftAip (getNode id)).run w).run a =
            .error (.invariant ("dangling allowedips node " ++ Nat.repr id)) := by
        rw [liftAip_run, hd]
        simp [getNode, hn, invariant, AmbientM.invariant, Except.map]
        rfl
      simp [rootRemoveStep, hs, branch, AmbientM.branch, liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, hread] at hr
    | some n =>
      have hread (a : Ambient) : ((liftAip (getNode id)).run w).run a = .ok ((n, w), a) := by
        rw [liftAip_run, hd]
        simp [getNode, hn, Except.map, ← hd]
      let firstAmbient := record (record ambient .rootRemoveLenPositive true) .rootRemovePopped true
      obtain ⟨stack, current, nextAmbient, hpush, hstack, hstore⟩ :=
        (total_iff_run_ambient _ _ _).mp
          (pushChildren_wp n.bit.toList rest (wgStoreView w)) w firstAmbient rfl
      subst stack
      dsimp only [firstAmbient, record] at hpush
      have hdev : current.dev = some d :=
        (congrArg WGStoreView.dev hstore).trans hd
      cases howner : n.peer with
      | none =>
        simp [rootRemoveStep, hs, branch, AmbientM.branch, liftM, MonadLiftT.monadLift, MonadLift.monadLift, hread,
          StateT.run_bind, hpush, howner] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact start.after_unowned hs hd hn howner hdev
      | some pid =>
        cases hpeer : d.peers[pid]? with
        | none =>
          simp [rootRemoveStep, hs, branch, AmbientM.branch, liftM, MonadLiftT.monadLift, MonadLift.monadLift, hread,
            StateT.run_bind, hpush, howner, getPeer, getDev, hdev, hpeer,
            invariant, AmbientM.invariant] at hr
          cases hr
        | some peer =>
          by_cases hmem : id ∈ peer.allowedipsList
          · obtain ⟨returned, finish, finalAmbient, hlist, hunit, hfinish⟩ :=
              (total_iff_run_ambient _ _ _).mp (listDel_wp current d hdev id)
                current (record nextAmbient .rootRemoveHasPeer true) rfl
            subst returned
            subst finish
            dsimp only [record] at hlist
            simp [rootRemoveStep, hs, branch, AmbientM.branch, liftM, MonadLiftT.monadLift, MonadLift.monadLift, hread,
              StateT.run_bind, hpush, howner, getPeer, getDev, hdev, hpeer,
              hmem, hlist] at hr
            rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
            exact start.after_unlist hs hd hn rfl
          · simp [rootRemoveStep, hs, branch, AmbientM.branch, liftM, MonadLiftT.monadLift, MonadLift.monadLift, hread,
              StateT.run_bind, hpush, howner, getPeer, getDev, hdev, hpeer,
              hmem, invariant, AmbientM.invariant] at hr
            cases hr

/-- Normal completion supplies an empty pending stack. Exhaustion and missing
references remain Stops, with no returned failed WGWorld. -/
theorem rootRemove_spec (d : Device) (ho : ListsOwned d) (root : NodeId) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ rootRemoveSource root
    ⦃⇓? _ w => ⌜∃ out seen, w.dev = some out ∧ ClearProgress d.nodes seen out ∧
      Frontier d.nodes root seen []⌝⦄ := by

  have loop :
      Hoare (forIn [0:d.nodes.size + 1] (none, [root]) rootRemoveStep)
        (ClearWalkInv d.nodes root (none, [root])) (ClearWalkInv d.nodes root) := by
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    let inv : PostCond (Option Unit × List NodeId) (.arg WGWorld (.arg Ambient (.except Stop .pure))) :=
      (⇓? state w => ⌜ClearWalkInv d.nodes root state w⌝)
    refine Std.Do.Spec.forIn_list_const_inv (inv := inv) ?_
    intro i state
    apply Triple.entails_wp_of_post (rootRemoveStep_spec d.nodes root i state)
    constructor
    · intro result; cases result <;> exact .rfl
    · exact .rfl
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result out ambient' hd hr
  have start : ClearWalkInv d.nodes root (none, [root]) w :=
    ⟨d, [], hd, ClearProgress.start ho, Frontier.start _ _, by simp⟩
  have hget : (getDev.run w).run ambient = .ok ((d, w), ambient) := by simp [getDev, hd]
  simp only [rootRemoveSource, StateT.run_bind, hget] at hr
  cases he : ((forIn [0:d.nodes.size + 1] (none, [root]) rootRemoveStep).run w).run ambient with
  | error e =>
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at he
    simp [he] at hr
  | ok result' =>
    rcases result' with ⟨⟨state, current⟩, nextAmbient⟩
    have hi := (hoare_iff_run_ambient _ _ _).mp loop w ambient state current nextAmbient start he
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at he
    cases hs : state.1 with
    | none =>
      simp [he, hs, invariant, AmbientM.invariant] at hr
      cases hr
    | some value =>
      cases value
      simp [he, hs] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      obtain ⟨finish, seen, hout, hp, hf, done⟩ := hi
      have hempty := done (by simp [hs])
      exact ⟨finish, seen, hout, hp, by simpa [hempty] using hf⟩

/-- On a normal return, every node represented below this root has disappeared
from every resident peer list. Raw absent owners are permitted at entry; their
actual getter failure is not turned into a successful clear. -/
theorem rootRemove_lists (w v : WGWorld) (ambient ambient' : Ambient) (d : Device) (hd : w.dev = some d)
    (ho : ListsOwned d) (root : NodeId) (hr : t.root = some root)
    (hrep : RepAt d.nodes width parent t)
    (he : ((rootRemovePeerLists root).run w).run ambient = .ok (((), v), ambient')) :
    ∃ out, v.dev = some out ∧ out.nodes = d.nodes ∧
      ∀ (pid : PeerId) (p : Peer), out.peers[pid]? = some p →
        ∀ id ∈ t.nodeIds, id ∉ p.allowedipsList := by
  have hh := (hoare_iff_run_ambient _ _ _).mp (rootRemove_spec d ho root) w ambient () v ambient' hd
    (by simpa only [rootRemoveSource_eq] using he)
  obtain ⟨out, seen, hout, hp, hf⟩ := hh
  have coverage : ∀ id ∈ t.nodeIds, id ∈ seen := hrep.closed_coverage
    (by simpa [Frontier] using hf.2)
    (by intro id hid; have hid' : id = root := Option.some.inj (hid.symm.trans hr); subst id; simpa using hf.1)
  refine ⟨out, hout, hp.1, ?_⟩
  intro pid p hpeer id hid hlist
  exact (hp.2 pid p hpeer id hlist).1 (coverage id hid)


/-- The original seven-field WG store observation and complete peer records,
with resident allowed-IP lists hidden. Device and peer absence are retained. -/
def clearListView (w : WGWorld) : WGStoreView × (PeerId → Option Peer) :=
  ({wgStoreView w with dev := w.dev.map (fun d => {d with peers := {}})},
    fun pid => w.dev.bind (fun d => d.peers[pid]?.map (fun p => {p with allowedipsList := []})))

theorem listDel_clearListView (id : NodeId) : SameView clearListView (listDel id) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  cases hd : w.dev with
  | none =>
    simp [listDel, getDev, invariant, AmbientM.invariant, hd] at hr
    change (Except.error (.invariant "no WireGuard device in this trace's fixture") :
      Except Stop ((Unit × WGWorld) × Ambient)) = .ok ((result, v), ambient') at hr
    cases hr
  | some d =>
    obtain ⟨r, finish, finalAmbient, he, hh⟩ :=
      (total_iff_run_ambient _ _ _).mp (listDel_wp w d hd id) w ambient rfl
    rw [hr] at he
    cases he
    unfold clearListView
    rw [hh.2]
    apply Prod.ext
    · simp [wgStoreView, unlisted, hd]
    · funext pid
      simp only [Option.bind_some, unlisted_get, Option.map_map, hd]
      cases d.peers[pid]? <;> rfl

theorem rootRemove_clearListView (root : NodeId) : SameView clearListView (rootRemovePeerLists root) := by
  apply SameView.of_wp
  intro initial
  have hn (id : NodeId) :
      ⦃fun w => ⌜clearListView w = initial⌝⦄
        (MonadLift.monadLift (getNode id) : WG.M AipNode)
      ⦃⇓? _ w => ⌜clearListView w = initial⌝⦄ := by
    apply hoare_liftAip_of
    intro g d hg hd
    apply hoare_consequence ((getNode_sameAipStore id).wp
      (fun s => s = {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}))
    · intro s hs; exact hs
    · intro _ s hs
      subst s
      change clearListView {g with dev := some d} = initial
      rw [← hd]
      exact hg
  let P : WGWorld → Prop := fun w => clearListView w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (StateT.lift a) :=
    hoare_liftAmbient a P
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind (hoare_consequence (hoare_get P)
      (fun _ h => h) (fun _ _ h => h.2))
    intro w
    cases w.dev
    · exact ambient (AmbientM.invariant _)
    · exact preserves_pure _
  have peer (id : PeerId) : Preserves P (getPeer id) := by
    unfold getPeer
    apply preserves_bind device
    intro d
    cases d.peers.get? id
    · exact ambient (AmbientM.invariant _)
    · exact preserves_pure _
  have push (children : List (Option NodeId)) (stack : List NodeId) :
      Preserves P (pushChildren children stack) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result out b hp hr
    obtain ⟨value, finish, finalAmbient, he, _, hk⟩ :=
      (total_iff_run_ambient _ _ _).mp
        (pushChildren_wp children stack (wgStoreView w)) w a rfl
    rw [hr] at he
    cases he
    have hdev := congrArg WGStoreView.dev hk
    change out.dev = w.dev at hdev
    simpa only [P, clearListView, hk, hdev] using hp
  have step (i : Nat) (state : Option Unit × List NodeId) :
      Preserves P (rootRemoveStep i state) := by
    unfold rootRemoveStep
    cases state.2 with
    | nil =>
      apply preserves_bind (ambient (AmbientM.branch _ _))
      intro _
      exact preserves_pure _
    | cons id rest =>
      apply preserves_bind (ambient (AmbientM.branch _ _))
      intro _
      apply preserves_bind (ambient (AmbientM.branch _ _))
      intro _
      apply preserves_bind (hn id)
      intro n
      apply preserves_bind (push n.bit.toList rest)
      intro stack
      apply preserves_bind (ambient (AmbientM.branch _ _))
      intro hasPeer
      cases hasPeer with
      | false => exact preserves_pure _
      | true =>
        cases n.peer with
        | none => exact ambient (AmbientM.invariant _)
        | some pid =>
          apply preserves_bind (peer pid)
          intro p
          split
          · exact ambient (AmbientM.invariant _)
          · apply preserves_bind ((listDel_clearListView id).wp (fun s => s = initial))
            intro _
            exact preserves_pure _
  rw [← rootRemoveSource_eq]
  unfold rootRemoveSource
  apply preserves_bind device
  intro d
  apply preserves_bind (a := forIn [0:d.nodes.size + 1] (none, [root]) rootRemoveStep)
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    exact list_view_spec (fun w : WGWorld => w) P _ _ _ step
  · intro state
    cases state.1
    · exact ambient (AmbientM.invariant _)
    · exact preserves_pure _

end Leanux.Proofs.WG.AllowedIps
