import Leanux.Proofs.WG.AllowedIps.ClearWalk

/-! Normal root clearing against a fixed original node snapshot. Current nodes
may have been erased by an earlier family, but every surviving value is unchanged.
A retained list predicate carries provenance and completed-family exclusions. -/
namespace Leanux.Proofs.WG.AllowedIps.ClearSnapshot
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1500000
set_option pp.structureInstances false

def NodesFrom (original current : Std.TreeMap Nat AipNode) : Prop :=
  ∀ (id : NodeId) (n : AipNode), current[id]? = some n → original[id]? = some n

theorem NodesFrom.refl (nodes : Std.TreeMap Nat AipNode) : NodesFrom nodes nodes :=
  fun _ _ h => h

theorem NodesFrom.erase (h : NodesFrom original current) (id : NodeId) :
    NodesFrom original (current.erase id) := by
  intro q n hn
  by_cases he : id = q
  · simp [he] at hn
  · exact h q n (by simpa [Std.TreeMap.getElem?_erase, he] using hn)

def Progress (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (visited : List NodeId) (d : Device) : Prop :=
  NodesFrom nodes d.nodes ∧ ∀ pid p, d.peers[pid]? = some p →
    ∀ id ∈ p.allowedipsList, P pid id ∧ id ∉ visited ∧
      ∃ n : AipNode, nodes[id]? = some n ∧ n.peer = some pid

theorem Progress.mono (h : Progress nodes P seen d)
    (hp : ∀ pid id, P pid id → Q pid id) : Progress nodes Q seen d := by
  refine ⟨h.1, ?_⟩
  intro pid p hpeer id hid
  have hh := h.2 pid p hpeer id hid
  exact ⟨hp pid id hh.1, hh.2⟩

theorem Progress.erase (h : Progress nodes P seen d) (id : NodeId) :
    Progress nodes P seen {d with nodes := d.nodes.erase id} :=
  ⟨h.1.erase id, h.2⟩

theorem Progress.unlisted (h : Progress nodes P seen d) (id : NodeId) :
    Progress nodes P (id :: seen) (unlisted d id) := by
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
    exact ⟨ho.1, by simp [hh.2, ho.2.1], ho.2.2⟩

theorem Progress.unowned (h : Progress nodes P seen d) (id : NodeId) (n : AipNode)
    (hn : nodes[id]? = some n) (hp : n.peer = none) : Progress nodes P (id :: seen) d := by
  refine ⟨h.1, ?_⟩
  intro pid p hpeer q hq
  have ho := h.2 pid p hpeer q hq
  refine ⟨ho.1, ?_, ho.2.2⟩
  simp only [List.mem_cons, not_or]
  refine ⟨?_, ho.2.1⟩
  intro he
  subst q
  obtain ⟨nn, hh, hhpeer⟩ := ho.2.2
  rw [hn] at hh
  cases hh
  simp [hp] at hhpeer

def WalkInv (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (root : NodeId) (state : Option Unit × List NodeId) (w : WGWorld) : Prop :=
  ∃ d seen, w.dev = some d ∧ Progress nodes P seen d ∧
    Frontier nodes root seen state.2 ∧ (state.1.isSome = true → state.2 = [])

theorem WalkInv.finish (h : WalkInv nodes P root state w) (hs : state.2 = [])
    (hk : v.dev = w.dev) : WalkInv nodes P root (some (), []) v := by
  obtain ⟨d, seen, hd, hp, hf, _⟩ := h
  exact ⟨d, seen, hk.trans hd, hp, by simpa [hs] using hf, fun _ => rfl⟩

theorem WalkInv.after_unlist {id : NodeId} {rest : List NodeId} {n : AipNode}
    (h : WalkInv nodes P root state w) (hs : state.2 = id :: rest)
    (hd : w.dev = some d) (hn : d.nodes[id]? = some n)
    (hout : v.dev = some (unlisted d id)) :
    WalkInv nodes P root (none, pushed n.bit.toList rest) v := by
  obtain ⟨old, seen, hold, hp, hf, _⟩ := h
  have he : old = d := Option.some.inj (hold.symm.trans hd)
  subst old
  refine ⟨unlisted d id, id :: seen, hout, hp.unlisted id, ?_, by simp⟩
  exact Frontier.step (by simpa [hs] using hf) (hp.1 id n hn)

theorem WalkInv.after_unowned {id : NodeId} {rest : List NodeId} {n : AipNode}
    (h : WalkInv nodes P root state w) (hs : state.2 = id :: rest)
    (hd : w.dev = some d) (hn : d.nodes[id]? = some n) (hnone : n.peer = none)
    (hout : v.dev = some d) : WalkInv nodes P root (none, pushed n.bit.toList rest) v := by
  obtain ⟨old, seen, hold, hp, hf, _⟩ := h
  have he : old = d := Option.some.inj (hold.symm.trans hd)
  subst old
  have hn' := hp.1 id n hn
  exact ⟨d, id :: seen, hout, hp.unowned id n hn' hnone,
    Frontier.step (by simpa [hs] using hf) hn', by simp⟩

theorem step_spec (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (root : NodeId) (i : Nat) (state : Option Unit × List NodeId) :
    ⦃fun w => ⌜WalkInv nodes P root state w⌝⦄ rootRemoveStep i state
    ⦃⇓? result w => ⌜WalkInv nodes P root result.value w⌝⦄ := by
  have hl := listDel_wp
  have hc := pushChildren_wp
  have hn (id : NodeId) (g : WGWorld) :
      Hoare (MonadLift.monadLift (getNode id) : WG.M AipNode)
        (fun w => w = g)
        (fun n w => w = g ∧ ∃ d, g.dev = some d ∧ d.nodes[id]? = some n) := by
    apply hoare_liftAip_of
    intro entry d hentry hd
    subst entry
    unfold Hoare
    mvcgen [getNode, invariant, AmbientM.invariant]
    all_goals simp_all
    change {g with dev := some d} = g
    rw [← hd]
  unfold Hoare at hn
  mvcgen [rootRemoveStep, branch, AmbientM.branch, hn, getPeer, getDev, invariant, AmbientM.invariant, hl, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all only [ForInStep.value]
  all_goals try solve | apply WalkInv.finish <;> first | assumption | rfl
  all_goals obtain ⟨he, d, hdev, hnode⟩ := ‹_ = _ ∧ ∃ d, _ = some d ∧ _›
  all_goals obtain ⟨hstack, hstore⟩ := ‹_ = pushed _ _ ∧ _›
  all_goals have hstoredev := congrArg WGStoreView.dev hstore
  all_goals dsimp only [wgStoreView] at hstoredev
  all_goals subst_vars
  all_goals try simp_all
  all_goals solve
    | apply WalkInv.after_unlist <;> first | assumption | simp_all
    | apply WalkInv.after_unowned <;> first | assumption | simp_all

theorem root_spec (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (d : Device) (ho : Progress nodes P [] d) (root : NodeId) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ rootRemoveSource root
    ⦃⇓? _ w => ⌜∃ out seen, w.dev = some out ∧ Progress nodes P seen out ∧
      Frontier nodes root seen []⌝⦄ := by
  have hs := step_spec nodes P root
  mvcgen [rootRemoveSource, getDev, invariant, AmbientM.invariant, hs]
  invariants
  | inv1 => (fun cursor w => ⌜WalkInv nodes P root cursor.2 w⌝, ExceptConds.true)
  all_goals try dsimp +zetaDelta only at *
  case vc2.step.post.success =>
    rename_i r
    cases r <;> simp [ForInStep.value]
  case vc4.h_1.pre =>
    exact ⟨d, [], by assumption, ho, Frontier.start _ _, by simp⟩
  case vc5.h_1.post.success.h_1 =>
    rename_i before hbefore dd hdd state x hx finish hi
    obtain ⟨out, seen, hout, hp, hf, done⟩ := hi
    have hempty := done (by simp_all)
    exact ⟨out, seen, hout, hp, by simpa [hempty] using hf⟩

/-- Only normal root completion adds the represented-family exclusion. The
original map may include absent owners and the current map may omit old nodes. -/
theorem root_normal (w v : WGWorld) (ambient ambient' : Ambient) (nodes : Std.TreeMap Nat AipNode)
    (P : PeerId → NodeId → Prop) (d : Device) (hd : w.dev = some d)
    (ho : Progress nodes P [] d) (root : NodeId) (hroot : t.root = some root)
    (hrep : RepAt nodes width parent t)
    (hr : ((rootRemovePeerLists root).run w).run ambient = .ok (((), v), ambient')) :
    ∃ out, v.dev = some out ∧
      Progress nodes (fun pid id => P pid id ∧ id ∉ t.nodeIds) [] out := by
  have hh := (hoare_iff_run_ambient _ _ _).mp (root_spec nodes P d ho root) w ambient () v ambient' hd
    (by simpa only [rootRemoveSource_eq] using hr)
  obtain ⟨out, seen, hout, hp, hf⟩ := hh
  have coverage : ∀ id ∈ t.nodeIds, id ∈ seen := hrep.closed_coverage
    (by simpa [Frontier] using hf.2)
    (by intro id hid; have he : id = root := Option.some.inj (hid.symm.trans hroot); subst id; simpa using hf.1)
  refine ⟨out, hout, hp.1, ?_⟩
  intro pid p hpeer id hid
  have hh := hp.2 pid p hpeer id hid
  exact ⟨⟨hh.1, fun hm => hh.2.1 (coverage id hm)⟩, by simp, hh.2.2⟩

end Leanux.Proofs.WG.AllowedIps.ClearSnapshot
