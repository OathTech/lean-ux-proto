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

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result out ambient' hi hr
  obtain ⟨d, seen, hd, hp, hf, hdone⟩ := hi
  have start : WalkInv nodes P root state w := ⟨d, seen, hd, hp, hf, hdone⟩
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


theorem root_spec (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (d : Device) (ho : Progress nodes P [] d) (root : NodeId) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ rootRemoveSource root
    ⦃⇓? _ w => ⌜∃ out seen, w.dev = some out ∧ Progress nodes P seen out ∧
      Frontier nodes root seen []⌝⦄ := by

  have loop :
      Hoare (forIn [0:d.nodes.size + 1] (none, [root]) rootRemoveStep)
        (WalkInv nodes P root (none, [root])) (WalkInv nodes P root) := by
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    let inv : PostCond (Option Unit × List NodeId) (.arg WGWorld (.arg Ambient (.except Stop .pure))) :=
      (⇓? state w => ⌜WalkInv nodes P root state w⌝)
    refine Std.Do.Spec.forIn_list_const_inv (inv := inv) ?_
    intro i state
    apply Triple.entails_wp_of_post (step_spec nodes P root i state)
    constructor
    · intro result; cases result <;> exact .rfl
    · exact .rfl
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result out ambient' hd hr
  have start : WalkInv nodes P root (none, [root]) w :=
    ⟨d, [], hd, ho, Frontier.start _ _, by simp⟩
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
