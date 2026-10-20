import Leanux.Proofs.WG.AllowedIps.RemovalLoop

/-! Complete original peer removal from explicitly coherent resident lists.
This is a conditional operation theorem, not initialized history closure. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

private theorem run_bind_eq {S : Type} {m : Type → Type} [Monad m]
    (f : StateT S m α) (g : α → StateT S m β) (w : S) :
    (f >>= g).run w = (f.run w >>= fun (a, w') => (g a).run w') := rfl

theorem RepAt.entry_owner (hr : RepAt nodes width parent t) (he : e ∈ t.entries) :
    (nodes[e.id]?).bind WG.AipNode.peer = some e.peer := by
  induction t generalizing parent with
  | empty => simp [Tree.entries] at he
  | node n l r il ir =>
    simp only [Tree.entries, List.mem_append] at he
    rcases he with (he | he) | he
    · cases hp : n.peer <;> simp [NodeData.entries, NodeData.own, hp] at he
      subst e
      simp [NodeData.entry, hr.1, encode, hp]
    · exact il hr.2.1 he
    · exact ir hr.2.2 he

theorem forest_entry_owner (hf : ForestRep d t4 t6) (he : e ∈ t4.entries ++ t6.entries) :
    (d.nodes[e.id]?).bind WG.AipNode.peer = some e.peer := by
  rcases List.mem_append.mp he with he | he
  · exact hf.2.2.1.entry_owner he
  · exact hf.2.2.2.entry_owner he

theorem resident_saved_iff_owner (hf : ForestRep d t4 t6) (hc : ResidentLists d t4 t6)
    (hp : d.peers[pid]? = some p) (he : e ∈ t4.entries ++ t6.entries) :
    e.id ∈ p.allowedipsList ↔ e.peer = pid := by
  constructor
  · intro hi
    obtain ⟨other, ho, hid, hpid⟩ := ((hc pid p hp).2 e.id).mp hi
    have h := forest_entry_owner hf ho
    rw [hid, forest_entry_owner hf he] at h
    exact (Option.some.inj h).trans hpid
  · intro hpid
    exact ((hc pid p hp).2 e.id).mpr ⟨e, he, rfl, hpid⟩

def removalStart (d : WG.Device) (ids : List Nat) : WG.Device :=
  if ids.isEmpty then d else
    {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}}

theorem removalStart_forest (hf : ForestRep d t4 t6) (ids : List Nat) :
    ForestRep (removalStart d ids) t4 t6 := by
  cases ids <;> exact hf

theorem removalStart_lists (hc : ResidentLists d t4 t6) (ids : List Nat) :
    ResidentLists (removalStart d ids) t4 t6 := by
  cases ids <;> exact hc

/-- The start state changes only the sequence, and only for a nonempty
saved list. The loop contract records the complete subsequent mutation. -/
structure RemovedPeer (d out : WG.Device) (t4 t6 : Tree) (pid : Nat) (saved : List Nat) : Prop where
  loop : RemovedIds (removalStart d saved) out t4 t6 saved
  coherent : ResidentLists out (t4.eraseIds saved) (t6.eraseIds saved)
  entries : (t4.eraseIds saved).entries ++ (t6.eraseIds saved).entries =
    (t4.entries ++ t6.entries).filter (fun e => e.peer != pid)

theorem RemovedPeer.seq (h : RemovedPeer d out t4 t6 pid saved) :
    out.peerAllowedips.seq = d.peerAllowedips.seq + (if saved.isEmpty then 0 else 1) := by
  rw [h.loop.seq]
  cases saved <;> simp [removalStart]

theorem RemovedPeer.peers (h : RemovedPeer d out t4 t6 pid saved) (q : Nat) :
    out.peers[q]? = (d.peers[q]?).map (unlistIds saved) := by
  have hm := h.loop.peers q
  cases saved <;> exact hm

theorem RemovedPeer.frame (h : RemovedPeer d out t4 t6 pid saved) :
    out = {d with nodes := out.nodes, peers := out.peers, peerAllowedips := out.peerAllowedips} := by
  have hm := h.loop.frame
  cases saved <;> exact hm

theorem RemovedPeer.nextNode (h : RemovedPeer d out t4 t6 pid saved) : out.nextNode = d.nextNode := by
  have hm := h.loop.nextNode
  cases saved <;> exact hm

theorem RemovedPeer.below (h : RemovedPeer d out t4 t6 pid saved) (hb : NodesBelow d) :
    NodesBelow out := by
  apply h.loop.below
  cases saved <;> exact hb

theorem RemovedPeer.outside (h : RemovedPeer d out t4 t6 pid saved)
    (hq : q ∉ t4.nodeIds ++ t6.nodeIds) : out.nodes[q]? = d.nodes[q]? := by
  have hm := h.loop.outside q hq
  cases saved <;> exact hm

theorem RemovedPeer.target_empty (h : RemovedPeer d out t4 t6 pid p.allowedipsList)
    (hp : d.peers[pid]? = some p) :
    out.peers[pid]? = some {p with allowedipsList := []} := by
  rw [h.peers, hp, Option.map_some]
  simp [unlistIds, List.filter_eq_nil_iff]

theorem RemovedPeer.no_target_entry (h : RemovedPeer d out t4 t6 pid saved) :
    ∀ e ∈ (t4.eraseIds saved).entries ++ (t6.eraseIds saved).entries, e.peer ≠ pid := by
  intro e he
  rw [h.entries] at he
  exact by simpa using (List.mem_filter.mp he).2

theorem removeByPeer_total (w : WGWorld) (ambient : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed) (hl : ResidentLists d t4 t6) :
    ∃ out w' ambient', ((WG.removeByPeer pid).run w).run ambient = .ok (((), w'), ambient') ∧
      w' = {w with dev := some out} ∧ RemovedPeer d out t4 t6 pid p.allowedipsList := by
  have hs : OwnedIds p.allowedipsList t4 t6 := by
    intro id hi
    obtain ⟨e, he, hi, _⟩ := ((hl pid p hp).2 id).mp hi
    exact ⟨e, he, hi⟩
  have entries : (t4.eraseIds p.allowedipsList).entries ++ (t6.eraseIds p.allowedipsList).entries =
      (t4.entries ++ t6.entries).filter (fun e => e.peer != pid) := by
    rw [Tree.eraseIds_entries, Tree.eraseIds_entries, ← List.filter_append]
    apply List.filter_congr
    intro e he
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, bne_iff_ne]
    exact not_congr (resident_saved_iff_owner hf hl hp he)
  rw [← removeByPeerWithStep_eq]
  by_cases hempty : p.allowedipsList.isEmpty = true
  · have hnil : p.allowedipsList = [] := List.isEmpty_iff.mp hempty
    refine ⟨d, w, record ambient .removeListEmpty true, ?_, ?_, ?_⟩
    · simp [removeByPeerWithStep, WG.getPeer, WG.getDev, hd, hp, hnil, branch, AmbientM.branch, record, StateT.run_bind] <;> rfl
    · simp [← hd]
    · refine ⟨?_, ?_, entries⟩
      · simpa [hnil, removalStart] using (RemovedIds.nil hf)
      · simpa only [hnil, Tree.eraseIds] using hl
  · have hempty' : p.allowedipsList.isEmpty = false := Bool.eq_false_iff.mpr hempty
    let start : WGWorld := {w with dev := some (removalStart d p.allowedipsList)}
    let startAmbient := record ambient .removeListEmpty false
    obtain ⟨out, finish, finalAmbient, he, hk, hr⟩ := remove_saved_total p.allowedipsList start startAmbient
      (removalStart d p.allowedipsList) rfl t4 t6 (removalStart_forest hf _)
      hn4 hn6 hc4 hc6 (hl pid p hp).1 hs
    refine ⟨out, finish, record finalAmbient .removeListIter false, ?_, ?_,
      ⟨hr, hr.coherent (removalStart_lists hl _), entries⟩⟩
    · have hg : ((WG.getPeer pid).run w).run ambient = .ok ((p, w), ambient) := by
        simp [WG.getPeer, WG.getDev, hd, hp, StateT.run_bind] <;> rfl
      have hb (w : WGWorld) (ambient : Ambient) (dec : Decision) (value : Bool) :
          ((show WG.M Bool from branch dec value).run w).run ambient =
            .ok ((value, w), record ambient dec value) := rfl
      have hm : ((WG.modifyDev (fun d => {d with peerAllowedips :=
          {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}})).run w).run
          startAmbient = .ok (((), start), startAmbient) := by
        simp [WG.modifyDev, hd, start, removalStart, hempty', StateT.run_modify]
      have exceptBind {α β : Type} (x : Except Stop α) (f : α → Except Stop β) :
          (x >>= f) = Except.bind x f := rfl
      dsimp only [startAmbient] at hm he
      simp only [removeByPeerWithStep, run_bind_eq, hg, exceptBind, Except.bind, hb, hempty',
        Bool.false_eq_true, ↓reduceIte, hm, he, StateT.run_pure]
      rfl
    · rw [hk]

theorem removeByPeer_endpoint (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed) (hl : ResidentLists d t4 t6)
    (hr : ((WG.removeByPeer pid).run w).run ambient = .ok (((), w'), ambient')) :
    ∃ out, w' = {w with dev := some out} ∧ RemovedPeer d out t4 t6 pid p.allowedipsList := by
  obtain ⟨out, finish, finalAmbient, he, hk, hs⟩ := removeByPeer_total w ambient d hd pid p hp t4 t6 hf hn4 hn6 hc4 hc6 hl
  rw [hr] at he
  cases he
  exact ⟨out, hk, hs⟩

theorem resident_eraseIds_entries (hf : ForestRep d t4 t6) (hc : ResidentLists d t4 t6)
    (hp : d.peers[pid]? = some p) (v4 : Bool) :
    let t := if v4 then t4 else t6
    (t.eraseIds p.allowedipsList).entries = t.entries.filter (fun e => e.peer != pid) := by
  dsimp
  rw [Tree.eraseIds_entries]
  apply List.filter_congr
  intro e he
  have he' : e ∈ t4.entries ++ t6.entries := by
    cases v4
    · exact List.mem_append_right _ he
    · exact List.mem_append_left _ he
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, bne_iff_ne]
  exact not_congr (resident_saved_iff_owner hf hc hp he')

theorem RemovedPeer.findNode (h : RemovedPeer d out t4 t6 pid p.allowedipsList)
    (hf : ForestRep d t4 t6) (hc : ResidentLists d t4 t6) (hp : d.peers[pid]? = some p)
    (w : WGWorld) (ambient : Ambient) (hd : w.dev = some out) (hv4 : t4.Valid 32) (hv6 : t6.Valid 128)
    (v4 : Bool) (key : Nat) (hk : key < 2 ^ rootWidth v4) :
    let t := if v4 then t4 else t6
    ∃ w' ambient', ((WG.liftAip (WG.findNode (rootValue out v4) (rootWidth v4) key)).run w).run ambient =
        .ok (((t.eraseIds p.allowedipsList).lookupId (rootWidth v4) key, w'), ambient') ∧
      w' = w ∧ Winner (rootWidth v4) key (t.entries.filter (fun e => e.peer != pid))
        ((t.eraseIds p.allowedipsList).lookup (rootWidth v4) key) := by
  let t := if v4 then t4 else t6
  let store : WG.AipStore := {nodes := out.nodes, nextNode := out.nextNode, trie := out.peerAllowedips}
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have hv : t.Valid (rootWidth v4) := by cases v4 <;> assumption
  have hroot : rootValue out v4 = (t.eraseIds p.allowedipsList).root := by
    cases v4
    · exact h.loop.forest.2.1
    · exact h.loop.forest.1
  have hr : RepAt store.nodes (rootWidth v4) (rootSlot v4) (t.eraseIds p.allowedipsList) := by
    cases v4
    · exact h.loop.forest.2.2.2
    · exact h.loop.forest.2.2.1
  obtain ⟨finalStore, finalAmbient, he, hf'⟩ := findNode_run store ambient (rootWidth v4) key hw hk
    (t.eraseIds p.allowedipsList) (rootSlot v4) hr (Tree.eraseIds_valid t p.allowedipsList hv)
  subst finalStore
  refine ⟨w, finalAmbient, ?_, rfl, ?_⟩
  · rw [Leanux.Proofs.Framing.liftAip_run, hd, hroot]
    dsimp only [store] at he
    simp only [he, Except.map]
    change Except.ok ((_, {w with dev := some out}), finalAmbient) = _
    rw [← hd]
  · rw [← resident_eraseIds_entries hf hc hp v4]
    exact Tree.lookup_spec (Tree.eraseIds_valid t p.allowedipsList hv) key

end Leanux.Proofs.WG.AllowedIps
