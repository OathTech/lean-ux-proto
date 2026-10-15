import Leanux.Proofs.WG.Config.DumpReturns

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def listDelEntries (id : NodeId) (entries : List (PeerId × Peer)) : M Unit := do
  for (pid, p) in entries do
    if p.allowedipsList.contains id then
      setPeer pid { p with allowedipsList := listRemove p.allowedipsList id }

theorem listDel_source (id : NodeId) :
    listDel id = (do let d ← getDev; listDelEntries id d.peers.toList) := rfl

def deleteListedNode (id : NodeId) (d : Device) (entry : PeerId × Peer) : Device :=
  if entry.2.allowedipsList.contains id then
    let p := entry.2
    { d with peers := d.peers.insert entry.1 { p with allowedipsList := listRemove p.allowedipsList id } }
  else d

def deleteListedNodes (id : NodeId) (d : Device) (entries : List (PeerId × Peer)) : Device :=
  entries.foldl (deleteListedNode id) d

theorem listDelEntries_cons (id : NodeId) (pid : PeerId) (p : Peer) (rest : List (PeerId × Peer)) :
    listDelEntries id ((pid, p) :: rest) = (do
      if p.allowedipsList.contains id then
        setPeer pid { p with allowedipsList := listRemove p.allowedipsList id }
      listDelEntries id rest) := by
  simp [listDelEntries, List.forIn_cons, bind_assoc]
  split <;> simp [bind_assoc]

theorem listDelEntries_returns (id : NodeId) (entries : List (PeerId × Peer)) (d : Device) :
    Returns (listDelEntries id entries) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (deleteListedNodes id d entries)) := by
  induction entries generalizing d with
  | nil =>
      rw [returns_iff]
      simp [listDelEntries, deleteListedNodes]
      mvcgen
  | cons entry rest ih =>
      obtain ⟨pid, p⟩ := entry
      have ht := fun next => (returns_iff _ _ _).mp (ih next)
      rw [returns_iff]
      rw [listDelEntries_cons]
      mvcgen [setPeer, modifyDev, modifyK, ht]
      all_goals try dsimp +zetaDelta only at *
      all_goals repeat intro
      all_goals simp_all [deleteListedNodes, deleteListedNode]
      all_goals subst_vars
      all_goals exact ht _ _ (by assumption)

theorem listDel_returns (id : NodeId) (d : Device) :
    Returns (listDel id) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (deleteListedNodes id d d.peers.toList)) := by
  have hg : Returns getDev (fun w => w.k.wg = some d)
      (fun result w => result = d ∧ w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [getDev, getK, invariant]
    all_goals simp_all
  rw [listDel_source]
  apply returns_bind _ _ hg
  intro result w h
  obtain ⟨heq, hd⟩ := h
  subst result
  exact listDelEntries_returns id d.peers.toList d w hd

end Leanux.Proofs.WG.Config
