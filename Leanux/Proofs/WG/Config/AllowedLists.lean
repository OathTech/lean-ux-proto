import Leanux.Proofs.WG.Config.DumpReturns

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def listDelEntries (id : NodeId) (entries : List (PeerId × Peer)) : WG.M Unit := do
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
  simp [listDelEntries, List.forIn_cons]
  split <;> simp

theorem listDelEntries_returns (id : NodeId) (entries : List (PeerId × Peer)) (d : Device) :
    Returns (listDelEntries id entries) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (deleteListedNodes id d entries)) := by
  induction entries generalizing d with
  | nil =>
    intro g ambient device
    exact ⟨(), g, ambient, rfl, device⟩
  | cons entry rest ih =>
    obtain ⟨pid, p⟩ := entry
    intro g ambient device
    by_cases listed : id ∈ p.allowedipsList
    · let next := deleteListedNode id d (pid, p)
      obtain ⟨result, final, after, run, effect⟩ :=
        ih next {g with dev := some next} ambient rfl
      refine ⟨result, final, after, ?_, ?_⟩
      · rw [listDelEntries_cons]
        simpa [listed, setPeer, modifyDev, device, next, deleteListedNode] using run
      · simpa [deleteListedNodes, next] using effect
    · obtain ⟨result, final, after, run, effect⟩ := ih d g ambient device
      refine ⟨result, final, after, ?_, ?_⟩
      · rw [listDelEntries_cons]
        simpa [listed] using run
      · simpa [deleteListedNodes, deleteListedNode, listed] using effect

theorem listDel_returns (id : NodeId) (d : Device) :
    Returns (listDel id) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (deleteListedNodes id d d.peers.toList)) := by
  have hg : Returns getDev (fun w => w.dev = some d)
      (fun result w => result = d ∧ w.dev = some d) := by
    intro g ambient device
    refine ⟨d, g, ambient, ?_, rfl, device⟩
    simp [getDev, device]
    rfl
  rw [listDel_source]
  apply returns_bind _ _ hg
  intro result w ambient h
  obtain ⟨heq, hd⟩ := h
  subst result
  exact listDelEntries_returns id d.peers.toList d w ambient hd

end Leanux.Proofs.WG.Config
