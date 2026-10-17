import Leanux.Proofs.WG.Config.PeerDead

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem clearOne_empty_returns (pid : PeerId) (pick : Peer → Option KeypairId)
    (clear : Peer → Peer) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : pick p = none) :
    Returns (clearOne pid pick clear) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (withPeer d pid (clear p))) := by
  have hg : Returns (getPeer pid) (fun w => w.dev = some d)
      (fun result w => result = p ∧ w.dev = some d) := by
    intro g ambient device
    refine ⟨p, g, ambient, ?_, rfl, device⟩
    simp [getPeer, getDev, device, resident]
    rfl
  have hm : Returns (modifyPeer pid clear) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (withPeer d pid (clear p))) := by
    intro g ambient device
    refine ⟨(), {g with dev := some (withPeer d pid (clear p))}, ambient, ?_, rfl⟩
    change (((getPeer pid >>= fun p => setPeer pid (clear p)).run g).run ambient) = _
    simp [getPeer, getDev, device, resident, setPeer, modifyDev, withPeer]
    rfl
  have hn : Returns (keypairPut none true)
      (fun w => w.dev = some (withPeer d pid (clear p)))
      (fun _ w => w.dev = some (withPeer d pid (clear p))) := by
    intro g ambient device
    let after := {ambient with steps := ambient.steps.push {
      decision := .keypairPutNull, outcome := true, netRx := ambient.netRxSection}}
    refine ⟨(), g, after, ?_, device⟩
    simp [keypairPut, branch, AmbientM.branch, after]
    rfl
  unfold clearOne
  refine returns_bind _ _ hg ?_
  intro result w ambient pre
  obtain ⟨value, device⟩ := pre
  subst result
  rw [empty]
  exact returns_bind _ _ hm (fun _ => hn) w ambient device

def emptyKeysPeer (p : Peer) : Peer :=
  { p with keypairNext := none, keypairPrevious := none, keypairCurrent := none }

/-- Keep the actual three writes even when all slot values were already NULL. -/
def emptyKeysDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  let p1 := { p with keypairNext := none }
  let p2 := { p1 with keypairPrevious := none }
  withPeer (withPeer (withPeer d pid p1) pid p2) pid (emptyKeysPeer p)

theorem keypairsClear_empty_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none) :
    Returns (keypairsClear pid) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (emptyKeysDevice d pid p)) := by
  rw [keypairsClear_source]
  refine returns_bind _ _ (clearOne_empty_returns pid _ _ d p resident empty.1) ?_
  intro u
  refine returns_bind _ _ (clearOne_empty_returns pid _ _
    (withPeer d pid { p with keypairNext := none }) { p with keypairNext := none }
    (by simp [withPeer]) empty.2.1) ?_
  intro u
  exact clearOne_empty_returns pid _ _
    (withPeer (withPeer d pid { p with keypairNext := none }) pid
      { p with keypairNext := none, keypairPrevious := none })
    { p with keypairNext := none, keypairPrevious := none }
    (by simp [withPeer]) empty.2.2

end Leanux.Proofs.WG.Config
