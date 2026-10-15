import Leanux.Proofs.WG.Config.PeerDead

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem clearOne_empty_returns (pid : PeerId) (pick : Peer → Option KeypairId)
    (clear : Peer → Peer) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : pick p = none) :
    Returns (clearOne pid pick clear) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (withPeer d pid (clear p))) := by
  have hg : Returns (getPeer pid) (fun w => w.k.wg = some d)
      (fun result w => result = p ∧ w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [getPeer, getDev, getK, invariant]
    all_goals simp_all
  have hm : Returns (modifyPeer pid clear) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (withPeer d pid (clear p))) := by
    rw [returns_iff]
    noise_vcgen [_private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
      getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [withPeer]
  have hn : Returns (keypairPut none true)
      (fun w => w.k.wg = some (withPeer d pid (clear p)))
      (fun _ w => w.k.wg = some (withPeer d pid (clear p))) := by
    rw [returns_iff]
    mvcgen [keypairPut, branch]
  unfold clearOne
  refine returns_bind _ _ hg ?_
  intro result w pre
  obtain ⟨value, device⟩ := pre
  subst result
  rw [empty]
  exact returns_bind _ _ hm (fun _ => hn) w device

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
    Returns (keypairsClear pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (emptyKeysDevice d pid p)) := by
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
