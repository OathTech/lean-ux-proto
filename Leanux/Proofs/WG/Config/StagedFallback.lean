import Leanux.Proofs.WG.Config.StagedFallbackSource
import Leanux.Proofs.WG.Config.KeyReferences

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Historical prediction for the pending callers below; current effects use the actual inspection. -/
def fallbackDevice (d : Device) (pid : PeerId) (p : Peer) (packets : List Packet) (now : Int64) : Device :=
  let restored := { p with staged := packets ++ p.staged }
  let reset := { restored with timerHandshakeAttempts := 0 }
  queuedDevice (withPeer (withPeer d pid restored) pid reset) pid reset now

theorem stagedAfterGet_none (pid : PeerId) (packets : List Packet) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (stagedAfterGet pid packets none) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some (fallbackDevice d pid p packets now)) := by
  have hp : Ensures (keypairPut none false) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some d) := by
    intro w ret v hd hr
    obtain ⟨u, result, he, hv⟩ := keypairPut_none d w hd
    rw [hr] at he
    cases he
    exact hv
  have hs := (ensures_iff _ _ _).mp (stagedFallback_exact pid packets none d d p resident hp)
  rw [ensures_iff]
  simp [stagedAfterGet, branch, bind_assoc]
  mvcgen [hs]

theorem stagedAfterGet_invalid (pid : PeerId) (packets : List Packet) (id : KeypairId)
    (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (keyResident : d.keypairs[id]? = some k)
    (invalid : k.sending.isValid = false) (retained : 1 < k.refcount) :
    Ensures (stagedAfterGet pid packets (some id)) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some
        (fallbackDevice (withKeypair d id { k with refcount := k.refcount - 1 }) pid p packets now)) := by
  have hp : Ensures (keypairPut (some id) false) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (withKeypair d id { k with refcount := k.refcount - 1 })) := by
    intro w ret v hd hr
    obtain ⟨u, result, he, hv⟩ := keypairPut_retained id d k keyResident retained w hd
    rw [hr] at he
    cases he
    exact hv
  have hs := (ensures_iff _ _ _).mp
    (stagedFallback_exact pid packets (some id) d (withKeypair d id { k with refcount := k.refcount - 1 })
      p (by simpa [withKeypair] using resident) hp)
  rw [ensures_iff]
  simp [stagedAfterGet, branch, bind_assoc]
  mvcgen [getKeypair, getDev, getK, invariant, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

end Leanux.Proofs.WG.Config
