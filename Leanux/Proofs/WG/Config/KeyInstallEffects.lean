import Leanux.Proofs.WG.Config.KeyPeerEffects

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem keyPeer_missing_full (pid : PeerId) (sendStaged : Bool) :
    Ensures (keyPeerSource pid sendStaged) (fun w => peerAt w pid = none) (fun _ _ => False) := by
  have he := unconstrained_prefix (expireCurrentPeerKeypairs pid)
  have hs := unconstrained_prefix (sendStagedPackets pid)
  rw [ensures_iff]
  simp [keyPeerSource, branch, bind_assoc]
  mvcgen [precomputeStaticStatic, requireNotPending, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, unsupported, he, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt]

theorem keyPeer_full_step (pid : PeerId) (d : Device) (sendStaged : Bool) :
    Ensures (keyPeerSource pid sendStaged) (fun w => w.k.wg = some d)
      (fun _ w => ∃ p now queueNow, d.peers[pid]? = some p ∧ w.k.wg = some (keyPeerDevice d pid p now sendStaged queueNow)) := by
  intro w ret v hd hr
  cases resident : d.peers[pid]? with
  | none => exact False.elim (keyPeer_missing_full pid sendStaged w ret v (by simp [peerAt, hd, resident]) hr)
  | some p =>
    obtain ⟨now, queueNow, hv⟩ := keyPeer_complete pid d p sendStaged resident w ret v hd hr
    exact ⟨p, now, queueNow, rfl, hv⟩

/-- Ordered effects of the actual snapshotted peer list, including optional
staged sending. Timestamps here are existential parameters of Device effects;
this relation does not describe World bookkeeping or captured-record provenance. -/
inductive KeyPeerRun (sendStaged : Bool) : Device → List PeerId → Device → Prop
  | nil (d : Device) : KeyPeerRun sendStaged d [] d
  | cons (d : Device) (pid : PeerId) (p : Peer) (expiryNow queueNow : Int64)
      (rest : List PeerId) (final : Device)
      (resident : d.peers[pid]? = some p)
      (tail : KeyPeerRun sendStaged (keyPeerDevice d pid p expiryNow sendStaged queueNow) rest final) :
      KeyPeerRun sendStaged d (pid :: rest) final

theorem keyPeerLoop_complete (pids : List PeerId) (d : Device) (sendStaged : Bool) :
    Ensures (keyPeerLoopSource pids sendStaged) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ KeyPeerRun sendStaged d pids final) := by
  induction pids generalizing d with
  | nil =>
    intro w ret v hp hr
    simp [keyPeerLoopSource, StateT.run] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨d, hp, .nil d⟩
  | cons pid rest ih =>
    have factor : keyPeerLoopSource (pid :: rest) sendStaged = ((do
        _ ← branch .setDevKeyPeerIter true
        keyPeerSource pid sendStaged) >>= fun _ => keyPeerLoopSource rest sendStaged) := by
      simp [keyPeerLoopSource, List.forIn_cons, bind_assoc]
    have hstep : Ensures (do
        _ ← branch .setDevKeyPeerIter true
        keyPeerSource pid sendStaged) (fun w => w.k.wg = some d)
        (fun _ w => ∃ p now queueNow, d.peers[pid]? = some p ∧ w.k.wg = some (keyPeerDevice d pid p now sendStaged queueNow)) := by
      have hs := (ensures_iff _ _ _).mp (keyPeer_full_step pid d sendStaged)
      rw [ensures_iff]
      mvcgen [branch, hs]
    rw [factor]
    refine ensures_bind (R := fun (_ : Unit) w => ∃ final, w.k.wg = some final ∧ KeyPeerRun sendStaged d (pid :: rest) final)
      _ _ hstep ?_
    intro _ w ret v hp hr
    obtain ⟨p, now, queueNow, resident, hd⟩ := hp
    obtain ⟨final, hv, tail⟩ := ih (keyPeerDevice d pid p now sendStaged queueNow) w ret v hd hr
    exact ⟨final, hv, .cons d pid p now queueNow rest final resident tail⟩

theorem keyInstall_complete (d : Device) (key : Key) :
    Ensures (keyInstallSource key) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        KeyPeerRun (requestsStagedSend d key) (installedDevice d key) d.peerList final) := by
  have hi := (returns_iff _ _ _).mp (setStaticIdentity_returns key d)
  have hc := (returns_iff _ _ _).mp
    (cookiePrecompute_returns { d with staticIdentity := identityAfter key d.staticIdentity })
  have hl (sendStaged : Bool) := (ensures_iff _ _ _).mp
    (keyPeerLoop_complete d.peerList (installedDevice d key) sendStaged)
  rw [ensures_iff]
  simp [keyInstallSource, WG.andM, branch, bind_assoc]
  mvcgen [getDev, getK, invariant, hi, hc, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [-Bool.forall_bool, requestsStagedSend, installedDevice, cookieKeysAfter]
  all_goals subst_vars
  all_goals try exact hl _ _ (by assumption)

end Leanux.Proofs.WG.Config
