import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedSavedPeerFrames

/-! Saved peer metadata writes retain both staged and allocated queue owners.
The original read supplies the resident allocation and queue representation;
each later write must preserve those exact fields. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SavedFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

def PeerFields (pid : PeerId) (p : Peer) (w : WGWorld) : Prop :=
  ∃ d q, w.dev = some d ∧ d.peers[pid]? = some q ∧
    q.internalId = p.internalId ∧ q.staged = p.staged ∧ q.txQueue = p.txQueue

theorem read (pid : PeerId) (P : _ → Prop) :
    Hoare (getPeer pid) (fun w => P (StagedEntry.view w))
      (fun p w => P (StagedEntry.view w) ∧ PeerFields pid p w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  obtain ⟨rfl,_,d,device,resident⟩ := getPeer_normal pid w v p a b run
  exact ⟨before,d,p,device,resident,rfl,rfl,rfl⟩

theorem write (pid : PeerId) (p : Peer) (P : _ → Prop) :
    Preserves (fun w => P (StagedEntry.view w) ∧ PeerFields pid p w) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  obtain ⟨d,q,device,resident,stamp,staged,queued⟩ := before.2
  simp [setPeer,modifyDev,device] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  refine ⟨?_,{d with peers := d.peers.insert pid p},p,rfl,?_,rfl,rfl,rfl⟩
  · rw [Queued.replace_peer device resident stamp.symm staged.symm queued.symm]
    exact before.1
  · simp

theorem write_saved (pid : PeerId) (p q : Peer) (P : _ → Prop)
    (same : q.internalId = p.internalId ∧ q.staged = p.staged ∧ q.txQueue = p.txQueue) :
    Preserves (fun w => P (StagedEntry.view w) ∧ PeerFields pid p w) (setPeer pid q) := by
  have fields : ∀ w, PeerFields pid q w ↔ PeerFields pid p w := by
    intro w
    simp only [PeerFields,same.1,same.2.1,same.2.2]
  simpa only [fields] using write pid q P

theorem update (pid : PeerId) (saved : Peer) (P : _ → Prop) (f : Peer → Peer)
    (same : ∀ q, (f q).internalId = q.internalId ∧ (f q).staged = q.staged ∧ (f q).txQueue = q.txQueue) :
    Preserves (fun w => P (StagedEntry.view w) ∧ PeerFields pid saved w)
      (getPeer pid >>= fun q => setPeer pid (f q)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨q,u,c,read,writeRun⟩ := run
  obtain ⟨rfl,rfl,d,device,resident⟩ := getPeer_normal pid w u q a c read
  obtain ⟨old,prior,oldDevice,oldResident,stamp,staged,queued⟩ := before.2
  have sameDevice : old = d := Option.some.inj (oldDevice.symm.trans device)
  subst old
  have samePeer : prior = q := Option.some.inj (oldResident.symm.trans resident)
  subst prior
  exact (hoare_iff_run_ambient _ _ _).mp
    (write_saved pid saved (f q) P
      ⟨(same q).1.trans stamp,(same q).2.1.trans staged,(same q).2.2.trans queued⟩)
    _ _ value v b before writeRun

theorem precompute (pid : PeerId) : SameView StagedEntry.view (precomputeStaticStatic pid) := by
  intro initial
  unfold precomputeStaticStatic requireNotPending
  simp only [pure_bind]
  apply preserves_bind ((TimerFrames.store getDev_sameWGStore).wp (· = initial))
  intro identity
  apply hoare_bind _ _ (read pid (· = initial))
  intro p
  let P := fun w => StagedEntry.view w = initial ∧ PeerFields pid p w
  apply hoare_consequence (P := P) (Q := fun _ => P) ?_
    (fun _ before => before) (fun _ _ before => before.1)
  change Preserves P _
  simp only [branch]
  repeat' first
    | (receive_update_head setPeer
       apply update pid p (· = initial)
       intro q; exact ⟨rfl,rfl,rfl⟩)
    | (rx_retention_head setPeer; apply write_saved pid p _ (· = initial); exact ⟨rfl,rfl,rfl⟩)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SavedFrames
