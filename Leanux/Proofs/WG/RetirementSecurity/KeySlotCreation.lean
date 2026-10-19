import Leanux.Proofs.WG.RetirementSecurity.KeySlotWorkers

/-! Allocation initializes empty slots and native setup retains the saved
record's liveness relation. Creation needs no key-credit or numeric-slot
persistence assumption for this data projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem creation_core (before : InvExcept pending w) (device : w.dev=some d) (key : Key) :
    InvExcept pending (Peers.creationCoreWorld w d.nextPeer key) := by
  intro pid p found outside slots
  by_cases chosen : d.nextPeer=pid
  · subst pid
    have equal : p=Peers.createdPeer key (w.peerCounter+1) := by
      simpa [peerAt,Peers.creationCoreWorld,device] using found.symm
    subst p
    simp [HasKeySlot,Peers.createdPeer] at slots
  · exact before pid p (by simpa [peerAt,Peers.creationCoreWorld,device,
      Std.TreeMap.getElem?_insert,chosen] using found) outside slots

theorem precompute (pid : PeerId) : Preserves (InvExcept pending) (precomputeStaticStatic pid) := by
  unfold precomputeStaticStatic
  simp (config := {zeta:=false}) only [requireNotPending,branch]
  repeat' key_slot_work_step

theorem handshake_init (pid : PeerId) (psk : Option Key) :
    Preserves (InvExcept pending) (handshakeInit pid psk) := by
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact precompute _)
    | key_slot_work_step

theorem cache_reset (pid : PeerId) : Preserves (InvExcept pending) (dstCacheReset pid) := by
  unfold dstCacheReset
  simp (config := {zeta:=false}) only [getAmbient,hiddenJiffies]
  repeat' key_slot_work_step

theorem creation_finish (pid : PeerId) (key : Key) (psk : Option Key) :
    Preserves (InvExcept pending) (BaseCreation.finish pid key psk) := by
  unfold BaseCreation.finish ConfiguredIdentity.publishRow
  exact preserves_bind (cache_reset pid) (fun _=>
    preserves_bind (handshake_init pid psk) (fun _=>
      preserves_bind (reset pid) (fun _=>modify _ (fun _=>rfl))))

theorem create (key : Key) (psk : Option Key) : Preserves (InvExcept pending) (peerCreate key psk) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (hoare_iff_run_ambient _ _ _).mp
    (HolderPeerCreation.source (InvExcept pending) w key psk before
      (fun _ device=>creation_core before device key) (fun pid=>creation_finish pid key psk))
    w a result v b rfl run

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
