import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSoundHeld
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceStagingFrames
import Leanux.Proofs.WG.RetirementSecurity.TxWorkStagingFrames

/-! The native allocation preconditions retained by selected staging. These
frames concern packet allocation bounds, complete owning queues and TX cells;
the ledger's semantic evidence is carried separately. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.NativeReady
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues RetirementSecurity

def Inv (locals : List TxLocalBatch) (w : WGWorld) : Prop :=
  Packets.Inv w ∧ TxCoverage locals w ∧ TxInventory locals w

theorem frame (before : Inv locals w)
    (shape : StagingOccurrences.geometry v = StagingOccurrences.geometry w)
    (queues : txQueueContents v = txQueueContents w) : Inv locals v := by
  refine ⟨?_,before.2.1.cells (congrArg Prod.snd shape) queues,
    before.2.2.queueContents queues (congrArg Prod.snd shape)⟩
  have same : Packets.snapshot v = Packets.snapshot w := congrArg Prod.fst shape
  simpa only [Packets.Inv,same] using before.1

theorem native {action : WG.M α}
    (shape : SameView StagingOccurrences.geometry action)
    (queues : SameView txQueueContents action) : Preserves (Inv locals) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  exact frame before ((ProjectedAction.iff_run_ambient _ _ _).mp shape w a value v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a value v b run)

theorem world {action : WG.M α} (same : SameView id action) : Preserves (Inv locals) action :=
  native (same.factor StagingOccurrences.geometry) (same.factor txQueueContents)

theorem read_key (kid : KeypairId) : Preserves (Inv locals) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a key v b before run
  simpa only [(KeyTimes.getKeypair_return kid w v key a b run).1] using before

theorem key_geometry (kid : KeypairId) (key : Keypair) :
    SameView StagingOccurrences.geometry (setKeypair kid key) := by
  intro initial
  unfold setKeypair
  apply hoare_modify
  intro w before
  cases device : w.dev <;>
    simpa only [StagingOccurrences.geometry,Packets.snapshot,Packets.deviceStore,
      TxDisposition.txPackets,device,Option.map_none,Option.map_some,
      Option.bind_none,Option.bind_some] using before

theorem write_key (kid : KeypairId) (key : Keypair) : Preserves (Inv locals) (setKeypair kid key) :=
  native (key_geometry kid key)
    ((TxWork.set_key_queues kid key).factor (fun q pid => (q pid).getD []))

theorem reserve (kid : KeypairId) : Preserves (Inv locals) (Nonce.reserveNative kid) := by
  unfold Nonce.reserveNative
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨key,u,c,readRun,tail⟩ := run
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨_,t,e,written,returned⟩ := tail
  cases returned
  exact (hoare_iff_run_ambient _ _ _).mp (write_key kid _) u c () v b
    ((hoare_iff_run_ambient _ _ _).mp (read_key kid) w a key u c before readRun) written

theorem get_key (kid : Option KeypairId) : Preserves (Inv locals) (keypairGet kid) :=
  native (StagingOccurrences.key_get_geometry kid)
    ((keyGet_tx_queues kid).factor (fun q pid => (q pid).getD []))

theorem get_peer (pid : PeerId) : Preserves (Inv locals) (peerGet pid) :=
  native (StagingOccurrences.peer_get_geometry pid)
    ((ownership_queues (peerGet_ownership pid)).factor (fun q pid => (q pid).getD []))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.NativeReady
