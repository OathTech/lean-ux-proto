import Leanux.Proofs.WG.Progress.NativeSuffixSource
import Leanux.Proofs.WG.Queues.RxWorkerCuts

/-! Suffix preservation through original decryption and the existing RX publication and preparation source cuts. These partial-correctness contracts do not assert callback termination. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem decryptPacket_retains (records : List HiddenRecord) (pkt : RxPacket) :
    NativeKeeps records (decryptPacket pkt) := by
  unfold decryptPacket
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_branchCmp records _ _ _ _
    | with_reducible exact native_expired records _ _ _ _
    | with_reducible exact native_alloc records _
    | with_reducible exact native_getKeypair records _
    | with_reducible exact native_setKeypair records _ _
    | with_reducible exact native_invariant records _
    | with_reducible exact native_unsupported records _
    | with_reducible exact native_stop records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_or records
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem decryptPacket_statePrefix {E : Type} (records : List HiddenRecord) (pkt : RxPacket) :
    StatePrefixPreserves (fun (_ : List E) _ a=>Tail records a.hidden) (fun _=>True)
      (liftWGPrefix (decryptPacket pkt)) :=
  native_statePrefix records _ (decryptPacket_retains records pkt)

theorem publish_retains (records : List HiddenRecord) (id : SkbId) (state : PacketState) :
    NativeKeeps records (Queues.RxWorkers.publishSource id state) := by
  unfold Queues.RxWorkers.publishSource
  repeat' first
    | with_reducible exact native_getRx records _
    | with_reducible exact native_peerDeref records _
    | with_reducible exact native_peerGet records _
    | with_reducible exact native_getPeer records _
    | with_reducible exact native_setPeer records _ _
    | with_reducible exact native_setRx records _ _
    | with_reducible exact native_invariant records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem prepare_retains (records : List HiddenRecord) :
    NativeKeeps records Queues.RxWorkers.prepareSource := by
  unfold Queues.RxWorkers.prepareSource
  repeat' first
    | with_reducible exact native_getDev records
    | with_reducible exact native_modifyDev records _
    | with_reducible exact native_getRx records _
    | with_reducible exact native_setRx records _ _
    | with_reducible exact decryptPacket_retains records _
    | with_reducible exact publish_retains records _ _
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_invariant records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem prepare_statePrefix {E : Type} (records : List HiddenRecord) :
    StatePrefixPreserves (fun (_ : List E) _ a=>Tail records a.hidden) (fun _=>True)
      (liftWGPrefix Queues.RxWorkers.prepareSource) :=
  native_statePrefix records _ (prepare_retains records)

end Leanux.Proofs.WG.Progress.RecordSuffix
