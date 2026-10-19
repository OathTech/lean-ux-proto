import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextStaging

/-! Full packet cells and logical queue contents form the passive frame for
readiness. No erasure of bytes or completion marks is used in these frames. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

def view (w : WGWorld) := (handoffTxView w,TxDisposition.txPackets w)

theorem Inv.frame (before : Inv w) (same : view v=view w) : Inv v :=
  before.contents (queueContents_of_exact (congrArg Prod.fst same)) (congrArg Prod.snd same)

namespace Native

theorem wire {action : WG.M α} (queues : SameView handoffTxView action)
    (packets : SameView txCryptWire action) : Preserves Inv action :=
  frame (contents_factor queues) (packets.factor Prod.snd)

theorem contents_frame (before : Inv w) (queues : txQueueContents v=txQueueContents w)
    (packets : TxDisposition.txPackets v=TxDisposition.txPackets w) : Inv v :=
  before.contents queues packets

theorem contents_wire {action : WG.M α} (queues : SameView txQueueContents action)
    (wire : SameView txCryptWire action) : Preserves Inv action :=
  frame queues (wire.factor Prod.snd)

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves Inv action := by
  apply frame
  · exact same.of_factor (fun s=>txQueueContents {dev:=s.dev}) txQueueContents (fun _=>rfl)
  · exact same.of_factor (fun s=>TxDisposition.txPackets {dev:=s.dev}) TxDisposition.txPackets (fun _=>rfl)

theorem coherent_join {action : WG.M α}
    (physical : Preserves (OccurrenceStack.Ready locals active) action)
    (coherent : Preserves Inv action) : Preserves (Coherent locals active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp physical w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp coherent w a result v b before.2 run⟩

theorem coherent_store {action : WG.M α} (same : SameWGStore action) :
    Preserves (Coherent locals active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields:=(ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact ⟨OccurrenceStack.ready_store fields before.1,
    (hoare_iff_run_ambient _ _ _).mp (store same) w a result v b before.2 run⟩

theorem key_get (kid : Option KeypairId) : Preserves Inv (keypairGet kid) :=
  wire (keyGet_tx_queues kid) (keyGet_cryptWire kid)

theorem read_key (kid : KeypairId) : Preserves Inv (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b before run
  exact (KeyTimes.getKeypair_return kid w v k a b run).1 ▸ before

theorem free_packet (id : SkbId) : Preserves Inv (freeTxSkb id) := by
  simpa only [TxDisposition.freeList_cons,TxDisposition.freeList_nil,bind_pure_unit] using free_list [id]

end Native
end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
