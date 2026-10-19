import Leanux.Proofs.WG.Progress.ReleaseSuffixSource
import Leanux.Proofs.WG.Progress.DecryptSuffixSource

/-! The existing exact publication/decrypt source cuts compose with explicit IRQ and softirq parameters. Concrete Env callback suffix contracts remain separate obligations. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem enqueue_retains (records : List HiddenRecord) (irq : Leanux.M Unit)
    (irqKeeps : Preserves (fun w : World=>Tail records w.ambient.hidden) irq)
    (id : SkbId) (state : PacketState) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (enqueuePerPeerRx irq id state) := by
  rw [Queues.RxWorkers.enqueue_source]
  exact preserves_bind (native_product records _ (publish_retains records id state))
    (fun pid=>preserves_bind irqKeeps (fun _=>native_product records _ (peerPut_retains records (some pid))))

theorem decryptStep_retains (records : List HiddenRecord) (softirq irq : Leanux.M Unit)
    (softirqKeeps : Preserves (fun w : World=>Tail records w.ambient.hidden) softirq)
    (irqKeeps : Preserves (fun w : World=>Tail records w.ambient.hidden) irq) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (decryptStep softirq irq) := by
  rw [← Queues.RxWorkers.decrypt_source]
  unfold Queues.RxWorkers.decryptSource
  apply preserves_bind softirqKeeps
  intro _
  apply preserves_bind (native_product records _ (prepare_retains records))
  intro peer
  cases peer with
  | none => exact preserves_pure false
  | some pid =>
    exact preserves_bind irqKeeps (fun _=>
      preserves_bind (native_product records _ (peerPut_retains records (some pid))) (fun _=>
        preserves_bind softirqKeeps (fun _=>preserves_pure true)))

end Leanux.Proofs.WG.Progress.RecordSuffix
