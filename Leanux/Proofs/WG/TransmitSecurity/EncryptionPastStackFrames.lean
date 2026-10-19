import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastTransmit
import Leanux.Proofs.WG.Queues.TxLiveStack

/-! Product-state transport for the historical encryption projection. Ordinary
Stack bookkeeping retains the entire WireGuard store; actual replies use the
native transmit contract instead of a state frame. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.Proofs.Framing Leanux.Proofs.Logged WG Lifetimes Queues
open TxDisposition

theorem product_transport (same : productStoreView v = productStoreView w)
    (before : Ready past active w.wg) : Ready past active v.wg := by
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  have epochs : v.wg.netIfindexNext = w.wg.netIfindexNext :=
    congrArg (fun s : ProductStore43 => s.2.2.2.netIfindexNext) same
  simpa only [Ready,LiveFrontier.Ready,LiveFrontier.Inv,LiveFrontier.Physical,view,device,epochs] using before

theorem native_of_source {E α : Type} (g : PrefixM E α) (action : Leanux.M α)
    (erase : ErasesPrefix g action)
    (keeps : PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True) g) :
    Preserves (fun w : World => Ready past active w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  obtain ⟨_,_,_,out⟩ := keeps w [] before
  have erased := erase w []
  rw [run] at erased
  simpa only [erased] using out

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
