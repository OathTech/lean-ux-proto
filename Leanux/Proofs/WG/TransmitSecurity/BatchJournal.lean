import Leanux.Proofs.WG.TransmitSecurity.BatchNativeInitialized
import Leanux.Proofs.WG.TransmitSecurity.BatchWorkerHistory

/-! The shared journal carries batch alignment beside agreement of every
actual encryption receipt. Quiet paths preserve the complete receipt list. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

def receipts (h : List Journal.Event) := h.filterMap Journal.encryption?
def Safe (h : List Journal.Event) := BatchWorkerHistory.Good (receipts h)
def StateInv (active : List (List SkbId)) (h : List Journal.Event) (w : WGWorld) :=
  BatchCoherence.Native.Coherent [] active w ∧ Safe h
def Inv (active : List (List SkbId)) (h : List Journal.Event) (w : World) := StateInv active h w.wg

theorem Safe.frame (before : Safe h) (same : receipts j = receipts h) : Safe j := by
  simpa only [Safe,same] using before

theorem initial (net bare : Bool) : StateInv [] [] (Runner.initialWG net bare) :=
  ⟨BatchCoherence.Lifecycle.initial net bare,by intro r member; cases member⟩

end Leanux.Proofs.WG.TransmitSecurity.BatchJournal
