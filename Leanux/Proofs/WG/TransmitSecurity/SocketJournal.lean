import Leanux.Proofs.WG.TransmitSecurity.BatchNativeInitialized
import Leanux.Proofs.WG.TransmitSecurity.CompletionPeerStep
import Leanux.Proofs.WG.TransmitSecurity.JournalSocketHistory

/-! The shared journal carries batch alignment beside the selected peer of every
actual socket receipt. Quiet paths preserve the complete receipt list. -/
namespace Leanux.Proofs.WG.TransmitSecurity.SocketJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

def receipts (h : List Journal.Event) := h.filterMap Journal.SocketHistory.socket?
def Safe (h : List Journal.Event) := ∀ r ∈ receipts h, r.packet.value.peer = r.pid
def StateInv (active : List (List SkbId)) (h : List Journal.Event) (w : WGWorld) :=
  BatchCoherence.Native.Coherent [] active w ∧ Safe h
def Inv (active : List (List SkbId)) (h : List Journal.Event) (w : World) := StateInv active h w.wg

theorem Safe.frame (before : Safe h) (same : receipts j = receipts h) : Safe j := by
  simpa only [Safe,same] using before

theorem safe_eq (h : List Journal.Event) : Safe h = CompletionPeer.Good (h.filterMap Journal.completion?) := by
  have maps : (fun x => (Journal.completion? x).bind Completion.socket?) = Journal.SocketHistory.socket? := by
    funext e
    cases e <;> rfl
  simp only [Safe,receipts,CompletionPeer.Good,List.filterMap_filterMap,maps]

theorem initial (net bare : Bool) : StateInv [] [] (Runner.initialWG net bare) :=
  ⟨BatchCoherence.Lifecycle.initial net bare,by intro r member; cases member⟩

end Leanux.Proofs.WG.TransmitSecurity.SocketJournal
