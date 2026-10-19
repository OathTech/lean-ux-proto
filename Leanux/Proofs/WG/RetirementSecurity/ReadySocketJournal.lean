import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeInitialized
import Leanux.Proofs.WG.RetirementSecurity.ReadySocketStep
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection

/-! Queued byte readiness and actual socket receipts share the same source
journal. Stopped executions retain the socket safety property. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadySocketJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity

def socket? : Journal.Event → Option Completion.SocketReceipt
  | .socket r => some r
  | _ => none

def receipts (h : List Journal.Event) := h.filterMap socket?
def Safe (h : List Journal.Event) := ∀r∈receipts h,r.packet.value.bytes≠[]
def StateInv (active : List (List SkbId)) (h : List Journal.Event) (w : WGWorld) :=
  ReadyCiphertext.Coherent [] active w ∧ Safe h
def Inv (active : List (List SkbId)) (h : List Journal.Event) (w : World) := StateInv active h w.wg

theorem Safe.frame (before : Safe h) (same : receipts j = receipts h) : Safe j := by
  simpa only [Safe,same] using before

theorem safe_eq (h : List Journal.Event) : Safe h = ReadySocket.Good (h.filterMap Journal.completion?) := by
  have maps : (fun x => (Journal.completion? x).bind Completion.socket?) = socket? := by
    funext e
    cases e <;> rfl
  simp only [Safe,receipts,ReadySocket.Good,List.filterMap_filterMap,maps]

theorem initial (net bare : Bool) : StateInv [] [] (Runner.initialWG net bare) :=
  ⟨ReadyCiphertext.Lifecycle.initial net bare,by intro r member; cases member⟩

end Leanux.Proofs.WG.RetirementSecurity.ReadySocketJournal
