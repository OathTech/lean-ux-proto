import Leanux.Proofs.WG.AuthenticatedEffects.CausalRootsInitialized
import Leanux.Proofs.WG.TransmitSecurity.JournalSocketHistory
import Leanux.Proofs.WG.TransmitSecurity.CompletionEmission

/-! Actual transport socket receipts and keepalive preparations inherit the
initialized causal explanation on their own final-journal occurrence. Socket
validity binds any emitted bytes to the observed peer endpoint and native call;
this does not yet claim that handshake/cookie sends are in this receipt family. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Roots
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem socket_valid (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (receipt : Completion.SocketReceipt)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .old (.socket receipt) :: after) :
    receipt.Valid := by
  have projected := congrArg Prod.snd (execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at projected
  have oldPosition : (runPrefixOuter (Journal.execute trace placeholders) []).2 =
      before.filterMap old? ++ .socket receipt :: after.filterMap old? := by
    rw [projected,position]
    simp only [List.filterMap_append,List.filterMap_cons,old?]
  apply Journal.SocketHistory.initialized trace placeholders receipt
  rw [oldPosition]
  simp only [List.filterMap_append,List.filterMap_cons,Journal.SocketHistory.socket?]
  exact List.mem_append_right _ (List.mem_cons_self)

/-- A retained actual transport socket call has its own legitimate causal
root and the native emission bound and endpoint/byte binding. The receipt and
cause survive any later Stop in completion accounting. -/
theorem socket (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (receipt : Completion.SocketReceipt)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .old (.socket receipt) :: after) :
    Rooted before ∧ receipt.Valid ∧
      SocketEmission receipt.endpoint receipt.packet.value.bytes receipt.packet.value.ds
        receipt.socket.before.wg.sent receipt.socket.after.wg.sent := by
  have valid := socket_valid trace placeholders before after receipt position
  exact ⟨initialized trace placeholders before after (.old (.socket receipt)) position True.intro,
    valid,valid.emission⟩

/-- Native keepalive preparation is a causal operation at its own actual
caller; canonical empty packet contents are not treated as authentication. -/
theorem keepalive (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (pid : PeerId) (receipt : WGRunWitness Bool)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .keepalivePrepared pid receipt :: after) :
    Rooted before ∧ receipt.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid) :=
  ⟨initialized trace placeholders before after (.keepalivePrepared pid receipt) position True.intro,
    Receipts.initialized_keepalive trace placeholders before after pid receipt position⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Roots
