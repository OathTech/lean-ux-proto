import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionOuter
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionRunner

/-! Initialized execution certifies every delivery-entry sent occurrence in
its exact earlier append stream. Delivery certificates survive later Stop and
buffer clearing; no terminal-state membership inference is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (execute trace placeholders) []).2 := by
  apply EmissionRunner.executeTraceWith (fun h w => Carrier h w.wg) Safe
    (fun _ _ hi => hi.2)
    (fun _ _ _ same hi => ⟨hi.1.sent_equal same,hi.2⟩)
    _ Carrier.syscall trace placeholders
  intro w same
  refine ⟨Inv.empty ?_,Safe.empty⟩
  rw [same]
  cases trace.net <;> cases trace.bare <;> rfl

/-- The actual initialized delivery prefix contains a distinct native append
ordinal for each position, including equal-valued datagrams and later Stops. -/
theorem initialized_occurrence (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (sent : List SentDatagram)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .delivery sent :: after)
    (index : Nat) (datagram : SentDatagram) (atPosition : sent[index]? = some datagram) :
    Occurrence before ((emitted before).length - sent.length + index) datagram :=
  (initialized trace placeholders).locate position index datagram atPosition

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
