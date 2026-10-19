import Leanux.Proofs.WG.Config.ReplacementCompletionBridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.ReplaceCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Queues.RxCredits Queues.RxCredits.DurableHolders AllowedIps Std.Do Lifetimes

/-- The whole flag-only REPLACE_PEERS request, including both saved cleanup
passes and their actual work drains. Only normal completion is asserted:
zero return, an empty configured list/public-key table and empty represented
IPv4/IPv6 routes. No empty-work, final-state or physical-store-empty premise. -/
theorem request_completion (cs : Ledger) (loans : Reservations)
    (tables : FlatTable × FlatTable) (d : Device) :
    Campaign2.Ensures (wgSetDevice (replacePeersAttrs (byIndex d)))
      (fun s => s.wg.device=some d ∧ ClaimView.selectsDevice s d ∧
        View.Input cs loans tables s)
      (fun result s => result=0 ∧ View.Empty s) := by
  intro w a result v b pre run
  exact request_empty cs loans tables d w a result v b
    ⟨pre.1,pre.2.1,(input_snapshot cs loans tables w a).mp pre.2.2⟩ run

/-- The original whole bulk cleanup, without the request's interface-selection
and generation prefix, has the same derived empty endpoint. -/
theorem removal_completion (cs : Ledger) (loans : Reservations)
    (tables : FlatTable × FlatTable) :
    Campaign2.Ensures peerRemoveAll (View.Input cs loans tables)
      (fun _ s => View.Empty s) := by
  intro w a result v b pre run
  cases result
  obtain ⟨⟨holders,funded,stable⟩,base,routing⟩ :=
    (input_snapshot cs loans tables w a).mp pre
  exact removeAll_empty holders cs loans tables w v a b funded stable base routing run

end Leanux.Proofs.WG.Config.ReplaceCompletion
