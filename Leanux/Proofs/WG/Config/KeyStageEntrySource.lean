import Leanux.Proofs.WG.Config.KeyStageEntryModel
import Leanux.Proofs.WG.Config.KeyStageSource
import Leanux.Proofs.WG.Config.RequestOrderInspectionSource
import Leanux.Proofs.WG.Config.RequestKeyEntriesSource

/-! The actual device request supplies each completed private-key stage's account.
Only the pre-key phases carry the live account. The existing peer grammar keeps
the historical fact across arbitrary later attributes and Stops. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.KeyStage
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux.Proofs.Logged RequestOrder

def Before (cs : Ledger) (loans : Reservations)
    (h : List Receipt) (g : WGWorld) (_ : Ambient) : Prop :=
  FundedEntries cs loans h ∧ Entry cs loans g

theorem funded_contracts (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    EntryTransport.Contracts (Entry cs loans) (ProjectedEntry cs loans) attrs where
  projected g a pre := (entry_snapshot cs loans g a).mpr pre
  generation _ :=
    preserves_bind
      (join_ready cs loans _
        (Index.ConfigurationIndex.configuration_entry cs loans (fun initial=>
          modifyDev_configuration_spec (fun s=>s=initial) _ (fun _=>rfl)))
        (configuration_ready _ (fun initial=>
          modifyDev_configuration_spec (fun s=>s=initial) _ (fun _=>rfl))))
      (fun _=>preserves_pure _)
  fwmark :=
    join_ready cs loans _
      (Index.ConfigurationIndex.configuration_entry cs loans (fun initial=>
        modifyDev_configuration_spec (fun s=>s=initial) _ (fun _=>rfl)))
      (configuration_ready _ (fun initial=>
        modifyDev_configuration_spec (fun s=>s=initial) _ (fun _=>rfl)))
  clear pid :=
    preserves_bind
      (join_ready cs loans _ (Index.ConfigurationIndex.clearEndpoint_entry cs loans pid) (clearEndpoint_ready pid))
      (fun _=>preserves_pure _)
  port port := join_ready cs loans _ (Index.ConfigurationIndex.port_entry cs loans port) (port_ready port)
  replacement :=
    preserves_bind (join_ready cs loans _ (Index.ConfigurationIndex.bulk_entry cs loans) bulk_ready)
      (fun _=>preserves_pure _)

theorem lift_before {α : Type} (cs : Ledger) (loans : Reservations) (a : WG.M α)
    (kept : Preserves (Entry cs loans) a) :
    StatePrefixPreserves (Before cs loans) (FundedEntries cs loans)
      (liftWGPrefix a) :=
  EntryTransport.lift_before (Entry cs loans) (ProjectedEntry cs loans) a kept

theorem mark_before (cs : Ledger) (loans : Reservations) (site : Decision) (value : Bool) :
    StatePrefixPreserves (Before cs loans) (FundedEntries cs loans) (mark site value) :=
  EntryTransport.mark_before (Entry cs loans) (ProjectedEntry cs loans) site value

theorem record_before (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (kind : Kind) (kept : Preserves (Entry cs loans) (action attrs kind)) :
    StatePrefixPreserves (Before cs loans) (FundedEntries cs loans)
      (record attrs kind) :=
  EntryTransport.record_before (Entry cs loans) (ProjectedEntry cs loans)
    (fun g a pre=>(entry_snapshot cs loans g a).mpr pre) attrs kind kept

theorem stage_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    Preserves (Entry cs loans) (keyStage attrs) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a ret v b pre run
  obtain ⟨d,device,_⟩ := pre.2
  exact (stage_effect cs loans attrs d g a ret v b ⟨pre,device⟩ run).2.1

theorem peers_funded (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>FundedEntries cs loans h) (FundedEntries cs loans)
      (peers attrs) :=
  EntryTransport.peers_history (ProjectedEntry cs loans) attrs

theorem keyed_funded (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (keyed attrs)
      (fun _ h _ _=>FundedEntries cs loans h) :=
  EntryTransport.keyed_history (Entry cs loans) (ProjectedEntry cs loans)
    (fun g a pre=>(entry_snapshot cs loans g a).mpr pre) attrs

theorem quiet_before {α : Type} (cs : Ledger) (loans : Reservations) (value : α) :
    StatePrefixPreserves (Before cs loans) (FundedEntries cs loans) (pure value) :=
  EntryTransport.quiet_before (Entry cs loans) (ProjectedEntry cs loans) value

theorem finish_before (cs : Ledger) (loans : Reservations) (ret : Int) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (pure ret : WGPrefix Receipt Int)
      (fun _ h _ _=>FundedEntries cs loans h) :=
  EntryTransport.finish_before (Entry cs loans) (ProjectedEntry cs loans) ret

theorem afterPort_funded (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (afterPort attrs flags)
      (fun _ h _ _=>FundedEntries cs loans h) :=
  EntryTransport.afterPort_history (Entry cs loans) (ProjectedEntry cs loans)
    attrs (funded_contracts cs loans attrs) flags

theorem afterFwmark_funded (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (afterFwmark attrs flags)
      (fun _ h _ _=>FundedEntries cs loans h) :=
  EntryTransport.afterFwmark_history (Entry cs loans) (ProjectedEntry cs loans)
    attrs (funded_contracts cs loans attrs) flags

theorem field_before (cs : Ledger) (loans : Reservations) (f : Device → Device)
    (same : ∀d, configurationDevice (f d)=configurationDevice d) :
    StatePrefixPreserves (Before cs loans) (FundedEntries cs loans) (liftWGPrefix (modifyDev f)) := by
  apply lift_before cs loans
  apply join_ready cs loans
  · apply Index.ConfigurationIndex.configuration_entry cs loans
    intro initial
    exact modifyDev_configuration_spec (fun s=>s=initial) f same
  · apply configuration_ready
    intro initial
    exact modifyDev_configuration_spec (fun s=>s=initial) f same

theorem update_funded (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (update attrs flags)
      (fun _ h _ _=>FundedEntries cs loans h) :=
  EntryTransport.update_history (Entry cs loans) (ProjectedEntry cs loans)
    attrs (funded_contracts cs loans attrs) flags

theorem accepted_funded (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (accepted attrs flags)
      (fun _ h _ _=>FundedEntries cs loans h) :=
  EntryTransport.accepted_history (Entry cs loans) (ProjectedEntry cs loans)
    attrs (funded_contracts cs loans attrs) flags

theorem observe_funded (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (observe attrs)
      (fun _ h _ _=>FundedEntries cs loans h) :=
  EntryTransport.observe_history (Entry cs loans) (ProjectedEntry cs loans)
    attrs (funded_contracts cs loans attrs)

theorem inspection_funded (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (g : WGWorld) (a : Ambient) (pre : Entry cs loans g) :
    FundedEntries cs loans (inspection attrs g a).receipts :=
  EntryTransport.inspection_history (Entry cs loans) (ProjectedEntry cs loans)
    attrs (funded_contracts cs loans attrs) g a pre


end Leanux.Proofs.WG.Config.KeyStage
