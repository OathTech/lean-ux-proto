import Leanux.Proofs.WG.Config.KeyStageEntryModel
import Leanux.Proofs.WG.Config.KeyStageSource
import Leanux.Proofs.WG.Config.RequestOrderInspectionSource

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

theorem lift_before {α : Type} (cs : Ledger) (loans : Reservations) (a : WG.M α)
    (kept : Preserves (Entry cs loans) a) :
    StatePrefixPreserves (Before cs loans) (FundedEntries cs loans)
      (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift a (fun _ _ _ pre=>pre.1)
  intro h g ambient value v after pre run
  exact ⟨pre.1,(hoare_iff_run_ambient _ _ _).mp kept g ambient value v after pre.2 run⟩

theorem mark_before (cs : Ledger) (loans : Reservations) (site : Decision) (value : Bool) :
    StatePrefixPreserves (Before cs loans) (FundedEntries cs loans) (mark site value) :=
  lift_before cs loans _ (((RequestOrder.Internal.ambient_frame (AmbientM.branch site value)).bind
    (fun _=>SameView.pure _ ())).wp (Entry cs loans))

theorem record_before (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (kind : Kind) (kept : Preserves (Entry cs loans) (action attrs kind)) :
    StatePrefixPreserves (Before cs loans) (FundedEntries cs loans)
      (record attrs kind) := by
  intro g ambient h pre
  have hc := runWGPrefix_receiptWGObserved
    (liftWGPrefix (action attrs kind)) (receipt kind) g ambient h
  rw [runWGPrefix_lift] at hc
  simp only [runWGPrefix,runStatePrefix] at hc
  unfold RequestOrder.record
  rw [hc]
  cases run : ((action attrs kind).run g).run ambient with
  | error stop => exact ⟨[],by simp,pre.1,trivial⟩
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    have hist : FundedEntries cs loans (h ++ [receipt kind ⟨ret,g,v,ambient,after⟩]) := by
      intro r member chosen
      rcases List.mem_append.mp member with old | fresh
      · exact pre.1 r old chosen
      · have same := List.mem_singleton.mp fresh
        subst r
        exact (entry_snapshot cs loans g ambient).mpr pre.2
    exact ⟨[receipt kind ⟨ret,g,v,ambient,after⟩],rfl,hist,hist,
      (hoare_iff_run_ambient _ _ _).mp kept g ambient ret v after pre.2 run⟩

theorem stage_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    Preserves (Entry cs loans) (keyStage attrs) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a ret v b pre run
  obtain ⟨d,device,_⟩ := pre.2
  exact (stage_effect cs loans attrs d g a ret v b ⟨pre,device⟩ run).2.1

theorem peers_funded (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>FundedEntries cs loans h) (FundedEntries cs loans)
      (peers attrs) := by
  intro g a h pre
  obtain ⟨suffix,eq,path,_⟩ := peers_conforms attrs g a h
  have safe : FundedEntries cs loans (runWGPrefix (peers attrs) g a h).2 := by
    rw [eq]
    intro r member key
    rcases List.mem_append.mp member with old | fresh
    · exact pre r old key
    · have member' : r∈peerReceipts suffix := path.peerReceipts.symm ▸ fresh
      have flag := (List.mem_filter.mp member').2
      simp [key] at flag
  refine ⟨suffix,eq,safe,?_⟩
  simp only [runWGPrefix,runStatePrefix] at safe ⊢
  cases run : (runPrefix ((peers attrs).run g) a h).1 with
  | error stop => trivial
  | ok out => exact safe

theorem keyed_funded (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (keyed attrs)
      (fun _ h _ _=>FundedEntries cs loans h) := by
  apply StatePrefixEnsures.bind (record_before cs loans attrs .keyStage (stage_entry cs loans attrs))
  intro _
  exact (peers_funded cs loans attrs).consequence (fun _ _ _ pre=>pre.1)
    (fun _ _ _ _ pre=>pre)

theorem quiet_before {α : Type} (cs : Ledger) (loans : Reservations) (value : α) :
    StatePrefixPreserves (Before cs loans) (FundedEntries cs loans) (pure value) :=
  StatePrefixEnsures.pure value (fun _ _ _ pre=>pre.1) (fun _ _ _ pre=>pre)

theorem finish_before (cs : Ledger) (loans : Reservations) (ret : Int) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (pure ret : WGPrefix Receipt Int)
      (fun _ h _ _=>FundedEntries cs loans h) :=
  StatePrefixEnsures.pure ret (fun _ _ _ pre=>pre.1) (fun _ _ _ pre=>pre.1)

theorem afterPort_funded (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (afterPort attrs flags)
      (fun _ h _ _=>FundedEntries cs loans h) := by
  unfold afterPort
  apply StatePrefixEnsures.bind (mark_before cs loans _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (record_before cs loans attrs .replacement ?_)
    · intro _; exact keyed_funded cs loans attrs
    · exact preserves_bind
        (join_ready cs loans _ (Index.ConfigurationIndex.bulk_entry cs loans) bulk_ready)
        (fun _=>preserves_pure _)
  · exact keyed_funded cs loans attrs

theorem afterFwmark_funded (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (afterFwmark attrs flags)
      (fun _ h _ _=>FundedEntries cs loans h) := by
  unfold afterFwmark
  apply StatePrefixEnsures.bind (mark_before cs loans _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (record_before cs loans attrs (.port _) ?_)
    · intro ret
      apply StatePrefixEnsures.bind (mark_before cs loans _ _)
      intro _
      split
      · exact StatePrefixEnsures.bind (mark_before cs loans _ _) (fun _=>finish_before cs loans ret)
      · exact afterPort_funded cs loans attrs flags
    · exact join_ready cs loans _ (Index.ConfigurationIndex.port_entry cs loans _) (port_ready _)
  · exact afterPort_funded cs loans attrs flags

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
      (fun _ h _ _=>FundedEntries cs loans h) := by
  rw [update_factor]
  apply StatePrefixEnsures.bind (Q := fun _=>Before cs loans) ?_ (fun _=>afterFwmark_funded cs loans attrs flags)
  apply StatePrefixEnsures.bind (mark_before cs loans _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (field_before cs loans (fun d=>{d with fwmark:=attrs.fwmark.getD 0}) (fun _=>rfl))
    intro _
    apply StatePrefixEnsures.bind (lift_before cs loans getDev get_ready)
    intro d
    apply StatePrefixEnsures.bind (Q := fun _=>Before cs loans) ?_ (fun _=>mark_before cs loans _ _)
    apply StatePrefixEnsures.forInInvariant d.peerList () _ (fun _=>Before cs loans)
      (FundedEntries cs loans) (fun _ _ _ _ pre=>pre.1)
    intro pid out
    apply StatePrefixEnsures.bind (mark_before cs loans _ _)
    intro _
    apply StatePrefixEnsures.bind (record_before cs loans attrs (.clearSource pid) ?_)
    · intro _; exact quiet_before cs loans _
    · exact preserves_bind
        (join_ready cs loans _ (Index.ConfigurationIndex.clearEndpoint_entry cs loans pid) (clearEndpoint_ready pid))
        (fun _=>preserves_pure _)
  · exact quiet_before cs loans ()

theorem accepted_funded (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (accepted attrs flags)
      (fun _ h _ _=>FundedEntries cs loans h) := by
  apply StatePrefixEnsures.bind (record_before cs loans attrs (.updateEntry flags) ?_)
  · intro _; exact update_funded cs loans attrs flags
  · exact preserves_bind
      (join_ready cs loans _
        (Index.ConfigurationIndex.configuration_entry cs loans (fun initial=>
          modifyDev_configuration_spec (fun s=>s=initial) _ (fun _=>rfl)))
        (configuration_ready _ (fun initial=>
          modifyDev_configuration_spec (fun s=>s=initial) _ (fun _=>rfl))))
      (fun _=>preserves_pure _)

theorem observe_funded (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    StatePrefixEnsures (Before cs loans) (FundedEntries cs loans) (observe attrs)
      (fun _ h _ _=>FundedEntries cs loans h) := by
  apply observe_entry_rule attrs
  · exact finish_before cs loans
  · exact mark_before cs loans
  · exact lift_before cs loans _ ((lookupInterface_sameWGWorld _).wp (Entry cs loans))
  · exact lift_before cs loans _ get_ready
  · exact lift_before cs loans _ ((RequestOrder.Internal.ambient_frame _).wp (Entry cs loans))
  · intro left right a b
    exact lift_before cs loans _ ((RequestOrder.Internal.branch_or_frame left right a b).wp (Entry cs loans))
  · exact accepted_funded cs loans attrs _

theorem inspection_funded (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (g : WGWorld) (a : Ambient) (pre : Entry cs loans g) :
    FundedEntries cs loans (inspection attrs g a).receipts := by
  obtain ⟨_,_,safe,_⟩ := observe_funded cs loans attrs g a []
    ⟨by simp [FundedEntries],pre⟩
  exact safe


end Leanux.Proofs.WG.Config.KeyStage
