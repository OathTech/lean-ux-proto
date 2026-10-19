import Leanux.Proofs.WG.Config.RequestKeyEntriesModel
import Leanux.Proofs.WG.Config.RequestRecordSource
import Leanux.Proofs.WG.Config.RequestOrderInspectionSource
import Leanux.Proofs.WG.Config.ConfiguredDeviceLeavesSource

/-! The existing request observer carries a live predicate only through the pre-key prefix. Actual recorded key-stage entries remain certified after later attributes or Stops. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.EntryTransport
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration
open Leanux.Proofs.Logged

def Before (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (h : List Receipt) (g : WGWorld) (_ : Ambient) : Prop :=
  KeyEntries F h ∧ P g

structure Contracts (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (attrs : DeviceAttrs) : Prop where
  projected : ∀g a,P g → F (Campaign2.snapshot g a)
  generation : ∀flags,Preserves P (action attrs (.updateEntry flags))
  fwmark : Preserves P (modifyDev fun d=>{d with fwmark:=attrs.fwmark.getD 0})
  clear : ∀pid,Preserves P (action attrs (.clearSource pid))
  port : ∀port,Preserves P (action attrs (.port port))
  replacement : Preserves P (action attrs .replacement)

theorem lift_before {α : Type} (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (a : WG.M α) (kept : Preserves P a) :
    StatePrefixPreserves (Before P F) (KeyEntries F) (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift a (fun _ _ _ pre=>pre.1)
  intro h g ambient value v after pre run
  exact ⟨pre.1,(hoare_iff_run_ambient _ _ _).mp kept g ambient value v after pre.2 run⟩

theorem mark_before (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (site : Decision) (value : Bool) :
    StatePrefixPreserves (Before P F) (KeyEntries F) (mark site value) :=
  lift_before P F _ (((Internal.ambient_frame (AmbientM.branch site value)).bind
    (fun _=>SameView.pure _ ())).wp P)

theorem receipt_entries (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (projected : ∀g a,P g→F (Campaign2.snapshot g a))
    (kind : Kind) (h : List Receipt) (g v : WGWorld) (a b : Ambient) (ret : Int)
    (pre : Before P F h g a) :
    KeyEntries F (h++[receipt kind ⟨ret,g,v,a,b⟩]) := by
  intro r member chosen
  rcases List.mem_append.mp member with old | fresh
  · exact pre.1 r old chosen
  · have same:=List.mem_singleton.mp fresh
    subst r
    exact projected g a pre.2

theorem record_before (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (projected : ∀g a,P g→F (Campaign2.snapshot g a))
    (attrs : DeviceAttrs) (kind : Kind) (kept : Preserves P (action attrs kind)) :
    StatePrefixPreserves (Before P F) (KeyEntries F) (record attrs kind) := by
  apply record_state_rule attrs kind (fun _ _ _ pre=>pre.1)
  intro h g a ret v b pre run
  have hist:=receipt_entries P F projected kind h g v a b ret pre
  exact ⟨hist,hist,(hoare_iff_run_ambient _ _ _).mp kept g a ret v b pre.2 run⟩

theorem record_history (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (projected : ∀g a,P g→F (Campaign2.snapshot g a))
    (attrs : DeviceAttrs) (kind : Kind) :
    StatePrefixEnsures (Before P F) (KeyEntries F) (record attrs kind)
      (fun _ h _ _=>KeyEntries F h) := by
  apply record_state_rule attrs kind (fun _ _ _ pre=>pre.1)
  intro h g a ret v b pre _
  have hist:=receipt_entries P F projected kind h g v a b ret pre
  exact ⟨hist,hist⟩

theorem peers_history (F : Campaign2.Snapshot → Prop) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>KeyEntries F h) (KeyEntries F) (peers attrs) := by
  intro g a h pre
  obtain ⟨suffix,eq,path,_⟩:=peers_conforms attrs g a h
  have safe : KeyEntries F (runWGPrefix (peers attrs) g a h).2 := by
    rw [eq]
    intro r member key
    rcases List.mem_append.mp member with old | fresh
    · exact pre r old key
    · have member' : r∈peerReceipts suffix:=path.peerReceipts.symm ▸ fresh
      have flag:=(List.mem_filter.mp member').2
      simp [key] at flag
  refine ⟨suffix,eq,safe,?_⟩
  simp only [runWGPrefix,runStatePrefix] at safe ⊢
  cases run : (runPrefix ((peers attrs).run g) a h).1 with
  | error stop=>trivial
  | ok out=>exact safe

theorem keyed_history (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (projected : ∀g a,P g→F (Campaign2.snapshot g a)) (attrs : DeviceAttrs) :
    StatePrefixEnsures (Before P F) (KeyEntries F) (keyed attrs)
      (fun _ h _ _=>KeyEntries F h) := by
  exact StatePrefixEnsures.bind (record_history P F projected attrs .keyStage)
    (fun _=>peers_history F attrs)

theorem quiet_before {α : Type} (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop) (value : α) :
    StatePrefixPreserves (Before P F) (KeyEntries F) (pure value) :=
  StatePrefixEnsures.pure value (fun _ _ _ pre=>pre.1) (fun _ _ _ pre=>pre)

theorem finish_before (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop) (ret : Int) :
    StatePrefixEnsures (Before P F) (KeyEntries F) (pure ret : WGPrefix Receipt Int)
      (fun _ h _ _=>KeyEntries F h) :=
  StatePrefixEnsures.pure ret (fun _ _ _ pre=>pre.1) (fun _ _ _ pre=>pre.1)

theorem afterPort_history (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (attrs : DeviceAttrs) (c : Contracts P F attrs) (flags : UInt32) :
    StatePrefixEnsures (Before P F) (KeyEntries F) (afterPort attrs flags)
      (fun _ h _ _=>KeyEntries F h) := by
  unfold afterPort
  apply StatePrefixEnsures.bind (mark_before P F _ _)
  intro _
  split
  · exact StatePrefixEnsures.bind (record_before P F c.projected attrs .replacement c.replacement)
      (fun _=>keyed_history P F c.projected attrs)
  · exact keyed_history P F c.projected attrs

theorem afterFwmark_history (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (attrs : DeviceAttrs) (c : Contracts P F attrs) (flags : UInt32) :
    StatePrefixEnsures (Before P F) (KeyEntries F) (afterFwmark attrs flags)
      (fun _ h _ _=>KeyEntries F h) := by
  unfold afterFwmark
  apply StatePrefixEnsures.bind (mark_before P F _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (record_before P F c.projected attrs (.port _) (c.port _))
    intro ret
    apply StatePrefixEnsures.bind (mark_before P F _ _)
    intro _
    split
    · exact StatePrefixEnsures.bind (mark_before P F _ _) (fun _=>finish_before P F ret)
    · exact afterPort_history P F attrs c flags
  · exact afterPort_history P F attrs c flags

theorem update_history (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (attrs : DeviceAttrs) (c : Contracts P F attrs) (flags : UInt32) :
    StatePrefixEnsures (Before P F) (KeyEntries F) (update attrs flags)
      (fun _ h _ _=>KeyEntries F h) := by
  rw [update_factor]
  apply StatePrefixEnsures.bind (Q:=fun _=>Before P F) ?_ (fun _=>afterFwmark_history P F attrs c flags)
  apply StatePrefixEnsures.bind (mark_before P F _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (lift_before P F _ c.fwmark)
    intro _
    apply StatePrefixEnsures.bind (lift_before P F getDev OwnerConfiguration.get_ready)
    intro d
    apply StatePrefixEnsures.bind (Q:=fun _=>Before P F) ?_ (fun _=>mark_before P F _ _)
    apply StatePrefixEnsures.forInInvariant d.peerList () _ (fun _=>Before P F)
      (KeyEntries F) (fun _ _ _ _ pre=>pre.1)
    intro pid out
    apply StatePrefixEnsures.bind (mark_before P F _ _)
    intro _
    apply StatePrefixEnsures.bind (record_before P F c.projected attrs (.clearSource pid) (c.clear pid))
    intro _
    exact quiet_before P F _
  · exact quiet_before P F ()

theorem accepted_history (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (attrs : DeviceAttrs) (c : Contracts P F attrs) (flags : UInt32) :
    StatePrefixEnsures (Before P F) (KeyEntries F) (accepted attrs flags)
      (fun _ h _ _=>KeyEntries F h) :=
  StatePrefixEnsures.bind (record_before P F c.projected attrs (.updateEntry flags) (c.generation flags))
    (fun _=>update_history P F attrs c flags)

theorem observe_history (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (attrs : DeviceAttrs) (c : Contracts P F attrs) :
    StatePrefixEnsures (Before P F) (KeyEntries F) (observe attrs)
      (fun _ h _ _=>KeyEntries F h) := by
  apply observe_entry_rule attrs
  · exact finish_before P F
  · exact mark_before P F
  · exact lift_before P F _ ((lookupInterface_sameWGWorld _).wp P)
  · exact lift_before P F _ OwnerConfiguration.get_ready
  · exact lift_before P F _ ((Internal.ambient_frame _).wp P)
  · intro left right a b
    exact lift_before P F _ ((Internal.branch_or_frame left right a b).wp P)
  · exact accepted_history P F attrs c _

theorem inspection_history (P : WGWorld → Prop) (F : Campaign2.Snapshot → Prop)
    (attrs : DeviceAttrs) (c : Contracts P F attrs)
    (g : WGWorld) (a : Ambient) (pre : P g) :
    KeyEntries F (inspection attrs g a).receipts := by
  obtain ⟨_,_,safe,_⟩:=observe_history P F attrs c g a [] ⟨by simp [KeyEntries],pre⟩
  exact safe

end Leanux.Proofs.WG.Config.RequestOrder.EntryTransport
