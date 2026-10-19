import Leanux.Proofs.WG.Config.RequestInputFieldSource
import Leanux.Proofs.WG.Config.RequestInputFrames
import Leanux.Proofs.WG.Config.RequestOrderInspectionSource

/-! The unchanged request observer links its completed port input to the original entry. Stops retain completed receipts. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

theorem Conforms.input_closed {α : Type} {action : WGPrefix Receipt α} {L : Language α}
    (law : Conforms action L) (silent : PortSilent L)
    (attrs : DeviceAttrs) (initial : Campaign2.State) :
    StatePrefixPreserves (fun h _ _ => InputHistory attrs initial h)
      (InputHistory attrs initial) action := by
  intro w ambient h point
  obtain ⟨added,eq,path,_⟩ := law w ambient h
  have all : InputHistory attrs initial (runWGPrefix action w ambient h).2 := by
    rw [eq]
    exact point.append (silent added path).input
  refine ⟨added,eq,all,?_⟩
  simp only [runWGPrefix,runStatePrefix] at all ⊢
  cases run : (runPrefix (action.run w) ambient h).1 with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    exact all

theorem input_lift {α : Type} (attrs : DeviceAttrs) (initial : Campaign2.State) (a : WG.M α) :
    StatePrefixPreserves (fun h _ _ => InputHistory attrs initial h)
      (InputHistory attrs initial) (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ point => point)
    (fun _ _ _ _ _ _ point _ => point)

theorem input_pure {α : Type} (attrs : DeviceAttrs) (initial : Campaign2.State) (x : α) :
    StatePrefixPreserves (fun h _ _ => InputHistory attrs initial h)
      (InputHistory attrs initial) (pure x : WGPrefix Receipt α) :=
  StatePrefixEnsures.pure x (fun _ _ _ point => point) (fun _ _ _ point => point)

theorem fwmarkObserved_input (attrs : DeviceAttrs) (initial : Campaign2.State)
    (start : WGWorld) (a : Ambient) :
    StatePrefixEnsures (fun h w _ => InputHistory attrs initial h ∧ w = start)
      (InputHistory attrs initial) (fwmarkObserved attrs)
      (fun _ h w _ => InputHistory attrs initial h ∧
        MarkInput attrs (Campaign2.snapshot start a).wg (Campaign2.snapshot w a).wg) := by
  intro w ambient h point
  rcases point with ⟨prior,rfl⟩
  obtain ⟨added,eq,path,_⟩ := fwmarkObserved_conforms attrs w ambient h
  have all : InputHistory attrs initial (runWGPrefix (fwmarkObserved attrs) w ambient h).2 := by
    rw [eq]
    exact prior.append ((fwmarkObserved_portSilent attrs) added path).input
  refine ⟨added,eq,all,?_⟩
  simp only [runWGPrefix,runStatePrefix] at all ⊢
  cases run : (runPrefix ((fwmarkObserved attrs).run w) ambient h).1 with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    have native : ((fwmarkSource attrs).run w).run ambient = .ok ((ret,v),after) :=
      (fwmarkObserved_erases attrs w ambient h).symm.trans run
    exact ⟨all,fwmarkSource_fields attrs w a w ambient ret v after rfl native⟩

theorem record_port_input (attrs : DeviceAttrs) (initial : Campaign2.State)
    (port : Nat) (a : Ambient) :
    StatePrefixEnsures (fun h w _ => InputHistory attrs initial h ∧
      MarkInput attrs (incrementState initial) (Campaign2.snapshot w a).wg)
      (InputHistory attrs initial) (record attrs (.port port))
      (fun _ h _ _ => InputHistory attrs initial h) := by
  have captured : StatePrefixEnsures
      (fun h w _ => InputHistory attrs initial h ∧
        MarkInput attrs (incrementState initial) (Campaign2.snapshot w a).wg)
      (InputHistory attrs initial)
      (Logged.captureWGRun (action attrs (.port port)))
      (fun native h _ _ => InputHistory attrs initial h ∧
        PortInput attrs initial (receipt (.port port) native)) :=
    StatePrefixEnsures.captureWGRun _ (fun _ _ _ point => point.1)
      (fun _ _ _ _ _ _ point _ => point)
  unfold record receiptWGObserved
  apply StatePrefixEnsures.bind captured
  intro native
  have added : ∀ h, InputHistory attrs initial h ∧
      PortInput attrs initial (receipt (.port port) native) →
      InputHistory attrs initial (h ++ [receipt (.port port) native]) := by
    intro h point
    apply point.1.append
    intro r member p kind
    have eq : r = receipt (.port port) native := List.mem_singleton.mp member
    subst r
    exact point.2
  apply StatePrefixEnsures.bind
    (StatePrefixEnsures.emit (Q := fun _ h _ _ => InputHistory attrs initial h)
      (receipt (.port port) native) (fun h _ _ point => added h point)
      (fun h _ _ point => added h point))
  intro _
  exact input_pure attrs initial native.value

theorem afterFwmark_input (attrs : DeviceAttrs) (flags : UInt32)
    (initial : Campaign2.State) (a : Ambient) :
    StatePrefixEnsures (fun h w _ => InputHistory attrs initial h ∧
      MarkInput attrs (incrementState initial) (Campaign2.snapshot w a).wg)
      (InputHistory attrs initial) (afterFwmark attrs flags)
      (fun _ h _ _ => InputHistory attrs initial h) := by
  have suffix := (afterPort_conforms attrs flags).input_closed
    (afterPort_portSilent attrs flags) attrs initial
  unfold afterFwmark
  apply StatePrefixEnsures.bind (input_mark attrs initial _ _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (record_port_input attrs initial _ a)
    intro ret
    apply StatePrefixEnsures.bind (input_lift attrs initial _)
    intro _
    split
    · exact StatePrefixEnsures.bind (input_lift attrs initial _)
        (fun _ => input_pure attrs initial ret)
    · exact suffix
  · exact suffix.consequence (fun _ _ _ point => point.1)
      (fun _ _ _ _ point => point)

def generationWorld (w : WGWorld) : WGWorld :=
  {w with dev := w.dev.map fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}}

theorem update_input (attrs : DeviceAttrs) (flags : UInt32) (initial : WGWorld) (a : Ambient) :
    StatePrefixEnsures (fun h w _ =>
      InputHistory attrs (Campaign2.snapshot initial a).wg h ∧ w = generationWorld initial)
      (InputHistory attrs (Campaign2.snapshot initial a).wg) (update attrs flags)
      (fun _ h _ _ => InputHistory attrs (Campaign2.snapshot initial a).wg h) := by
  rw [update_fwmark_factor]
  exact StatePrefixEnsures.bind
    (fwmarkObserved_input attrs (Campaign2.snapshot initial a).wg (generationWorld initial) a)
    (fun _ => afterFwmark_input attrs flags (Campaign2.snapshot initial a).wg a)

theorem entry_input (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient) :
    StatePrefixEnsures (fun h w _ =>
      InputHistory attrs (Campaign2.snapshot initial a).wg h ∧ w = initial)
      (InputHistory attrs (Campaign2.snapshot initial a).wg)
      (record attrs (.updateEntry (attrs.flags.getD 0)))
      (fun _ h w _ => InputHistory attrs (Campaign2.snapshot initial a).wg h ∧
        w = generationWorld initial) := by
  intro w ambient h point
  rcases point with ⟨prior,rfl⟩
  let r := receipt (.updateEntry (attrs.flags.getD 0))
    ⟨0,w,generationWorld w,ambient,ambient⟩
  have all : InputHistory attrs (Campaign2.snapshot w a).wg (h ++ [r]) :=
    prior.append (fun other member port kind => by
      have same : other = r := List.mem_singleton.mp member
      subst other
      cases kind)
  exact ⟨[r],rfl,all,all,rfl⟩

theorem observe_input (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient) :
    StatePrefixEnsures (fun h w _ =>
      InputHistory attrs (Campaign2.snapshot initial a).wg h ∧ w = initial)
      (InputHistory attrs (Campaign2.snapshot initial a).wg) (observe attrs)
      (fun _ h _ _ => InputHistory attrs (Campaign2.snapshot initial a).wg h) := by
  apply observe_entry_rule attrs
  · intro ret
    exact StatePrefixEnsures.pure ret (fun _ _ _ point => point.1)
      (fun _ _ _ point => point.1)
  · exact fun site value => input_mark attrs _ (fun w => w = initial) site value
  · exact input_frame attrs _ _ _
      (Leanux.Proofs.Framing.lookupInterface_sameWGWorld _)
  · exact input_frame attrs _ _ _ Internal.getDev_frame
  · exact input_frame attrs _ _ _ (Internal.ambient_frame _)
  · exact fun left right b c => input_frame attrs _ _ _ (Internal.branch_or_frame left right b c)
  · exact StatePrefixEnsures.bind (entry_input attrs initial a)
      (fun _ => update_input attrs _ initial a)

theorem inspection_input (attrs : DeviceAttrs) (w : WGWorld) (ambient : Ambient) :
    InputHistory attrs (Campaign2.snapshot w ambient).wg (inspection attrs w ambient).receipts := by
  obtain ⟨_,_,safe,_⟩ := observe_input attrs w ambient w ambient []
    ⟨by simp [InputHistory],rfl⟩
  exact safe

end Leanux.Proofs.WG.Config.RequestOrder
