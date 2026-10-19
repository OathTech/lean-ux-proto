import Leanux.Proofs.WG.Config.RequestKeyHeaderFrames
import Leanux.Proofs.WG.Config.RequestInputClaims

/-! Source-linked continuity through the unchanged request observer. Completed receipts survive later Stops; a stopped key-stage call has no completion receipt. The validation lemma excludes namespace refusal from any nonempty selected-port receipt history. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
open Leanux Leanux.WG Noise TimerDiscipline
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem record_rule (attrs : DeviceAttrs) (initial : Campaign2.State) (kind : Kind)
    {P : List Receipt→WGWorld→Ambient→Prop} {Q : Int→List Receipt→WGWorld→Ambient→Prop}
    (safe : ∀ h g a,P h g a→History attrs initial h)
    (normal : ∀ h g a ret v b,P h g a→((action attrs kind).run g).run a=.ok ((ret,v),b)→
      let r:=receipt kind ⟨ret,g,v,a,b⟩
      History attrs initial (h++[r]) ∧ Q ret (h++[r]) v b) :
    StatePrefixEnsures P (History attrs initial) (record attrs kind) Q := by
  intro g a h pre
  have source:=runWGPrefix_receiptWGObserved
    (liftWGPrefix (action attrs kind)) (receipt kind) g a h
  rw [runWGPrefix_lift] at source
  simp only [runWGPrefix,runStatePrefix] at source
  unfold record
  rw [source]
  cases run : ((action attrs kind).run g).run a with
  | error stop => exact ⟨[],by simp,safe h g a pre,trivial⟩
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,b⟩
    exact ⟨[receipt kind ⟨ret,g,v,a,b⟩],rfl,normal h g a ret v b pre run⟩

theorem history_frame {α : Type} (attrs : DeviceAttrs) (initial : Campaign2.State)
    (P : List Receipt→WGWorld→Prop) (action : WG.M α)
    (frame : SameView (id : WGWorld→WGWorld) action) :
    StatePrefixPreserves (fun h g _=>History attrs initial h ∧ P h g)
      (History attrs initial) (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift action (fun _ _ _ pre=>pre.1)
  intro h g a ret v b pre run
  have same : v=g := (ProjectedAction.iff_run_ambient _ _ _).mp frame g a ret v b run
  exact ⟨pre.1,same ▸ pre.2⟩

theorem history_mark (attrs : DeviceAttrs) (initial : Campaign2.State)
    (P : List Receipt→WGWorld→Prop) (site : Decision) (value : Bool) :
    StatePrefixPreserves (fun h g _=>History attrs initial h ∧ P h g)
      (History attrs initial) (mark site value) :=
  history_frame attrs initial P _
    ((Internal.ambient_frame (AmbientM.branch site value)).bind (fun _=>SameView.pure _ ()))

theorem peers_history (attrs : DeviceAttrs) (initial : Campaign2.State) :
    StatePrefixPreserves (fun h _ _=>History attrs initial h) (History attrs initial)
      (peers attrs) := by
  intro g a h pre
  obtain ⟨added,eq,path,_⟩:=peers_conforms attrs g a h
  have kept : History attrs initial (runWGPrefix (peers attrs) g a h).2 := by
    rw [eq]
    apply pre.append
    intro r member kind
    have selected : r∈peerReceipts added := path.peerReceipts.symm ▸ member
    have chosen:=(List.mem_filter.mp selected).2
    simp [kind] at chosen
  refine ⟨added,eq,kept,?_⟩
  simp only [runWGPrefix,runStatePrefix] at kept ⊢
  cases run : (runPrefix ((peers attrs).run g) a h).1 with
  | error stop => trivial
  | ok out => exact kept

theorem keyed_history (attrs : DeviceAttrs) (initial : Campaign2.State) (z : Ambient) :
    StatePrefixEnsures (fun h g _=>History attrs initial h ∧ At attrs initial h (Campaign2.snapshot g z).wg)
      (History attrs initial) (keyed attrs) (fun _ h _ _=>History attrs initial h) := by
  apply StatePrefixEnsures.bind (record_rule attrs initial .keyStage (fun _ _ _ pre=>pre.1) ?_)
  · intro _; exact peers_history attrs initial
  · intro h g a ret v b pre run
    have next : History attrs initial (h++[receipt .keyStage ⟨ret,g,v,a,b⟩]) := by
      apply pre.1.append
      intro r member kind
      have same:=List.mem_singleton.mp member
      subst r
      exact pre.2.mono (fun _ seen=>List.mem_append_left _ seen)
    exact ⟨next,next⟩

theorem replacement_history (attrs : DeviceAttrs) (initial : Campaign2.State) (z : Ambient) :
    StatePrefixPreserves (fun h g _=>History attrs initial h ∧ At attrs initial h (Campaign2.snapshot g z).wg)
      (History attrs initial) (record attrs .replacement) := by
  apply record_rule attrs initial .replacement (fun _ _ _ pre=>pre.1)
  intro h g a ret v b pre run
  have hist : History attrs initial (h++[receipt .replacement ⟨ret,g,v,a,b⟩]) := by
    apply pre.1.append
    intro r member kind
    have same:=List.mem_singleton.mp member
    subst r
    cases kind
  have effect : SameView getterMetadata (action attrs .replacement) :=
    GetterCleanup.remove_all.bind (fun _=>SameView.pure _ (0:Int))
  have same:=(ProjectedAction.iff_run_ambient _ _ _).mp effect g a ret v b run
  have header:=congrArg (fun m=>m.map Prod.fst) same
  simp only [getterMetadata,Option.map_map,Function.comp_def] at header
  change v.dev.map sendConfiguration=g.dev.map sendConfiguration at header
  exact ⟨hist,hist,(pre.2.header header).mono (fun _ seen=>List.mem_append_left _ seen)⟩

theorem afterPort_history (attrs : DeviceAttrs) (flags : UInt32)
    (initial : Campaign2.State) (z : Ambient) :
    StatePrefixEnsures (fun h g _=>History attrs initial h ∧ At attrs initial h (Campaign2.snapshot g z).wg)
      (History attrs initial) (afterPort attrs flags) (fun _ h _ _=>History attrs initial h) := by
  unfold afterPort
  apply StatePrefixEnsures.bind (history_mark attrs initial _ _ _)
  intro _
  split
  · exact StatePrefixEnsures.bind (replacement_history attrs initial z)
      (fun _=>keyed_history attrs initial z)
  · exact keyed_history attrs initial z

theorem port_history (attrs : DeviceAttrs) (initial : Campaign2.State) (z : Ambient)
    (port : Nat) (selected : attrs.listenPort=some port) :
    StatePrefixEnsures (fun h g _=>History attrs initial h ∧
      MarkInput attrs (incrementState initial) (Campaign2.snapshot g z).wg)
      (History attrs initial) (record attrs (.port port))
      (fun ret h g _=>History attrs initial h ∧
        (ret=0→At attrs initial h (Campaign2.snapshot g z).wg)) := by
  apply record_rule attrs initial (.port port) (fun _ _ _ pre=>pre.1)
  intro h g a ret v b pre run
  let r:=receipt (.port port) ⟨ret,g,v,a,b⟩
  have hist : History attrs initial (h++[r]) := by
    apply pre.1.append
    intro other member kind
    have same:=List.mem_singleton.mp member
    subst other
    cases kind
  refine ⟨hist,hist,?_⟩
  intro zero
  have same:=(ProjectedAction.iff_run_ambient _ _ _).mp (port_fixed port) g a ret v b run
  refine ⟨same.trans (MarkInput.core pre.2),?_⟩
  simp only [PortOrigin,selected]
  exact ⟨r,List.mem_append_right _ (by simp [r]),rfl,zero,rfl⟩

theorem afterFwmark_history (attrs : DeviceAttrs) (flags : UInt32)
    (initial : Campaign2.State) (z : Ambient) :
    StatePrefixEnsures (fun h g _=>History attrs initial h ∧
      MarkInput attrs (incrementState initial) (Campaign2.snapshot g z).wg)
      (History attrs initial) (afterFwmark attrs flags)
      (fun _ h _ _=>History attrs initial h) := by
  unfold afterFwmark
  apply StatePrefixEnsures.bind (history_mark attrs initial _ _ _)
  intro _
  cases selected : attrs.listenPort with
  | none =>
    simp only [Option.isSome_none,Bool.false_eq_true,ite_false]
    exact (afterPort_history attrs flags initial z).consequence
      (fun _ _ _ pre=>⟨pre.1,MarkInput.portless selected pre.2⟩) (fun _ _ _ _ pre=>pre)
  | some port =>
    simp only [Option.isSome_some,ite_true,Option.getD_some]
    apply StatePrefixEnsures.bind (port_history attrs initial z port selected)
    intro ret
    apply StatePrefixEnsures.bind (history_mark attrs initial _ _ _)
    intro _
    split
    · unfold zero
      exact StatePrefixEnsures.bind (history_mark attrs initial _ _ _)
        (fun _=>StatePrefixEnsures.pure ret (fun _ _ _ pre=>pre.1) (fun _ _ _ pre=>pre.1))
    · rename_i normal
      exact (afterPort_history attrs flags initial z).consequence
        (fun _ _ _ pre=>⟨pre.1,pre.2 (by simpa using normal)⟩)
        (fun _ _ _ _ pre=>pre)

theorem fwmark_history (attrs : DeviceAttrs) (initial : Campaign2.State)
    (start : WGWorld) (z : Ambient) :
    StatePrefixEnsures (fun h g _=>History attrs initial h ∧ g=start)
      (History attrs initial) (fwmarkObserved attrs)
      (fun _ h g _=>History attrs initial h ∧
        MarkInput attrs (Campaign2.snapshot start z).wg (Campaign2.snapshot g z).wg) := by
  intro g a h pre
  rcases pre with ⟨prior,same⟩
  subst g
  obtain ⟨added,eq,path,_⟩:=fwmarkObserved_conforms attrs start a h
  have hist : History attrs initial (runWGPrefix (fwmarkObserved attrs) start a h).2 := by
    rw [eq]
    apply prior.append
    intro r member kind
    obtain ⟨pid,clear⟩:=path.1 r member
    cases clear.symm.trans kind
  refine ⟨added,eq,hist,?_⟩
  simp only [runWGPrefix,runStatePrefix] at hist ⊢
  cases run : (runPrefix ((fwmarkObserved attrs).run start) a h).1 with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,b⟩
    have native : ((fwmarkSource attrs).run start).run a=.ok ((ret,v),b) :=
      (fwmarkObserved_erases attrs start a h).symm.trans run
    exact ⟨hist,fwmarkSource_fields attrs start z start a ret v b rfl native⟩

theorem update_history (attrs : DeviceAttrs) (flags : UInt32) (initial : WGWorld) (z : Ambient) :
    StatePrefixEnsures (fun h g _=>History attrs (Campaign2.snapshot initial z).wg h ∧
      g=generationWorld initial) (History attrs (Campaign2.snapshot initial z).wg)
      (update attrs flags) (fun _ h _ _=>History attrs (Campaign2.snapshot initial z).wg h) := by
  rw [update_fwmark_factor]
  exact StatePrefixEnsures.bind
    (fwmark_history attrs (Campaign2.snapshot initial z).wg (generationWorld initial) z)
    (fun _=>afterFwmark_history attrs flags (Campaign2.snapshot initial z).wg z)

theorem entry_history (attrs : DeviceAttrs) (initial : WGWorld) (z : Ambient) :
    StatePrefixEnsures (fun h g _=>History attrs (Campaign2.snapshot initial z).wg h ∧ g=initial)
      (History attrs (Campaign2.snapshot initial z).wg)
      (record attrs (.updateEntry (attrs.flags.getD 0)))
      (fun _ h g _=>History attrs (Campaign2.snapshot initial z).wg h ∧ g=generationWorld initial) := by
  intro g a h pre
  rcases pre with ⟨prior,same⟩
  subst g
  let r:=receipt (.updateEntry (attrs.flags.getD 0)) ⟨0,initial,generationWorld initial,a,a⟩
  have hist : History attrs (Campaign2.snapshot initial z).wg (h++[r]) := by
    apply prior.append
    intro other member kind
    have same:=List.mem_singleton.mp member
    subst other
    cases kind
  exact ⟨[r],rfl,hist,hist,rfl⟩

theorem observe_history (attrs : DeviceAttrs) (initial : WGWorld) (z : Ambient) :
    StatePrefixEnsures (fun h g _=>History attrs (Campaign2.snapshot initial z).wg h ∧ g=initial)
      (History attrs (Campaign2.snapshot initial z).wg) (observe attrs)
      (fun _ h _ _=>History attrs (Campaign2.snapshot initial z).wg h) := by
  apply observe_entry_rule attrs
  · intro ret
    exact StatePrefixEnsures.pure ret (fun _ _ _ pre=>pre.1) (fun _ _ _ pre=>pre.1)
  · exact fun site value=>history_mark attrs _ _ site value
  · exact history_frame attrs _ _ _ (lookupInterface_sameWGWorld _)
  · exact history_frame attrs _ _ _ Internal.getDev_frame
  · exact history_frame attrs _ _ _ (Internal.ambient_frame _)
  · exact fun left right x y=>history_frame attrs _ _ _ (Internal.branch_or_frame left right x y)
  · exact StatePrefixEnsures.bind (entry_history attrs initial z)
      (fun _=>update_history attrs _ initial z)

theorem inspection_history (attrs : DeviceAttrs) (g : WGWorld) (a : Ambient) :
    History attrs (Campaign2.snapshot g a).wg (inspection attrs g a).receipts := by
  obtain ⟨_,_,safe,_⟩:=observe_history attrs g a g a [] ⟨by simp [History],rfl⟩
  exact safe

theorem no_net_history (attrs : DeviceAttrs) (port : Nat)
    (selected : attrs.listenPort=some port) (next : UInt32→WGPrefix Receipt Int)
    (d : Device) (net : d.creatingNet=false) (g : WGWorld) (a : Ambient)
    (device : g.dev=some d) (h : List Receipt) :
    (runWGPrefix (setDeviceWith (fun {_} x=>liftWGPrefix x) next attrs) g a h).2=h := by
  unfold setDeviceWith
  change (runStatePrefix (liftWGPrefix (lookupInterface attrs.device) >>= _) g a h).2=h
  rw [runStatePrefix_bind]
  simp only [liftWGPrefix,runStatePrefix_lift]
  cases first : ((lookupInterface attrs.device).run g).run a with
  | error stop => rfl
  | ok out =>
    rcases out with ⟨⟨look,v⟩,b⟩
    have same : v=g := (ProjectedAction.iff_run_ambient _ _ _).mp
      (lookupInterface_sameWGWorld attrs.device) g a look v b first
    subst v
    cases look <;> cases flag : attrs.flags
    all_goals
      repeat' first
        | (simp [runStatePrefix_bind,runStatePrefix_lift,runStatePrefix_pure,
            -bind_pure_comp,branch,AmbientM.branch,WG.orM,selected,getDev,device,net])
        | split

end Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
