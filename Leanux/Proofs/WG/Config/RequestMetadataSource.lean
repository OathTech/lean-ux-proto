import Leanux.Proofs.WG.Config.RequestMetadataFrames

/-! Metadata transport through the unchanged request observer and source factories. The key stage establishes the tracked value; actual peer commands retain it. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Leanux.Proofs.WG.Configuration

theorem metadata_pure {α : Type} (value : α) :
    StatePrefixPreserves (fun h w _=>MetadataAll h (getterMetadata w))
      MetadataConsistent (pure value : WGPrefix Receipt α) :=
  StatePrefixEnsures.pure value (fun _ w _ point=>⟨getterMetadata w,point⟩)
    (fun _ _ _ point=>point)

theorem metadata_peer (attrs : DeviceAttrs) (p : PeerAttrs) :
    StatePrefixPreserves (fun h w _=>MetadataAll h (getterMetadata w))
      MetadataConsistent (record attrs (.peer p)) := by
  intro w ambient h prior
  have source := runWGPrefix_receiptWGObserved
    (liftWGPrefix (action attrs (.peer p))) (receipt (.peer p)) w ambient h
  rw [runWGPrefix_lift] at source
  simp only [runWGPrefix,runStatePrefix] at source
  unfold record
  rw [source]
  cases run : ((action attrs (.peer p)).run w).run ambient with
  | error stop => exact ⟨[],by simp,⟨getterMetadata w,prior⟩,trivial⟩
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (GetterPeerCommand.command p) w ambient ret v after run
    change getterMetadata v=getterMetadata w at same
    let r := receipt (.peer p) ⟨ret,w,v,ambient,after⟩
    have next : MetadataAll (h++[r]) (getterMetadata v) := by
      apply MetadataAll.append
      · simpa only [same] using prior
      · intro q member value selected
        have eq : q=r := List.mem_singleton.mp member
        subst q
        change value ∈ [getterMetadata w,getterMetadata v] at selected
        simp only [List.mem_cons,List.not_mem_nil,or_false] at selected
        rcases selected with rfl|rfl
        · exact same.symm
        · rfl
    exact ⟨[r],rfl,⟨getterMetadata v,next⟩,next⟩

theorem metadata_forIn {α β : Type} (xs : List α) (init : β)
    (body : α→β→WGPrefix Receipt (ForInStep β))
    (step : ∀ x state,StatePrefixPreserves
      (fun h w _=>MetadataAll h (getterMetadata w)) MetadataConsistent (body x state)) :
    StatePrefixPreserves (fun h w _=>MetadataAll h (getterMetadata w))
      MetadataConsistent (forIn xs init body) :=
  StatePrefixEnsures.forInInvariant xs init body
    (fun _ h w _=>MetadataAll h (getterMetadata w)) MetadataConsistent
    (fun _ _ w _ point=>⟨getterMetadata w,point⟩) step

theorem peers_metadata (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h w _=>MetadataAll h (getterMetadata w))
      MetadataConsistent (peers attrs) := by
  unfold peers devicePeersWith
  dsimp only
  repeat' first
    | with_reducible exact metadata_peer attrs _
    | with_reducible exact metadata_branch _ _
    | with_reducible exact metadata_pure _
    | (maintenance_head ForIn.forIn; apply metadata_forIn)
    | with_reducible apply StatePrefixEnsures.bind
    | (maintenance_intro; try dsimp only)
    | split

theorem key_metadata (attrs : DeviceAttrs) :
    StatePrefixEnsures (fun h _ _=>NoMetadata h) MetadataConsistent
      (record attrs .keyStage)
      (fun _ h w _=>MetadataAll h (getterMetadata w)) := by
  intro w ambient h prior
  have source := runWGPrefix_receiptWGObserved
    (liftWGPrefix (action attrs .keyStage)) (receipt .keyStage) w ambient h
  rw [runWGPrefix_lift] at source
  simp only [runWGPrefix,runStatePrefix] at source
  unfold record
  rw [source]
  cases run : ((action attrs .keyStage).run w).run ambient with
  | error stop => exact ⟨[],by simp,prior.consistent,trivial⟩
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    let r := receipt .keyStage ⟨ret,w,v,ambient,after⟩
    have next : MetadataAll (h++[r]) (getterMetadata v) := by
      apply MetadataAll.append (prior.all _)
      intro q member value selected
      have eq : q=r := List.mem_singleton.mp member
      subst q
      change value ∈ [getterMetadata v] at selected
      exact List.mem_singleton.mp selected
    exact ⟨[r],rfl,⟨getterMetadata v,next⟩,next⟩

theorem keyed_metadata (attrs : DeviceAttrs) :
    StatePrefixEnsures (fun h _ _=>NoMetadata h) MetadataConsistent
      (keyed attrs) (fun _ h w _=>MetadataAll h (getterMetadata w)) :=
  StatePrefixEnsures.bind (key_metadata attrs) (fun _=>peers_metadata attrs)


theorem nometa_pure {α : Type} (value : α) :
    StatePrefixPreserves (fun h _ _=>NoMetadata h) MetadataConsistent
      (pure value : WGPrefix Receipt α) :=
  StatePrefixEnsures.pure value (fun _ _ _ point=>point.consistent) (fun _ _ _ point=>point)

theorem nometa_lift {α : Type} (action : WG.M α) :
    StatePrefixPreserves (fun h _ _=>NoMetadata h) MetadataConsistent (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ point=>point.consistent)
    (fun _ _ _ _ _ _ point _=>point)

theorem nometa_mark (site : Decision) (value : Bool) :
    StatePrefixPreserves (fun h _ _=>NoMetadata h) MetadataConsistent (mark site value) :=
by
  change StatePrefixPreserves _ _ (liftWGPrefix _)
  exact nometa_lift _

theorem pure_metadata {α : Type} (value : α) :
    StatePrefixEnsures (fun h _ _=>NoMetadata h) MetadataConsistent
      (pure value : WGPrefix Receipt α) (fun _ h w _=>MetadataAll h (getterMetadata w)) :=
  StatePrefixEnsures.pure value (fun _ _ _ point=>point.consistent)
    (fun _ w _ point=>point.all (getterMetadata w))

theorem nometa_record (attrs : DeviceAttrs) (kind : Kind)
    (silent : ∀ native : WGRunWitness Int,metadataValues (receipt kind native)=[]) :
    StatePrefixPreserves (fun h _ _=>NoMetadata h) MetadataConsistent (record attrs kind) := by
  intro w ambient h prior
  have source := runWGPrefix_receiptWGObserved
    (liftWGPrefix (action attrs kind)) (receipt kind) w ambient h
  rw [runWGPrefix_lift] at source
  simp only [runWGPrefix,runStatePrefix] at source
  unfold record
  rw [source]
  cases run : ((action attrs kind).run w).run ambient with
  | error stop => exact ⟨[],by simp,prior.consistent,trivial⟩
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    let r := receipt kind ⟨ret,w,v,ambient,after⟩
    have next : NoMetadata (h++[r]) := by
      intro q member
      rcases List.mem_append.mp member with old|new
      · exact prior q old
      · have eq : q=r := List.mem_singleton.mp new
        subst q
        exact silent _
    exact ⟨[r],rfl,next.consistent,next⟩

theorem fwmark_nometa (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>NoMetadata h) MetadataConsistent
      (fwmarkObserved attrs) := by
  intro w ambient h prior
  obtain ⟨added,eq,path,_⟩ := fwmarkObserved_conforms attrs w ambient h
  have all : NoMetadata (runWGPrefix (fwmarkObserved attrs) w ambient h).2 := by
    rw [eq]
    intro r member
    rcases List.mem_append.mp member with old|new
    · exact prior r old
    · obtain ⟨pid,kind⟩ := path.1 r new
      simp only [metadataValues,kind]
  refine ⟨added,eq,all.consistent,?_⟩
  simp only [runWGPrefix,runStatePrefix] at all ⊢
  cases run : (runPrefix ((fwmarkObserved attrs).run w) ambient h).1 with
  | error stop => trivial
  | ok out => rcases out with ⟨⟨ret,v⟩,after⟩; exact all

theorem afterPort_metadata (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (fun h _ _=>NoMetadata h) MetadataConsistent
      (afterPort attrs flags) (fun _ h w _=>MetadataAll h (getterMetadata w)) := by
  unfold afterPort
  apply StatePrefixEnsures.bind (nometa_mark _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (nometa_record attrs .replacement (fun _=>rfl))
    intro _
    exact keyed_metadata attrs
  · exact keyed_metadata attrs

theorem afterFwmark_metadata (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (fun h _ _=>NoMetadata h) MetadataConsistent
      (afterFwmark attrs flags) (fun _ h w _=>MetadataAll h (getterMetadata w)) := by
  unfold afterFwmark
  apply StatePrefixEnsures.bind (nometa_mark _ _)
  intro _
  split
  · apply StatePrefixEnsures.bind (nometa_record attrs (.port _) (fun _=>rfl))
    intro ret
    apply StatePrefixEnsures.bind (nometa_mark _ _)
    intro _
    split
    · unfold zero
      exact StatePrefixEnsures.bind (nometa_mark _ _) (fun _=>pure_metadata ret)
    · exact afterPort_metadata attrs flags
  · exact afterPort_metadata attrs flags

theorem update_metadata (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixEnsures (fun h _ _=>NoMetadata h) MetadataConsistent
      (update attrs flags) (fun _ h w _=>MetadataAll h (getterMetadata w)) := by
  rw [update_fwmark_factor]
  exact StatePrefixEnsures.bind (fwmark_nometa attrs) (fun _=>afterFwmark_metadata attrs flags)

theorem observe_metadata (attrs : DeviceAttrs) :
    StatePrefixEnsures (fun h _ _=>NoMetadata h) MetadataConsistent
      (observe attrs) (fun _ h w _=>MetadataAll h (getterMetadata w)) := by
  apply observe_entry_rule attrs
  · exact fun ret=>pure_metadata ret
  · exact fun site value=>nometa_mark site value
  · exact nometa_lift _
  · exact nometa_lift _
  · exact nometa_lift _
  · exact fun _ _ _ _=>nometa_lift _
  · exact StatePrefixEnsures.bind
      (nometa_record attrs (.updateEntry _) (fun _=>rfl)) (fun _=>update_metadata attrs _)

theorem inspection_metadata (attrs : DeviceAttrs) (w : WGWorld) (ambient : Ambient) :
    MetadataFacts (inspection attrs w ambient) := by
  obtain ⟨_,_,safe,post⟩ := observe_metadata attrs w ambient []
    (by simp [NoMetadata])
  refine ⟨safe,?_⟩
  unfold inspection
  simp only [runWGPrefix,runStatePrefix] at post ⊢
  cases run : (runPrefix ((observe attrs).run w) ambient []).1 with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    simpa only [run,Campaign2.observeResult,Except.map,←getterMetadata_observation] using post

end Leanux.Proofs.WG.Config.RequestOrder
