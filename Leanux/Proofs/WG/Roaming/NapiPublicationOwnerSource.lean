import Leanux.Proofs.WG.Roaming.NapiPublicationSelectionSource
import Leanux.Proofs.WG.Roaming.PublicationClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Env Noise

theorem enqueuePublication_scheduled (id : SkbId) (state : PacketState) :
    Campaign2.Product.Ensures (enqueuePublication id state) (fun _ => True)
      (fun result _ => OwnerScheduled result.2 result.1) := by
  let R : (PeerId × Campaign2.Product.Snapshot) → World → Prop := fun result _ =>
    ∀ d, result.2.wg.device = some d → ∃ p, d.peers[result.1]? = some p ∧ p.napiScheduled = true
  have seq {α : Type} (action : Leanux.M α) (next : α → Leanux.M (PeerId × Campaign2.Product.Snapshot))
      (h : ∀ x, Noise.Product.Ensures (next x) (fun _ => True) R) :
      Noise.Product.Ensures (action >>= next) (fun _ => True) R :=
    Noise.Product.ensures_bind _ _ (by intro _ _ _ _ _; trivial) h
  have conditional : Noise.Product.Ensures (enqueuePublication id state) (fun _ => True) R := by
    unfold enqueuePublication
    refine seq _ _ ?_
    intro pkt
    refine seq _ _ ?_
    intro pid
    refine seq _ _ ?_
    intro ignored
    refine seq _ _ ?_
    intro p
    split
    · intro w result final _ run; cases run
    refine seq _ _ ?_
    intro ignored
    intro w result final _ run
    let next := {w with wg := {w.wg with dev := w.wg.dev.map fun (d : Device) =>
      {d with peers := d.peers.insert pid {p with napiScheduled := true}}}}
    change Except.ok ((pid,Campaign2.Product.snapshot next),next) = Except.ok (result,final) at run
    dsimp only [R]
    have sameResult : (pid,Campaign2.Product.snapshot next) = result := congrArg Prod.fst (Except.ok.inj run)
    rw [← sameResult]
    intro d found
    cases hd : w.wg.dev with
    | none => simp [next,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core,hd] at found
    | some original =>
      simp only [next,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core,hd,Option.map_some] at found
      cases found
      exact ⟨{p with napiScheduled := true},by simp,rfl⟩
  intro w result final pre run
  obtain ⟨_,pkt,_,stored⟩ := enqueuePublication_packet id state (fun _ => True)
    w result final (by intro _ _; trivial) run
  cases hd : result.2.wg.device with
  | none => simp [packetAt,hd] at stored
  | some d =>
    obtain ⟨p,resident,scheduled⟩ := conditional w result final pre run d hd
    exact ⟨d,p,hd,resident,scheduled⟩

theorem publicationPrefix_scheduled (softirq : Leanux.M Unit) :
    Campaign2.Product.Ensures (publicationPrefix softirq) (fun _ => True)
      (fun result _ => ∀ pub, result = some pub → OwnerScheduled pub.publication pub.owner) := by
  have any {α : Type} (action : Leanux.M α) :
      Noise.Product.Ensures action (fun _ => True) (fun _ _ => True) := by
    intro _ _ _ _ _; trivial
  have publish (id : SkbId) (decrypted : Option RxPacket) :
      Campaign2.Product.Ensures (publicationPublish id decrypted) (fun _ => True)
        (fun result _ => OwnerScheduled result.2 result.1) := by
    cases decrypted with
    | none =>
      intro w result final pre run
      let next := {w with ambient := {w.ambient with steps := w.ambient.steps.push {
        decision := .decWorkerDecrypted,outcome := false,netRx := w.ambient.netRxSection}}}
      exact enqueuePublication_scheduled id .dead next result final pre run
    | some plain =>
      have chain : Noise.Product.Ensures (do
          liftWG (setRxSkb id (fun _ => plain)); enqueuePublication id .crypted)
          (fun _ => True) (fun result _ => OwnerScheduled result.2 result.1) := by
        refine Noise.Product.ensures_bind _ _ (any _) ?_
        intro ignored
        exact enqueuePublication_scheduled id .crypted
      intro w result final pre run
      let next := {w with ambient := {w.ambient with steps := w.ambient.steps.push {
        decision := .decWorkerDecrypted,outcome := true,netRx := w.ambient.netRxSection}}}
      exact chain next result final pre run
  have packet (after : Campaign2.Product.Snapshot) (id : SkbId) :
      Campaign2.Product.Ensures (publicationPacket after id) (fun _ => True)
        (fun pub _ => OwnerScheduled pub.publication pub.owner) := by
    unfold publicationPacket
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro input
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro before
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro decrypted
    refine Noise.Product.ensures_bind _ _ (publish id decrypted) ?_
    intro published w pub final pre run
    cases run
    exact pre
  have selected (after : Campaign2.Product.Snapshot) (id : SkbId) (ring : PtrRing SkbId) :
      Campaign2.Product.Ensures (publicationSelected after id ring) (fun _ => True)
        (fun pub _ => OwnerScheduled pub.publication pub.owner) := by
    unfold publicationSelected
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro ignored
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro ignored
    exact packet after id
  unfold publicationPrefix
  refine Noise.Product.ensures_bind _ _ (any _) ?_
  intro ignored
  refine Noise.Product.ensures_bind _ _ (any _) ?_
  intro after
  refine Noise.Product.ensures_bind _ _ (any _) ?_
  intro d
  cases hc : d.decryptQueue.consume with
  | mk first ring =>
    cases first with
    | none =>
      refine Noise.Product.ensures_bind _ _ (any _) ?_
      intro ignored w result final pre run pub same
      cases run
      cases same
    | some id =>
      refine Noise.Product.ensures_bind _ _ (selected after id ring) ?_
      intro cut w result final pre run pub same
      cases run
      cases same
      exact pre

/-- Actual NAPI admission selects the already scheduled owner; the multiple-
peer branch remains an error and no successful-callback premise is imposed. -/
theorem napiPublicationFront_owner (owner : PeerId) :
    Campaign2.Product.Ensures napiPublicationFront (fun s => OwnerScheduled s owner)
      (fun result _ => ∀ peers, result = some peers → peers = [owner]) := by
  have any {α : Type} (action : Leanux.M α) :
      Noise.Product.Ensures action (fun _ => True) (fun _ _ => True) := by
    intro _ _ _ _ _; trivial
  have dev : Noise.Product.Ensures (liftWG getDev)
      (fun w => OwnerScheduled (Campaign2.Product.snapshot w) owner)
      (fun d _ => ∃ p, d.peers[owner]? = some p ∧ p.napiScheduled = true) := by
    intro w result final pre run
    obtain ⟨d,p,hd,hp,scheduled⟩ := pre
    change w.wg.dev = some d at hd
    have read : (liftWG getDev).run w = .ok (d,w) := by
      dsimp only [liftWG,getDev,StateT.run,StateT.bind,get,getThe,MonadStateOf.get,
        StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure]
      rw [hd]; rfl
    rw [read] at run
    cases run
    exact ⟨p,hp,scheduled⟩
  unfold napiPublicationFront
  refine Noise.Product.ensures_bind _ _ dev ?_
  intro d w result final pre run
  obtain ⟨p,resident,scheduled⟩ := pre
  let pending := d.peers.toList.filterMap fun (pid,p) => if p.napiScheduled then some pid else none
  have member : owner ∈ pending := by
    apply List.mem_filterMap.mpr
    exact ⟨(owner,p),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr resident,by simp [scheduled]⟩
  have singleton (bound : ¬ pending.length > 1) : pending = [owner] := by
    cases hp : pending with
    | nil => simp [hp] at member
    | cons first rest =>
      cases hr : rest with
      | nil =>
        have eq : owner = first := by simpa [hp,hr] using member
        exact congrArg List.singleton eq.symm
      | cons second rest =>
        simp only [hp,hr,List.length_cons] at bound
        omega
  let tail : Leanux.M (Option (List PeerId)) := do
    if pending.isEmpty then return none
    if (← getAmbient).hidden.isSome && (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return none
    if pending.length > 1 then unsupported "NAPI polls of several peers in one softirq"
    _ ← hidden (.sectionStart .netRx)
    modifyAmbient fun s => {s with netRxSection := s.netRxSections}
    return some pending
  have htail : Noise.Product.Ensures tail (fun _ => True)
      (fun result _ => ∀ peers, result = some peers → peers = [owner]) := by
    unfold tail
    split
    · intro _ _ _ _ hr peers eq; cases hr; cases eq
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro ambient
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro site
    split
    · intro _ _ _ _ hr peers eq; cases hr; cases eq
    split
    · intro _ _ _ _ hr; cases hr
    · rename_i bound
      refine Noise.Product.ensures_bind _ _ (any _) ?_
      intro ignored
      refine Noise.Product.ensures_bind _ _ (any _) ?_
      intro ignored entry result final _ hr peers eq
      cases hr
      cases eq
      exact singleton bound
  exact htail w result final trivial run

theorem napiIrqPublicationFront_owner (owner : PeerId) :
    Campaign2.Product.Ensures napiIrqPublicationFront (fun s => OwnerScheduled s owner)
      (fun result _ => ∀ peers, result = some peers → peers = [owner]) := by
  let P : World → Prop := fun w => OwnerScheduled (Campaign2.Product.snapshot w) owner
  have ambient {α : Type} (action : AmbientM α) :
      Noise.Product.Ensures (monadLift action : Leanux.M α) P (fun _ => P) := by
    intro w result final pre run
    change (action.run w.ambient >>= fun (x,a) => Except.ok (x,{w with ambient := a})) = _ at run
    cases hr : action.run w.ambient with
    | error stop => rw [hr] at run; cases run
    | ok out => obtain ⟨x,a⟩ := out; rw [hr] at run; cases run; exact pre
  have dev : Noise.Product.Ensures (liftWG getDev) P (fun _ => P) := by
    intro w result final pre run
    have saved := pre
    obtain ⟨d,p,hd,hp,scheduled⟩ := pre
    change w.wg.dev = some d at hd
    have read : (liftWG getDev).run w = .ok (d,w) := by
      dsimp only [liftWG,getDev,StateT.run,StateT.bind,get,getThe,MonadStateOf.get,
        StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure]
      rw [hd]; rfl
    rw [read] at run
    cases run
    exact saved
  have env : Noise.Product.Ensures getEnv P (fun _ => P) := by
    intro w result final pre run; cases run; exact pre
  have changeEnv (f : EnvWorld → EnvWorld) : Noise.Product.Ensures (modifyEnv f) P (fun _ => P) := by
    intro w result final pre run; cases run; exact pre
  have skip : Noise.Product.Ensures (pure none : Leanux.M (Option (List PeerId))) P
      (fun result _ => ∀ peers, result = some peers → peers = [owner]) := by
    intro w result final pre run peers eq; cases run; cases eq
  unfold napiIrqPublicationFront
  refine Noise.Product.ensures_bind _ _ (ambient (get : AmbientM Ambient)) ?_
  intro a
  split
  · exact skip
  refine Noise.Product.ensures_bind _ _ dev ?_
  intro d
  split
  · exact skip
  refine Noise.Product.ensures_bind _ _ (ambient AmbientM.peekHiddenSite) ?_
  intro site
  split
  · exact skip
  refine Noise.Product.ensures_bind _ _ env ?_
  intro fixture
  refine Noise.Product.ensures_bind _ _ (changeEnv _) ?_
  intro ignored
  split
  · exact napiPublicationFront_owner owner
  · exact skip

theorem observedNapiIrqFirst_facts (owner : PeerId) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures observedNapiIrqFirst
      (fun s => s = entry ∧ OwnerScheduled entry owner)
      (fun result _ => NapiOwnerFacts entry owner result) := by
  intro w result final pre run cut same
  obtain ⟨rfl,owned⟩ := pre
  change ((napiIrqPublicationFront).run w >>= fun (pending,middle) =>
    (observedNapiFirst pending).run middle) = _ at run
  cases hr : napiIrqPublicationFront.run w with
  | error stop => rw [hr] at run; cases run
  | ok out =>
    obtain ⟨pending,middle⟩ := out
    have preserved := napiIrqPublicationFront_preserves w.wg w pending middle rfl hr
    have selection := napiIrqPublicationFront_owner owner w pending middle owned hr
    rw [hr] at run
    obtain ⟨entryEq,selected,facts⟩ := observedNapiFirst_facts pending (Campaign2.Product.snapshot middle)
      middle result final rfl run cut same
    have pidEq : cut.pid = owner := by
      cases hp : pending with
      | none => simp [hp] at selected
      | some peers =>
        have single := selection peers hp
        simpa [hp,single] using selected.symm
    have wgEq : (Campaign2.Product.snapshot middle).wg = (Campaign2.Product.snapshot w).wg := by
      change (Campaign2.snapshot middle.wg middle.ambient).wg = (Campaign2.snapshot w.wg w.ambient).wg
      rw [preserved]
      rfl
    have deviceEq : (Campaign2.Product.snapshot middle).wg.device = (Campaign2.Product.snapshot w).wg.device :=
      congrArg (fun s => s.device) wgEq
    refine ⟨pidEq,entryEq ▸ wgEq,?_⟩
    intro endpoint atEndpoint observed
    obtain ⟨endpointFacts,head⟩ := facts endpoint atEndpoint observed
    constructor
    · simpa only [PollEndpointFacts,packetAt,deviceEq,pidEq] using endpointFacts
    · simpa only [queueHead,deviceEq,pidEq] using head


end Leanux.Proofs.WG.Roaming
