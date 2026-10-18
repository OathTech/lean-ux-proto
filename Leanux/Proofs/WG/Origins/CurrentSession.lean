import Leanux.Proofs.WG.Origins.CurrentIdentity

/-! The actual session front installs current configured identity in the same
receipt that supports its receiving material. Configuration is justified by a
normal whole-session tail; no such endpoint is assigned to a stopped tail. -/
namespace Leanux.Proofs.WG.CurrentSession
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.MaterialOrigin Leanux.Proofs.WG.CurrentIdentity Lifetimes

private theorem configured_peers {before after : Device}
    (he : ConfiguredIdentity.state after = ConfiguredIdentity.state before) (pid : PeerId) :
    (after.peers[pid]?).map CurrentIdentity.identity = (before.peers[pid]?).map CurrentIdentity.identity := by
  have cells := congrFun (congrArg ConfiguredIdentity.State.peers he) pid
  have fields := congrArg (Option.map (fun c : ConfiguredIdentity.Cell => (c.stamp, c.static))) cells
  change (after.peers[pid]?).map (fun p => (p.internalId, p.remoteStatic)) =
    (before.peers[pid]?).map (fun p => (p.internalId, p.remoteStatic))
  simpa only [ConfiguredIdentity.state, Option.map_map, Function.comp_def,
    ConfiguredIdentity.cell] using fields

private theorem support_peers (hi : Supported history epoch slot key before)
    (hp : ∀ pid, (after pid).map CurrentIdentity.identity = (before pid).map CurrentIdentity.identity) :
    Supported history epoch slot key after := by
  obtain ⟨pid, run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, word, current⟩ := hi
  refine ⟨pid, run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, word, ?_⟩
  intro owner peer kw stored
  have old : (before owner).map CurrentIdentity.identity = some (CurrentIdentity.identity peer) := by
    rw [← hp owner, stored]
    rfl
  obtain ⟨previous, resident, same⟩ := Option.map_eq_some_iff.mp old
  exact same.symm.trans (current owner previous kw resident)

/-- The conditional configured premise is discharged from the actual normal
tail below. This lemma alone never declares every completed front configured. -/
theorem front_installs (pid : PeerId) (w u : WGWorld) (result : Option SessionOrigin.Context)
    (ambient middle : Ambient) (history : List SessionOrigin.Receipt) (hi : Inv history w)
    (hr : ((SessionOrigin.front pid).run w).run ambient = .ok ((result,u),middle))
    (configured : ∀ ctx, result = some ctx → ConfiguredSession.Configured pid w ctx) :
    Inv (history ++ [SessionOrigin.Receipt.material pid ⟨result,w,u,ambient,middle⟩]) u := by
  cases result with
  | none =>
    have eq := Origins.front_none pid w u ambient middle hr
    subst u
    exact hi.mono (fun r hm => List.mem_append_left _ hm)
  | some ctx =>
    obtain ⟨d, key, hd, hp, _state, _word, _slot, hview, _stamp, hword, hvalid⟩ :=
      Origins.front_effect pid ctx w u ambient middle hr
    have configuredView := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ConfiguredSession.front_view pid) w ambient (some ctx) u middle hr
    intro dev hdev id k hk valid
    have fields : (dev.ifindex, fun q => dev.keypairs[q]?) =
        (d.ifindex, fun q => if ctx.slot = q then some key else d.keypairs[q]?) := by
      simpa [Origins.view, hdev] using hview
    have epoch : dev.ifindex = d.ifindex := congrArg Prod.fst fields
    have keys := congrFun (congrArg Prod.snd fields) id
    dsimp only at keys
    have cells : ConfiguredIdentity.state dev = ConfiguredIdentity.state d :=
      Option.some.inj (by simpa [ConfiguredIdentity.view, hdev, hd] using configuredView)
    have peers := configured_peers cells
    by_cases atSlot : ctx.slot = id
    · subst id
      have equal : k = key := by rw [hk] at keys; simpa using keys
      subst k
      have cfg := configured ctx rfl
      refine ⟨pid, ⟨some ctx,w,u,ambient,middle⟩, ctx, dev, key, by simp,
        hr, rfl, rfl, cfg, hdev, rfl, hk, hvalid, hword, rfl, Or.inr hword, ?_⟩
      intro owner peer kw resident
      have self : ctx.word = some pid := cfg.choose_spec.2.2.2.2
      have ownerEq : owner = pid := Option.some.inj (kw.symm.trans (hword.trans self))
      subst owner
      have same : (dev.peers[pid]?).map CurrentIdentity.identity =
          some (CurrentIdentity.identity ctx.peer) := (peers pid).trans (by rw [hp]; rfl)
      exact Option.some.inj (by simpa only [resident, Option.map_some] using same)
    · have old : d.keypairs[id]? = some k := by simpa [atSlot, hk] using keys.symm
      have retained := support_peers (hi d hd id k old valid) peers
      have retainedAt : Supported history dev.ifindex id k (fun pid => dev.peers[pid]?) := by
        simpa only [epoch] using retained
      exact retainedAt.mono (fun r hm => List.mem_append_left _ hm)

/-- The real tail changes slots, counters and owner/index state while retaining
both receiving origin and the exact configured peer identity fields. -/
theorem tail_retains (pid kp : Nat) (ambient ambient' : Ambient)
    (hr : ((SessionOrigin.tail pid kp).run w).run ambient = .ok ((result,v),ambient')) :
    Retains w v :=
  retains_of_configured_view (Origins.tail_retains pid kp ambient ambient' hr)
    ((ProjectedAction.iff_run_ambient _ _ _).mp
      (ConfiguredSession.tail_view pid kp) w ambient result v ambient' hr)

/-- Every normal original session, including false, exposes its actual front
cut and supports current identity at the returned endpoint. No affiliation,
fresh-slot or non-NULL premise is assumed at entry. -/
theorem beginSession_support (pid : PeerId) (w v : WGWorld) (result : Bool)
    (ambient ambient' : Ambient) (history : List SessionOrigin.Receipt)
    (configured : ConfiguredIdentity.Inv w) (hi : Inv history w)
    (hr : ((beginSession pid).run w).run ambient = .ok ((result,v),ambient')) :
    ∃ front u middle, ((SessionOrigin.front pid).run w).run ambient = .ok ((front,u),middle) ∧
      Inv (history ++ [SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩]) v := by
  rw [SessionOrigin.factor, bind_ok_ambient] at hr
  obtain ⟨front,u,middle,hf,ht⟩ := hr
  refine ⟨front,u,middle,hf,?_⟩
  cases front with
  | none =>
    simp only [StateT.run_pure, CounterWindow.except_pure, Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := ht
    exact front_installs pid w u none ambient middle history hi hf (by simp)
  | some ctx =>
    exact (front_installs pid w u (some ctx) ambient middle history hi hf (by
      intro c hc; cases hc
      exact ConfiguredSession.front_configured pid ctx w u v ambient middle ambient'
        result configured hf ht)).retain (tail_retains pid ctx.slot middle ambient' ht)

/-- Appending is unconditional, including arbitrary incoming receipt histories
and failed fronts; no global validity premise is needed just to retain a prefix. -/
theorem observedFront_appends (pid : PeerId) : StateAppends (SessionOrigin.observedFront pid) := by
  unfold SessionOrigin.observedFront SessionOrigin.frontWith
  simp only [SessionOrigin.allocate]
  repeat' first
    | with_reducible exact StateAppends.focus _ _ _
    | with_reducible exact StateAppends.lift _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.receiptWGObserved
    | with_reducible apply StateAppends.bind
    | (session_origin_intro_forall; try dsimp only)
    | split
  all_goals first | exact StateAppends.focus _ _ _ | exact StateAppends.lift _

/-- Normal support for the unchanged once-only observer. Every prior receipt
is retained, but arbitrary unrelated incoming receipts need not be certified.
No endpoint claim is made after a Stop. -/
theorem observed_support (pid : PeerId) (w v : WGWorld) (result : Bool)
    (ambient ambient' : Ambient) (h t : List (MaterialOrigin.Event SessionOrigin.Receipt))
    (configured : ConfiguredIdentity.Inv w) (hi : Inv (h.filterMap Origins.receipt?) w)
    (hr : runWGPrefix (SessionOrigin.observed pid) w ambient h = (.ok ((result,v),ambient'),t)) :
    Inv (t.filterMap Origins.receipt?) v := by
  obtain ⟨suffix,hs⟩ := observedFront_appends pid w ambient h
  change (runStatePrefix (SessionOrigin.observedFront pid) w ambient h).2 = h ++ suffix at hs
  change runStatePrefix (SessionOrigin.observed pid) w ambient h = _ at hr
  unfold SessionOrigin.observed at hr
  rw [runStatePrefix_bind] at hr
  have hc := runWGPrefix_receiptWGObserved (SessionOrigin.observedFront pid)
    (MaterialOrigin.Event.receipt ∘ SessionOrigin.Receipt.material pid) w ambient h
  simp only [runWGPrefix] at hc
  rw [hc] at hr
  cases hf : runStatePrefix (SessionOrigin.observedFront pid) w ambient h with
  | mk output middleHistory =>
    simp only [hf] at hs
    cases output with
    | error e => simp [hf] at hr
    | ok output =>
      rcases output with ⟨⟨front,u⟩,middle⟩
      simp only [hf,Function.comp_apply] at hr
      have source : ((SessionOrigin.front pid).run w).run ambient = .ok ((front,u),middle) :=
        (SessionOrigin.observedFront_erases pid w ambient h).symm.trans (congrArg Prod.fst hf)
      have incl : ∀ r ∈ (h.filterMap Origins.receipt? ++
          [SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩]),
          r ∈ (middleHistory ++ [MaterialOrigin.Event.receipt
            (SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩)]).filterMap Origins.receipt? := by
        intro r hm
        rw [hs]
        simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,Origins.receipt?,List.append_assoc]
          using (show r ∈ h.filterMap Origins.receipt? ++ suffix.filterMap Origins.receipt? ++
            [SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩] from by
              rcases List.mem_append.mp hm with hm | hm
              · exact List.mem_append_left _ (List.mem_append_left _ hm)
              · exact List.mem_append_right _ hm)
      cases front with
      | none =>
        simp only [runStatePrefix_pure,Prod.mk.injEq,Except.ok.injEq] at hr
        obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩ := hr
        exact (front_installs pid w u none ambient middle _ hi source (by simp)).mono incl
      | some ctx =>
        change runWGPrefix (Origins.accessNative (SessionOrigin.tailPrefix pid ctx.slot)) u middle
          (middleHistory ++ [MaterialOrigin.Event.receipt
            (SessionOrigin.Receipt.material pid ⟨some ctx,w,u,ambient,middle⟩)]) =
              (.ok ((result,v),ambient'),t) at hr
        have tail : ((SessionOrigin.tail pid ctx.slot).run u).run middle = .ok ((result,v),ambient') :=
          (focusStatePrefix_erases _ _ (SessionOrigin.tail_erases pid ctx.slot) u middle _).symm.trans
            (congrArg Prod.fst hr)
        have frame := Origins.access_receipts (R := SessionOrigin.Receipt)
          ((SessionOrigin.tailPrefix pid ctx.slot).run u) middle
          (middleHistory ++ [MaterialOrigin.Event.receipt
            (SessionOrigin.Receipt.material pid ⟨some ctx,w,u,ambient,middle⟩)])
        change (runWGPrefix (Origins.accessNative (SessionOrigin.tailPrefix pid ctx.slot)) u middle
          (middleHistory ++ [MaterialOrigin.Event.receipt
            (SessionOrigin.Receipt.material pid ⟨some ctx,w,u,ambient,middle⟩)])).2.filterMap Origins.receipt? =
              (middleHistory ++ [MaterialOrigin.Event.receipt
                (SessionOrigin.Receipt.material pid ⟨some ctx,w,u,ambient,middle⟩)]).filterMap Origins.receipt? at frame
        rw [hr] at frame
        rw [frame]
        exact ((front_installs pid w u (some ctx) ambient middle _ hi source (by
          intro c hc; cases hc
          exact ConfiguredSession.front_configured pid ctx w u v ambient middle ambient' result configured source tail)).retain
            (tail_retains pid ctx.slot middle ambient' tail)).mono incl

end Leanux.Proofs.WG.CurrentSession
