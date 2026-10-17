import Leanux.Proofs.WG.Origins.HistoryAdapters
import Leanux.Proofs.WG.Origins.RetainingLifecycle
import Leanux.Proofs.WG.Lifetimes.BatchAudit

/-! Stateful material support on the existing committed RX journal. A decrypt
or saved probe is justified at its exact earlier prefix and captured state.
All input history/support is supplied; initialized execution is separate. -/
namespace Leanux.Proofs.WG.Origins.HistorySupport
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Retaining
abbrev Event := RxHistory.Event
abbrev Obs := RxHistory.Obs

def sessionEvent : Event → Option SessionOrigin.Receipt
  | .session r => some r | _ => none
def sessions (h : List Event) := h.filterMap sessionEvent
def StateSupported (h : List Event) (w : World) : Prop := Origins.Inv (sessions h) w.wg

/-- The prefix is positional, so two equal receipt values remain separate
occurrences. The decrypt entry retains its native WG and Ambient endpoints;
the saved probe retains its actual product World. -/
def Checked (pre : List Event) : Event → Prop
  | .rx (.decrypt _ r) => Origins.Inv (sessions pre) r.before
  | .audit (.probe p) => p.history = RxHistory.prior pre ∧ StateSupported pre p.world
  | _ => True

def Checks (h : List Event) : Prop :=
  ∀ pre e post, h = pre ++ e :: post → Checked pre e

def HistorySafe (h : List Event) : Prop := HistoryAdapters.Valid h ∧ Checks h
def SupportInv (h : List Event) (w : World) : Prop := HistorySafe h ∧ StateSupported h w
abbrev Preserves (a : Obs α) := PrefixPreserves SupportInv HistorySafe a

theorem safe (h : List Event) (w : World) (hi : SupportInv h w) : HistorySafe h := hi.1

private theorem positions_append {E : Type} (R : List E → E → Prop)
    (h s : List E) (hh : ∀ pre e post, h = pre ++ e :: post → R pre e)
    (hs : ∀ pre e post, s = pre ++ e :: post → R (h ++ pre) e) :
    ∀ pre e post, h ++ s = pre ++ e :: post → R pre e := by
  induction h generalizing R with
  | nil => simpa using hs
  | cons x xs ih =>
    intro pre e post he
    cases pre with
    | nil =>
      simp only [List.cons_append,List.nil_append,List.cons.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      exact hh [] x xs rfl
    | cons y ys =>
      simp only [List.cons_append,List.cons.injEq] at he
      obtain ⟨rfl,he⟩ := he
      exact ih (fun pre e => R (x::pre) e)
        (fun pre e post hx => hh (x::pre) e post (by simp only [List.cons_append,hx]))
        (fun pre e post hx => hs pre e post hx) ys e post he

theorem Checks.append (hh : Checks h)
    (hs : ∀ pre e post, s = pre ++ e :: post → Checked (h ++ pre) e) : Checks (h ++ s) :=
  positions_append Checked h s hh hs

theorem Checks.snoc (hh : Checks h) (he : Checked h e) : Checks (h ++ [e]) := by
  apply hh.append
  intro pre x post hx
  cases pre with
  | nil => simp only [List.nil_append,List.cons.injEq] at hx; obtain ⟨rfl,_⟩ := hx; simpa using he
  | cons y ys => cases ys <;> simp at hx

def sensitive : Event → Option Event
  | e@(.rx (.decrypt ..)) => some e
  | e@(.audit (.probe ..)) => some e
  | _ => none

theorem checked_quiet (he : sensitive e = none) : Checked pre e := by
  cases e <;> try trivial
  case rx r => cases r <;> first | trivial | cases he
  case audit a => cases a <;> first | trivial | cases he

theorem Checks.quiet (hh : Checks h) (hs : s.filterMap sensitive = []) : Checks (h ++ s) := by
  apply hh.append
  intro pre e post he
  apply checked_quiet
  have hm : e ∈ s := by rw [he]; simp
  cases hx : sensitive e with
  | none => rfl
  | some v => have : v ∈ s.filterMap sensitive := List.mem_filterMap.mpr ⟨e,hm,hx⟩; simp [hs] at this

theorem sessions_decoded (h : List Event) :
    Origins.sessions (h.filterMap HistoryAdapters.decode) = sessions h := by
  simp only [Origins.sessions,sessions,List.filterMap_filterMap]
  congr 1
  funext e
  cases e <;> try rfl
  case audit a => cases a <;> rfl

theorem SupportInv.kernel (hi : SupportInv h w)
    (hk : productStoreView v = productStoreView w) : SupportInv h v := by
  refine ⟨hi.1,?_⟩
  have hd : v.wg.dev = w.wg.dev := congrArg (fun k : ProductStore43 => k.2.2.2.dev) hk
  exact hi.2.retain (by unfold Retains; simp only [view,hd]; exact RetainsView.refl _)

theorem lift_retains (a : Leanux.M α) (ha : ProductRetainsCall a) : Preserves (liftPrefix a) :=
  (PrefixEnsures.lift a safe (fun _ _ _ _ hi hr => ⟨hi.1,ha.support hi.2 hr⟩)).preserves

theorem lift_kernel (a : Leanux.M α) (ha : SameProductStore a) : Preserves (liftPrefix a) :=
  lift_retains a (of_view (kernel ha))

/-- Quiet means the actual appended suffix contains neither an origin receipt
nor a probe. Erasure and a concrete full-material frame are separate premises. -/
theorem quiet (g : Obs α) (a : Leanux.M α) (he : ErasesPrefix g a) (ha : ProductRetainsCall a)
    (hs : ∀ w h, ∃ s, (runPrefix g w h).2 = h ++ s ∧
      s.filterMap HistoryAdapters.decode = [] ∧ s.filterMap sensitive = [] ∧
      s.filterMap sessionEvent = []) : Preserves g := by
  intro w h hi
  obtain ⟨s,hist,hd,hq,hse⟩ := hs w h
  have hv : HistorySafe (runPrefix g w h).2 := by
    rw [hist]
    refine ⟨?_,hi.1.2.quiet hq⟩
    simpa only [HistoryAdapters.Valid,List.filterMap_append,hd,List.append_nil] using hi.1.1
  refine ⟨s,hist,hv,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    refine ⟨hv,?_⟩
    have hx : sessions (runPrefix g w h).2 = sessions h := by simp only [sessions,hist,List.filterMap_append,hse,List.append_nil]
    change Origins.Inv (sessions (runPrefix g w h).2) out.2.wg
    rw [hx]
    exact ha.support hi.2 ((he w h).symm.trans hr)

/-- Lifetime access events may be added; they carry no origin obligation. -/
theorem mixed (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (he : ErasesPrefix g a) (ha : ProductRetainsCall a) :
    Preserves (RxHistory.mixed g) := by
  intro w h hi
  let s := ((runPrefix g w (RxHistory.prior h)).2.drop (RxHistory.prior h).length).map
    (fun e => RxHistory.Event.audit (.lifetime e))
  have run : runPrefix (RxHistory.mixed g) w h = ((runPrefix g w (RxHistory.prior h)).1,h ++ s) := by
    change ((runPrefix g w (RxHistory.prior h)).1,
      h ++ ((h.filterMap RxHistory.auditEvent ++
        ((runPrefix g w (RxHistory.prior h)).2.drop (RxHistory.prior h).length).map AuditEvent.lifetime).drop
          (h.filterMap RxHistory.auditEvent).length).map RxHistory.Event.audit) = _
    simp only [List.drop_left,List.map_map]
    rfl
  have valid : HistoryAdapters.Valid (h ++ s) := by
    intro e hm
    simp only [List.filterMap_append] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hi.1.1 e hm
    · obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp hm
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
      simp only [HistoryAdapters.decode,Option.some.injEq] at he
      subst e
      trivial
  have noSensitive : s.filterMap sensitive = [] := filterMap_disjoint _ _ (fun _ => rfl) _
  have noSession : sessions (h ++ s) = sessions h := by
    simp only [sessions,List.filterMap_append]
    rw [filterMap_disjoint _ _ (fun _ => rfl)]
    exact List.append_nil _
  have safeOut : HistorySafe (h ++ s) := ⟨valid,hi.1.2.quiet noSensitive⟩
  rw [run]
  refine ⟨s,rfl,safeOut,?_⟩
  cases hr : (runPrefix g w (RxHistory.prior h)).1 with
  | error e => trivial
  | ok out =>
    refine ⟨safeOut,?_⟩
    change Origins.Inv (sessions (h ++ s)) out.2.wg
    rw [noSession]
    exact ha.support hi.2 ((he w _).symm.trans hr)

/-- Composition of the existing focus adapters; the lower computation still
executes exactly once at its actual projected input history. -/
theorem focus_compose (enc : E → F) (dec : F → Option E)
    (enc' : F → Event) (dec' : Event → Option F) (a : PrefixM E α) (w : World) (h : List Event) :
    runPrefix (focusPrefix enc' dec' (focusPrefix enc dec a)) w h =
      runPrefix (focusPrefix (enc' ∘ enc) (fun e => (dec' e).bind dec) a) w h := by
  change ((runPrefix a w ((h.filterMap dec').filterMap dec)).1,
    h ++ ((h.filterMap dec' ++ ((runPrefix a w ((h.filterMap dec').filterMap dec)).2.drop
      ((h.filterMap dec').filterMap dec).length).map enc).drop (h.filterMap dec').length).map enc') = _
  simp only [List.drop_left,List.filterMap_filterMap,List.map_map]
  rfl

/-- Focusing a native journal commutes with its actual product adapter. The
native observer executes once, with the same input history and both states. -/
private theorem liftWGObserver_focus (enc : E → F) (dec : F → Option E)
    (g : WGPrefix E α) :
    liftWGObserver (focusStatePrefix enc dec g) = focusPrefix enc dec (liftWGObserver g) := rfl

theorem preserve_facts (g : Obs α) (ha : Appends g)
    (hv : PrefixPreserves (fun h _ => HistoryAdapters.Valid h) HistoryAdapters.Valid g)
    (hc : ∀ w h, SupportInv h w → Checks (runPrefix g w h).2)
    (hq : ∀ w h x v, SupportInv h w → (runPrefix g w h).1 = .ok (x,v) →
      StateSupported (runPrefix g w h).2 v) : Preserves g := by
  intro w h hi
  obtain ⟨s,hs⟩ := ha w h
  have truth := (hv w h hi.1.1).choose_spec.2.1
  have hsafety : HistorySafe (runPrefix g w h).2 := ⟨truth,hc w h hi⟩
  refine ⟨s,hs,hsafety,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact ⟨hsafety,hq w h out.1 out.2 hi hr⟩

theorem Checks.of_unchanged (ha : Appends g)
    (hq : ∀ w h, (runPrefix g w h).2.filterMap sensitive = h.filterMap sensitive)
    (hi : Checks h) : Checks (runPrefix g w h).2 := by
  obtain ⟨s,hs⟩ := ha w h
  have he := hq w h
  rw [hs,List.filterMap_append] at he
  have empty : s.filterMap sensitive = [] := by simpa using he
  rw [hs]
  exact hi.quiet empty

theorem session (pid : PeerId) : Preserves (HistoryAdapters.session pid) := by
  apply preserve_facts _ (Appends.focus _ _ _) (HistoryAdapters.session_valid pid)
  · intro w h hi
    apply Checks.of_unchanged (Appends.focus _ _ _) _ hi.1.2
    intro w h
    change (runPrefix (focusPrefix HistoryAdapters.encode HistoryAdapters.decode
      (liftWGObserver (focusStatePrefix Origins.sessionEncode Origins.sessionDecode
        (SessionOrigin.observed pid)))) w h).2.filterMap sensitive = _
    rw [liftWGObserver_focus,focus_compose]
    exact focusPrefix_other _ _ sensitive (by intro e; cases e <;> rfl) _ w h
  · intro w h x v hi hr
    have input : MaterialOrigin.Valid SessionOrigin.Receipt.Valid
        ((h.filterMap HistoryAdapters.decode).filterMap Origins.sessionDecode) := by
      intro e hm
      obtain ⟨a,ha,he⟩ := List.mem_filterMap.mp hm
      have truth := hi.1.1 a ha
      cases a <;> simp only [Origins.sessionDecode,Option.some.injEq,reduceCtorEq] at he
      all_goals subst e; exact truth
    let I := fun (h : List Origins.Event) (w : World) =>
      MaterialOrigin.Valid SessionOrigin.Receipt.Valid (h.filterMap Origins.sessionDecode) ∧
        Origins.Inv (Origins.sessions h) w.wg
    let S := fun (h : List Origins.Event) => MaterialOrigin.Valid SessionOrigin.Receipt.Valid (h.filterMap Origins.sessionDecode)
    have localProof : PrefixEnsures I S (liftWGObserver (Origins.localSession pid)) (fun _ => I) := by
      exact (Origins.localSession_support pid).liftWGObserver
    have hp := PrefixEnsures.focus HistoryAdapters.encode HistoryAdapters.decode
      HistoryAdapters.decode_encode localProof
    have out := (hp w h ⟨input,by simpa only [StateSupported,sessions_decoded] using hi.2⟩).choose_spec.2.2
    dsimp only [I] at out
    have hrun : (runPrefix (focusPrefix HistoryAdapters.encode HistoryAdapters.decode
        (liftWGObserver (Origins.localSession pid))) w h).1 = .ok (x,v) := hr
    rw [hrun] at out
    simpa only [StateSupported,sessions_decoded] using out.2

def lifeEncode (e : LifetimeEvent) : Event := .audit (.lifetime e)

theorem life_valid_append (hi : HistoryAdapters.Valid h) (s : List LifetimeEvent) :
    HistoryAdapters.Valid (h ++ s.map lifeEncode) := by
  intro e hm
  rw [List.filterMap_append] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hi e hm
  · obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp hm
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
    simp only [lifeEncode,HistoryAdapters.decode,Option.some.injEq] at he
    subst e
    trivial

theorem life_sessions (h : List Event) (s : List LifetimeEvent) :
    sessions (h ++ s.map lifeEncode) = sessions h := by
  simp only [sessions,List.filterMap_append]
  rw [filterMap_disjoint _ _ (fun _ => rfl)]
  exact List.append_nil _

theorem decrypt_run (id : SkbId) (w : World) (h : List Event) :
    let out := runWGPrefix (RxOrigin.readDecryptPrefix id) w.wg w.ambient (RxHistory.prior h)
    let suffix := (out.2.drop (RxHistory.prior h).length).map lifeEncode
    runPrefix (HistoryAdapters.decrypt id) w h = match out.1 with
      | .error e => (.error e,h ++ suffix)
      | .ok ((result,v),ambient') =>
        (.ok (result,{w with wg := v, ambient := ambient'}),
          h ++ suffix ++ [.rx (.decrypt id ⟨result,w.wg,v,w.ambient,ambient'⟩)]) := by
  change ((runWGPrefix (Origins.localDecrypt id) w.wg w.ambient
      (h.filterMap HistoryAdapters.decode)).1.map
        (fun ((x,g),ambient) => (x,{w with wg := g, ambient})),
    h ++ ((runWGPrefix (Origins.localDecrypt id) w.wg w.ambient (h.filterMap HistoryAdapters.decode)).2.drop
      (h.filterMap HistoryAdapters.decode).length).map HistoryAdapters.encode) = _
  rw [Origins.localDecrypt_run,HistoryAdapters.input_lifetime]
  cases hr : runWGPrefix (RxOrigin.readDecryptPrefix id) w.wg w.ambient (RxHistory.prior h) with
  | mk result hist =>
    cases result with
    | error e => simp only [List.drop_left,List.map_map]; rfl
    | ok out =>
      rcases out with ⟨⟨result,v⟩,ambient'⟩
      simp only [List.append_assoc,List.drop_left,List.map_append,List.map_map,List.map_cons,List.map_nil]
      rfl

theorem decrypt (id : SkbId) : Preserves (HistoryAdapters.decrypt id) := by
  apply preserve_facts _ (Appends.focus _ _ _) (HistoryAdapters.decrypt_valid id)
  · intro w h hi
    change Checks (runPrefix (HistoryAdapters.decrypt id) w h).2
    rw [decrypt_run]
    cases hr : runWGPrefix (RxOrigin.readDecryptPrefix id) w.wg w.ambient (RxHistory.prior h) with
    | mk result hist =>
      have quiet : Checks (h ++ (hist.drop (RxHistory.prior h).length).map lifeEncode) :=
        hi.1.2.quiet (filterMap_disjoint _ _ (fun _ => rfl) _)
      cases result with
      | error e => exact quiet
      | ok out =>
        apply quiet.snoc
        change Origins.Inv (sessions (h ++ _)) w.wg
        rw [life_sessions]
        exact hi.2
  · intro w h x v hi hr
    have native : RetainsCall (RxOrigin.readDecrypt id) := by
      apply (ProjectedAction.iff_run_ambient _ _ _).mpr
      intro g ambient result g' ambient' hrun
      exact readDecrypt_retains id g g' result ambient ambient' hrun
    have keep := native.product.support hi.2
      ((HistoryAdapters.decrypt_erases id w h).symm.trans hr)
    have hs : sessions (runPrefix (HistoryAdapters.decrypt id) w h).2 = sessions h := by
      rw [decrypt_run]
      cases hrun : runWGPrefix (RxOrigin.readDecryptPrefix id) w.wg w.ambient (RxHistory.prior h) with
      | mk result hist =>
        cases result <;> simp only [sessions,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,sessionEvent,
          List.append_nil]
        all_goals rw [filterMap_disjoint lifeEncode sessionEvent (fun _ => rfl)]; exact List.append_nil _
    change Origins.Inv (sessions (runPrefix (HistoryAdapters.decrypt id) w h).2) v.wg
    rw [hs]
    exact keep

theorem poll (pid : PeerId) (budget : Nat) : Preserves (RxHistory.observePoll pid budget) := by
  intro w h hi
  let s := ((runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior h))).2.drop
    (RxJoint.seed (RxHistory.prior h)).length).map RxHistory.promote
  have hs : (runPrefix (RxHistory.observePoll pid budget) w h).2 = h ++ s := rfl
  have hv : HistoryAdapters.Valid (h ++ s) := by
    intro e hm
    rw [List.filterMap_append] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hi.1.1 e hm
    · obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp hm
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
      cases x <;> simp only [RxHistory.promote,HistoryAdapters.decode,Option.some.injEq,reduceCtorEq] at he
      subst e
      trivial
  have hc : Checks (h ++ s) := hi.1.2.quiet (filterMap_disjoint _ _ (by intro e; cases e <;> rfl) _)
  refine ⟨s,hs,by rw [hs]; exact ⟨hv,hc⟩,?_⟩
  cases hr : (runPrefix (RxHistory.observePoll pid budget) w h).1 with
  | error e => trivial
  | ok out =>
    have keep := (actualRxPoll_material pid budget).support hi.2
      ((RxHistory.observePoll_erases pid budget w h).symm.trans hr)
    refine ⟨by rw [hs]; exact ⟨hv,hc⟩,?_⟩
    change Origins.Inv (sessions (runPrefix (RxHistory.observePoll pid budget) w h).2) out.2.wg
    have eq : sessions (h ++ s) = sessions h := by
      simp only [sessions,List.filterMap_append]
      rw [filterMap_disjoint _ _ (by intro e; cases e <;> rfl)]
      exact List.append_nil _
    rw [hs,eq]
    exact keep

theorem filter_probe : Preserves (RxHistory.audit consistentFilterAudit) := by
  intro w h hi
  have run : runPrefix (RxHistory.audit consistentFilterAudit) w h =
      ((w.ambient.suspended.filterM Env.Activation.consistent).run w,
        h ++ [.audit (.probe ⟨w,RxHistory.prior h⟩)]) := by
    change ((runPrefix consistentFilterAudit w (h.filterMap RxHistory.auditEvent)).1,
      h ++ ((runPrefix consistentFilterAudit w (h.filterMap RxHistory.auditEvent)).2.drop
        (h.filterMap RxHistory.auditEvent).length).map RxHistory.Event.audit) = _
    rw [consistentFilterAudit_run]
    simp only [List.drop_left,List.map_cons,List.map_nil]
    rfl
  have hc := hi.1.2.snoc (e := .audit (.probe ⟨w,RxHistory.prior h⟩)) ⟨rfl,hi.2⟩
  have hv : HistoryAdapters.Valid (h ++ [.audit (.probe ⟨w,RxHistory.prior h⟩)]) := by
    simpa only [HistoryAdapters.Valid,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      HistoryAdapters.decode,List.append_nil] using hi.1.1
  rw [run]
  refine ⟨_,rfl,⟨hv,hc⟩,?_⟩
  cases hr : (w.ambient.suspended.filterM Env.Activation.consistent).run w with
  | error e => trivial
  | ok out =>
    refine ⟨⟨hv,hc⟩,?_⟩
    have frame : ProductRetainsCall (w.ambient.suspended.filterM Env.Activation.consistent) :=
      of_view (kernel (filterM_sameKernel productStoreView _ activationConsistent_sameKernel _))
    have keep := frame.support hi.2 hr
    simpa only [StateSupported,sessions,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      sessionEvent,List.append_nil] using keep

/-- Transport a proof across an exact execution equation, without re-running
or replacing the observer. -/
theorem congr (hg : Preserves g) (he : ∀ w h, runPrefix g w h = runPrefix f w h) : Preserves f := by
  intro w h hi
  simpa only [← he w h] using hg w h hi

theorem focus_pure (enc : E → Event) (dec : Event → Option E) (x : α) :
    Preserves (focusPrefix enc dec (pure x)) := by
  apply congr (PrefixPreserves.pure safe x)
  intro w h
  change (Except.ok (ε := Stop) (x,w),h) = (.ok (x,w),h ++ ((h.filterMap dec).drop (h.filterMap dec).length).map enc)
  simp

theorem focus_lift (enc : E → Event) (dec : Event → Option E)
    (a : Leanux.M α) (ha : ProductRetainsCall a) :
    Preserves (focusPrefix enc dec (liftPrefix a)) := by
  apply congr (lift_retains a ha)
  intro w h
  change (a.run w,h) = (a.run w,h ++ ((h.filterMap dec).drop (h.filterMap dec).length).map enc)
  simp

theorem focus_bind (enc : E → Event) (dec : Event → Option E) (hd : ∀ e, dec (enc e) = some e)
    (a : PrefixM E α) (b : α → PrefixM E β) (ha : Appends a) (hb : ∀ x, Appends (b x))
    (hp : Preserves (focusPrefix enc dec a))
    (hq : ∀ x, Preserves (focusPrefix enc dec (b x))) :
    Preserves (focusPrefix enc dec (a >>= b)) := by
  apply congr (PrefixPreserves.bind hp hq)
  exact focusPrefix_bind_appends enc dec hd ha hb

theorem focus_ite (enc : E → Event) (dec : Event → Option E) (p : Prop) [Decidable p]
    (ha : p → Preserves (focusPrefix enc dec a)) (hb : ¬p → Preserves (focusPrefix enc dec b)) :
    Preserves (focusPrefix enc dec (if p then a else b)) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem appends_ite {E α : Type} {a b : PrefixM E α} (p : Prop) [Decidable p]
    (ha : p → Appends a) (hb : ¬p → Appends b) : Appends (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

macro "support_appends" : tactic => `(tactic|
  repeat' first
    | with_reducible exact Appends.focus _ _ _
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.receiptObserved
    | with_reducible apply Appends.bind
    | with_reducible apply appends_ite
    | (with_reducible intro x; try dsimp only)
    | with_reducible split)

theorem focused_life (enc : E → Event) (dec : Event → Option E)
    (inj : LifetimeEvent → E) (proj : E → Option LifetimeEvent)
    (hin : ∀ h, (h.filterMap dec).filterMap proj = RxHistory.prior h)
    (hout : ∀ e, enc (inj e) = lifeEncode e)
    (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (he : ErasesPrefix g a) (ha : ProductRetainsCall a) :
    Preserves (focusPrefix enc dec (focusPrefix inj proj g)) := by
  apply congr (mixed g a he ha)
  intro w h
  change runPrefix (focusPrefix RxHistory.Event.audit RxHistory.auditEvent
    (focusPrefix AuditEvent.lifetime AuditEvent.lifetime? g)) w h = _
  rw [focus_compose,focus_compose]
  change ((runPrefix g w (h.filterMap (fun e => (RxHistory.auditEvent e).bind AuditEvent.lifetime?))).1,
    h ++ ((runPrefix g w (h.filterMap (fun e => (RxHistory.auditEvent e).bind AuditEvent.lifetime?))).2.drop
      (h.filterMap (fun e => (RxHistory.auditEvent e).bind AuditEvent.lifetime?)).length).map lifeEncode) =
      ((runPrefix g w (h.filterMap (fun e => (dec e).bind proj))).1,
    h ++ ((runPrefix g w (h.filterMap (fun e => (dec e).bind proj))).2.drop
      (h.filterMap (fun e => (dec e).bind proj)).length).map (enc ∘ inj))
  have prior : h.filterMap (fun e => (RxHistory.auditEvent e).bind AuditEvent.lifetime?) = RxHistory.prior h := by
    rw [← List.filterMap_filterMap]
    rfl
  rw [prior]
  have hi : h.filterMap (fun e => (dec e).bind proj) = RxHistory.prior h := by
    rw [← List.filterMap_filterMap]
    exact hin h
  rw [hi]
  have ho : enc ∘ inj = lifeEncode := funext hout
  rw [ho]

theorem origin_life (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (he : ErasesPrefix g a) (ha : ProductRetainsCall a) :
    Preserves (HistoryAdapters.focus (HistoryAdapters.life g)) :=
  focused_life _ _ _ _ HistoryAdapters.input_lifetime (fun _ => rfl) g a he ha

def rxEncode : MaterialOrigin.Event RxOrigin.Receipt → Event := HistoryAdapters.encode ∘ Origins.rxEncode
def rxDecode (e : Event) := (HistoryAdapters.decode e).bind Origins.rxDecode

theorem rx_decode_encode (e : MaterialOrigin.Event RxOrigin.Receipt) : rxDecode (rxEncode e) = some e := by cases e <;> rfl

theorem rx_life (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (he : ErasesPrefix g a) (ha : ProductRetainsCall a) :
    Preserves (focusPrefix rxEncode rxDecode (MaterialOrigin.access g)) := by
  change Preserves (focusPrefix rxEncode rxDecode (focusPrefix MaterialOrigin.Event.life MaterialOrigin.life? g))
  apply focused_life rxEncode rxDecode MaterialOrigin.Event.life MaterialOrigin.life? _ (fun _ => rfl) g a he ha
  intro h
  simp only [List.filterMap_filterMap,RxHistory.prior,RxHistory.auditHistory,lifetimeHistory]
  congr 1
  funext e
  cases e <;> try rfl
  case audit a => cases a <;> rfl

theorem rx_decrypt (id : SkbId) :
    Preserves (focusPrefix rxEncode rxDecode (liftWGObserver (RxOrigin.decrypt id))) := by
  apply congr (decrypt id)
  intro w h
  change runPrefix (focusPrefix HistoryAdapters.encode HistoryAdapters.decode
    (liftWGObserver (focusStatePrefix Origins.rxEncode Origins.rxDecode (RxOrigin.decrypt id)))) w h = _
  rw [liftWGObserver_focus]
  exact focus_compose _ _ _ _ _ w h

/-- A successful stored decrypt is supported by session receipts in its strict
positional prefix, at its actual captured WG and Ambient entry. The supplied input
history is not asserted to have arisen from initialization. -/
theorem HistorySafe.decrypt (h pre post : List Event) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket)
    (hh : HistorySafe h) (he : h = pre ++ .rx (.decrypt id r) :: post)
    (ho : r.value.2 = some out) :
    ∃ d k, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
      d.keypairs[r.value.1.keypair]? = some k ∧
      Origins.Supported (sessions pre) d.ifindex r.value.1.keypair k ∧
      ((decryptPacket r.value.1).run r.before).run r.ambientBefore =
        .ok ((some out,r.after),r.ambientAfter) ∧
      out = {r.value.1 with nonce := u64le r.value.1.bytes 8, bytes := out.bytes} ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le r.value.1.bytes 8))
        (r.value.1.bytes.drop 16) [] = some out.bytes := by
  have hm : RxHistory.Event.rx (.decrypt id r) ∈ h := by rw [he]; simp
  have hr : r.Valid (RxOrigin.readDecrypt id) :=
    hh.1 _ (List.mem_filterMap.mpr ⟨.rx (.decrypt id r),hm,rfl⟩)
  exact Origins.decrypt_supported (sessions pre) id r out (hh.2 pre _ post he) hr ho

/-- Saved filter entries retain the exact prior committed lifetime projection
and the support at that entry World, including a later filter Stop. -/
theorem HistorySafe.probe (h pre post : List Event) (p : ProbeEntry)
    (hh : HistorySafe h) (he : h = pre ++ .audit (.probe p) :: post) :
    p.history = RxHistory.prior pre ∧ StateSupported pre p.world :=
  hh.2 pre _ post he

end Leanux.Proofs.WG.Origins.HistorySupport
