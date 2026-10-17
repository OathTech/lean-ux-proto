import Leanux.Proofs.WG.Origins.OwnerHistory
import Leanux.Proofs.WG.Origins.CurrentSensitive
import Leanux.Proofs.WG.Origins.SupportRunner
import Leanux.Proofs.WG.Packets.PublicationRetained

/-! Receiving-owner bounds accompany the existing current and allocation
journal contracts. Carrier checks depend on the captured World alone; the
history-dependent current checks retain their strict earlier-prefix meaning.
No new execution observer or initialized-run premise is introduced. -/
namespace Leanux.Proofs.WG.OwnerChecks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
open Origins.HistorySupport (sensitive lifeEncode sessions)

def Checked : RxHistory.Event → Prop
  | .rx (.decrypt _ r) => OwnerBounds.Carrier r.before
  | .audit (.probe p) => OwnerBounds.Carrier p.world.wg
  | _ => True

def Checks (h : List RxHistory.Event) : Prop := ∀ e ∈ h, Checked e

structure Inv (h : List RxHistory.Event) (w : World) : Prop where
  current : CurrentChecks.Inv h w
  boundary : RxHistory.BoundaryInv h w
  carrier : OwnerBounds.Carrier w.wg
  checked : Checks h

def Safe (h : List RxHistory.Event) : Prop :=
  CurrentChecks.Safe h ∧ RxHistory.BoundarySafe h ∧ Checks h

abbrev Preserves (g : RxHistory.Obs α) := PrefixPreserves Inv Safe g

theorem Inv.safe (hi : Inv h w) : Safe h :=
  ⟨⟨hi.current.1.1,hi.current.2.2⟩,hi.boundary.safe,hi.checked⟩

theorem Inv.allocation (hi : Inv h w) : AllocationInv (RxHistory.prior h) w.wg :=
  hi.boundary.audit.1

theorem Checks.append (hh : Checks h) (hs : Checks s) : Checks (h ++ s) := by
  intro e he
  rcases List.mem_append.mp he with old | new
  · exact hh e old
  · exact hs e new

theorem Checks.snoc (hh : Checks h) (he : Checked e) : Checks (h ++ [e]) :=
  hh.append (by intro x hx; simpa only [List.mem_singleton.mp hx] using he)

theorem checked_quiet (he : sensitive e = none) : Checked e := by
  cases e <;> try trivial
  case rx r => cases r <;> first | trivial | cases he
  case audit a => cases a <;> first | trivial | cases he

theorem Checks.quiet (hh : Checks h) (hs : s.filterMap sensitive = []) : Checks (h ++ s) := by
  apply hh.append
  intro e he
  apply checked_quiet
  cases chosen : sensitive e with
  | none => rfl
  | some value =>
    have found : value ∈ s.filterMap sensitive := List.mem_filterMap.mpr ⟨e,he,chosen⟩
    simp [hs] at found

theorem Checks.of_unchanged (appends : Appends g)
    (quiet : ∀ w h, (runPrefix g w h).2.filterMap sensitive = h.filterMap sensitive)
    (hi : Checks h) : Checks (runPrefix g w h).2 := by
  obtain ⟨s,hs⟩ := appends w h
  have eq := quiet w h
  rw [hs,List.filterMap_append] at eq
  have empty : s.filterMap sensitive = [] := by simpa using eq
  rw [hs]
  exact hi.quiet empty

/-- Each conjunct concerns the identical run and output journal. A Stop keeps
safe history only, and never acquires a fictitious normal state. -/
theorem combine (g : RxHistory.Obs α)
    (current : CurrentChecks.Preserves g)
    (boundary : PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe g)
    (carrier : ∀ w h, Inv h w → ∀ x v, (runPrefix g w h).1 = .ok (x,v) → OwnerBounds.Carrier v.wg)
    (checks : ∀ w h, Inv h w → Checks (runPrefix g w h).2) : Preserves g := by
  intro w h hi
  obtain ⟨s,hs,safe,post⟩ := current w h hi.current
  obtain ⟨_,_,bsafe,bpost⟩ := boundary w h hi.boundary
  have checked := checks w h hi
  refine ⟨s,hs,⟨safe,bsafe,checked⟩,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    rw [hr] at post bpost
    exact ⟨post,bpost,carrier w h hi out.1 out.2 hr,checked⟩

/-- The actual session updates its receipt while preserving owner bounds and
the original allocation journal. No old incoming receipt is newly certified. -/
theorem session (pid : PeerId) : Preserves (Origins.HistoryAdapters.session pid) := by
  apply combine _ (CurrentChecks.session pid) (Origins.HistoryAdapters.session_preserves pid)
  · intro w h hi x v hr
    have kept := (OwnerHistory.session pid w h ⟨hi.current,hi.carrier⟩).choose_spec.2.2
    rw [hr] at kept
    exact kept.2
  · intro w h hi
    apply Checks.of_unchanged (Appends.focus _ _ _) _ hi.checked
    intro w h
    change (runPrefix (focusPrefix Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode
      (focusPrefix Origins.sessionEncode Origins.sessionDecode
        (liftWGObserver (SessionOrigin.observed pid)))) w h).2.filterMap sensitive = _
    rw [Origins.HistorySupport.focus_compose]
    exact focusPrefix_other _ _ sensitive (by intro e; cases e <;> rfl) _ w h

theorem decrypt_checks (id : SkbId) (w : World) (h : List RxHistory.Event)
    (carrier : OwnerBounds.Carrier w.wg) (checks : Checks h) :
    Checks (runPrefix (Origins.HistoryAdapters.decrypt id) w h).2 := by
  rw [Origins.HistorySupport.decrypt_run]
  cases run : runWGPrefix (RxOrigin.readDecryptPrefix id) w.wg w.ambient (RxHistory.prior h) with
  | mk result history =>
    have quiet : Checks (h ++ (history.drop (RxHistory.prior h).length).map lifeEncode) :=
      checks.quiet (filterMap_disjoint _ _ (fun _ => rfl) _)
    cases result with
    | error e => exact quiet
    | ok out => exact quiet.snoc carrier

/-- Decrypt carrier transport is explicit until its concrete native contract
is supplied. The actual captured entry always uses the input carrier. -/
theorem decrypt (id : SkbId)
    (current : CurrentChecks.Preserves (Origins.HistoryAdapters.decrypt id))
    (native : Framing.Preserves OwnerBounds.Carrier (RxOrigin.readDecrypt id)) :
    Preserves (Origins.HistoryAdapters.decrypt id) := by
  apply combine _ current (Origins.HistoryAdapters.decrypt_preserves id)
  · intro w h hi x v hr
    have erased := (Origins.HistoryAdapters.decrypt_erases id w h).symm.trans hr
    rw [liftWG_run] at erased
    cases source : ((RxOrigin.readDecrypt id).run w.wg).run w.ambient with
    | error e => simp [source,Except.map] at erased
    | ok endpoint =>
      rcases endpoint with ⟨⟨result,u⟩,ambient⟩
      simp only [source,Except.map,Except.ok.injEq] at erased
      have kept := (hoare_iff_run_ambient _ _ _).mp native w.wg w.ambient result u ambient hi.carrier source
      cases erased
      exact kept
  · intro w h hi
    exact decrypt_checks id w h hi.carrier hi.checked

theorem filter_probe : Preserves (RxHistory.audit consistentFilterAudit) := by
  apply combine _ CurrentChecks.filter_probe
    (RxHistory.audit_preserves _ consistentFilterAudit_preserves)
  · intro w h hi x v hr
    rw [CurrentChecks.filter_run] at hr
    have frame := (ProjectedAction.iff_run _ _ _).mp
      (filterM_sameKernel productStoreView _ activationConsistent_sameKernel _) w x v hr
    have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) frame
    constructor
    · simpa only [CurrentIdentity.ReceivingOwnersBelow,dev] using hi.carrier.owners
    · simpa only [RxCredits.RxCompatible,RxCredits.KeyCompatible,dev] using hi.carrier.compatible
    · simpa only [OwnerBounds.RxKeysBelow,dev] using hi.carrier.rxKeys
  · intro w h hi
    rw [CurrentChecks.filter_run]
    exact hi.checked.snoc hi.carrier

/-- At the named occurrence, current support uses its strict earlier session
prefix and owner compatibility uses the very same captured native entry. -/
theorem Safe.decrypt {id : SkbId} (safe : Safe h)
    (position : h = pre ++ .rx (.decrypt id r) :: post) :
    CurrentLifecycle.Inv (sessions pre) r.before ∧ OwnerBounds.Carrier r.before := by
  refine ⟨CurrentChecks.Safe.decrypt safe.1 position,?_⟩
  apply safe.2.2 (.rx (.decrypt id r))
  rw [position]
  simp

theorem Safe.probe (safe : Safe h)
    (position : h = pre ++ .audit (.probe p) :: post) :
    p.history = RxHistory.prior pre ∧ CurrentSessionPrefix.StateInv pre p.world ∧
      OwnerBounds.Carrier p.world.wg := by
  obtain ⟨history,current⟩ := CurrentChecks.Safe.probe safe.1 position
  refine ⟨history,current,?_⟩
  apply safe.2.2 (.audit (.probe p))
  rw [position]
  simp


/-- The actual fixture establishes all conjuncts on the empty journal, for both
network and bare flags. Only the original WG store projection is constrained. -/
theorem initial (net bare : Bool) (w : World)
    (hw : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  refine ⟨⟨Origins.HistorySupport.support_initial net bare w hw,
    ⟨ConfiguredMaintenance.configured_initial net bare w.wg hw,
      CurrentIdentity.initial net bare w.wg hw⟩,?_⟩,
    RxHistory.boundary_initial w (allocation_initial net bare w.wg hw),
    OwnerBounds.initial net bare w.wg hw,?_⟩
  · intro pre e post position
    have member : e ∈ ([] : List RxHistory.Event) := by rw [position]; simp
    cases member
  · intro e member
    cases member

/-- A specified decrypt occurrence and its actual successful publication use
one strict earlier session prefix for material and current peer identity.
Initialized reachability and later packet transport remain separate. -/
theorem Safe.published {id : SkbId} (safe : Safe h)
    (position : h = pre ++ .rx (.decrypt id r) :: post)
    (published : PublicationIdentity.Published id r out pid v ambient) :
    PublicationIdentity.CurrentCertificate (sessions pre) id r out pid v := by
  obtain ⟨current,carrier⟩ := safe.decrypt position
  exact PublicationIdentity.published_current (sessions pre) id r out pid v ambient
    current.2 carrier.compatible published

end Leanux.Proofs.WG.OwnerChecks
