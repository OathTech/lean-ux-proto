import Leanux.Proofs.Framing.WGKernel
import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Device

/-! Native lifecycle frames retain the original seven WG observations.
Generic factor laws retain arbitrary additional observations and action stacks. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def ratelimiterStore (v : WGStoreView) : WGStoreView := {v with ratelimiter := {}}
def ratelimiterView (g : WGWorld) : WGStoreView := ratelimiterStore (wgStoreView g)
abbrev SameRatelimiter (a : WG.M α) := SameView ratelimiterView a

theorem mayHaveSlept_sameWGStore : SameWGStore mayHaveSlept := by
  intro initial
  apply hoare_modify
  intro g h
  exact h

theorem retireDeviceUnits_sameWGStore : SameWGStore retireDeviceUnits := by
  unfold retireDeviceUnits
  apply SameView.bind (fun initial => hoare_liftAmbient
    (_root_.modify fun a => {a with
      unitPeers := a.unitPeers.filter fun (e : Nat × Nat × Nat) =>
        !((Worker.all.find? (·.index == e.2.1)).any Worker.deviceOwned),
      pendingWork := a.pendingWork.filter fun i =>
        !((Worker.all.find? (·.index == i)).any Worker.deviceOwned)})
    (fun g => wgStoreView g = initial))
  intro _
  intro initial
  apply hoare_modify
  intro g h
  exact h

theorem ratelimiterInit_sameRatelimiter : SameRatelimiter ratelimiterInit := by
  have ambient {α : Type} (a : AmbientM α) : SameRatelimiter (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun g => ratelimiterView g = initial)
  have read : SameRatelimiter (get : WG.M WGWorld) :=
    fun initial => hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have edit (f : WGWorld → WGWorld)
      (hf : ∀ g, ratelimiterView (f g) = ratelimiterView g) :
      SameRatelimiter (modify f) := by
    intro initial
    apply hoare_modify
    intro g h
    simpa only [hf] using h
  unfold ratelimiterInit
  apply SameView.bind (edit (fun k => {k with ratelimiter := {k.ratelimiter with refcnt := k.ratelimiter.refcnt + 1}}) (fun _ => rfl))
  intro _
  dsimp only
  apply SameView.bind read
  intro g
  apply SameView.bind (ambient (AmbientM.branch _ _))
  intro notFirst
  split
  · exact SameView.pure _ _
  · apply SameView.bind (ambient (AmbientM.branch _ _))
    intro cacheFailed
    split
    · exact SameView.bind (edit (fun k => {k with ratelimiter := {k.ratelimiter with refcnt := k.ratelimiter.refcnt - 1}}) (fun _ => rfl)) (fun _ => SameView.pure _ _)
    · apply SameView.bind (ambient (AmbientM.branch _ _))
      intro v4Failed
      split
      · exact SameView.bind (edit (fun k => {k with ratelimiter := {k.ratelimiter with refcnt := k.ratelimiter.refcnt - 1}}) (fun _ => rfl)) (fun _ => SameView.pure _ _)
      · apply SameView.bind (ambient (AmbientM.branch _ _))
        intro v6Failed
        split
        · exact SameView.bind (edit (fun k => {k with ratelimiter := {k.ratelimiter with refcnt := k.ratelimiter.refcnt - 1}}) (fun _ => rfl)) (fun _ => SameView.pure _ _)
        · apply SameView.bind (ambient (AmbientM.hidden .ratelimiterKey))
          intro key
          exact SameView.bind (edit (fun k => {k with ratelimiter := {k.ratelimiter with key, table := [], table6 := []}}) (fun _ => rfl)) (fun _ => SameView.pure _ _)

theorem gcEntries_sameRatelimiter (work : Bool) : SameRatelimiter (gcEntries work) := by
  have ambient {α : Type} (a : AmbientM α) : SameRatelimiter (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun g => ratelimiterView g = initial)
  have read : SameRatelimiter (get : WG.M WGWorld) :=
    fun initial => hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have edit (f : WGWorld → WGWorld)
      (hf : ∀ g, ratelimiterView (f g) = ratelimiterView g) :
      SameRatelimiter (modify f) := by
    intro initial
    apply hoare_modify
    intro g h
    simpa only [hf] using h
  have loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, SameRatelimiter (f x b)) :
      SameRatelimiter (forIn xs b f) :=
    fun initial => list_view_spec ratelimiterView (fun v => v = initial) xs b f
      (fun x b => hf x b initial)
  unfold gcEntries
  apply SameView.bind (ambient (AmbientM.hiddenClock .ratelimiterGcNow))
  intro now
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply SameView.bind
  · apply loop
    intro i state
    have report (dec : Decision) (outcome : Bool) :
        SameRatelimiter (if i == 0 then branch dec outcome else pure outcome) := by
      split
      · exact ambient (AmbientM.branch _ _)
      · exact SameView.pure _ _
    apply SameView.bind (report _ _)
    intro _
    by_cases clear : (i == 0 && !work) = true
    · simp only [clear, ite_true]
      apply SameView.bind read
      intro g
      apply SameView.bind
      · apply loop
        intro entry state
        exact SameView.bind (ambient (AmbientM.branch .gcV4EntryIter true))
          (fun _ => SameView.pure _ _)
      · intro _
        apply SameView.bind (edit
          (fun k => {k with ratelimiter := {k.ratelimiter with table := []}}) (fun _ => rfl))
        intro _
        apply SameView.bind (report _ _)
        intro _
        apply SameView.bind read
        intro g
        apply SameView.bind
        · apply loop
          intro entry state
          exact SameView.bind (ambient (AmbientM.branch .gcV6EntryIter true))
            (fun _ => SameView.pure _ _)
        · intro _
          apply SameView.bind (edit
            (fun k => {k with ratelimiter := {k.ratelimiter with table6 := []}}) (fun _ => rfl))
          intro _
          apply SameView.bind (report _ _)
          intro _
          apply SameView.bind (report _ _)
          intro hasWork
          split
          · exact SameView.bind (ambient (AmbientM.unsupported _)) (fun _ => SameView.pure _ _)
          · exact SameView.pure _ _
    · simp only [clear]
      apply SameView.bind (report _ _)
      intro _
      apply SameView.bind (report _ _)
      intro _
      apply SameView.bind (report _ _)
      intro hasWork
      split
      · exact SameView.bind (ambient (AmbientM.unsupported _)) (fun _ => SameView.pure _ _)
      · exact SameView.pure _ _
  · intro _
    apply SameView.bind (ambient (AmbientM.branch .gcBucketIter false))
    intro _
    apply SameView.bind (ambient (AmbientM.branch .gcRequeue work))
    intro requeue
    split
    · exact ambient (AmbientM.unsupported _)
    · exact SameView.pure _ _

theorem ratelimiterUninit_sameRatelimiter : SameRatelimiter ratelimiterUninit := by
  have ambient {α : Type} (a : AmbientM α) : SameRatelimiter (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun g => ratelimiterView g = initial)
  have read : SameRatelimiter (get : WG.M WGWorld) :=
    fun initial => hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have edit (f : WGWorld → WGWorld)
      (hf : ∀ g, ratelimiterView (f g) = ratelimiterView g) :
      SameRatelimiter (modify f) := by
    intro initial
    apply hoare_modify
    intro g h
    simpa only [hf] using h
  unfold ratelimiterUninit
  apply SameView.bind read
  intro g
  dsimp only
  apply SameView.bind (ambient (AmbientM.branch _ _))
  intro zero
  split
  · exact SameView.pure _ _
  · apply SameView.bind (edit (fun k => {k with ratelimiter := {k.ratelimiter with refcnt := g.ratelimiter.refcnt - 1}}) (fun _ => rfl))
    intro _
    apply SameView.bind (ambient (AmbientM.branch _ _))
    intro notLast
    split
    · exact SameView.pure _ _
    · apply SameView.bind (gcEntries_sameRatelimiter false)
      intro _
      apply SameView.bind (mayHaveSlept_sameWGStore.factor ratelimiterStore)
      intro _
      exact ambient (AmbientM.skipCut [.alloc .dAllocSlabDebugfs])

def linkDevice (d : Device) : Device :=
  {d with creatingNet := false, deviceUpdateGen := 0, cookieSecret := [], cookieSecretBirthdate := 0, pubkeyHashKey := []}
def linkStore (v : WGStoreView) : WGStoreView :=
  {v with ratelimiter := {}, dev := v.dev.map linkDevice}
def linkView (g : WGWorld) : WGStoreView := linkStore (wgStoreView g)
abbrev SameLink (a : WG.M α) := SameView linkView a

/-- Only the WG observation is masked; all additional observations remain
in both the premise and conclusion, for any actual StateT action. -/
theorem ratelimiter_link {S R α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (project : S → R × WGStoreView)
    {a : StateT S m α}
    (ha : SameView (fun s => ((project s).1, ratelimiterStore (project s).2)) a) :
    SameView (fun s => ((project s).1, linkStore (project s).2)) a := by
  exact ha.of_factor (fun p : R × WGStoreView => (p.1, linkStore p.2)) _ (fun _ => rfl)

theorem sameLinkView_of_wg {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (project : S → WGStoreView)
    {a : StateT S m α} (ha : SameView project a) :
    SameView (fun s => linkStore (project s)) a := ha.factor linkStore

theorem modifyDev_linkView_spec (P : WGStoreView → Prop) (f : Device → Device)
    (hf : ∀ d, linkDevice (f d) = linkDevice d) :
    ⦃fun g => ⌜P (linkView g)⌝⦄ modifyDev f
    ⦃⇓? _ g => ⌜P (linkView g)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g ambient x g' ambient' hp hr
  cases hr
  simpa [linkView, linkStore, wgStoreView, modifyDev,
    Option.map_map, Function.comp_def, hf] using hp

theorem cookieCheckerInit_sameLink : SameLink cookieCheckerInit := by
  have ambient {α : Type} (a : AmbientM α) : SameLink (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun g => linkView g = initial)
  have edit (f : Device → Device) (hf : ∀ d, linkDevice (f d) = linkDevice d) :
      SameLink (modifyDev f) :=
    fun initial => modifyDev_linkView_spec (fun s => s = initial) f hf
  unfold cookieCheckerInit
  apply SameView.bind (ambient (AmbientM.hiddenClock64 .cookieSecretBirthdate))
  intro birthday
  apply SameView.bind (ambient (AmbientM.hidden .cookieSecret))
  intro secret
  exact edit _ (fun _ => rfl)

theorem pubkeyHashtableAlloc_sameLink : SameLink pubkeyHashtableAlloc := by
  have ambient {α : Type} (a : AmbientM α) : SameLink (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun g => linkView g = initial)
  have edit (f : Device → Device) (hf : ∀ d, linkDevice (f d) = linkDevice d) :
      SameLink (modifyDev f) :=
    fun initial => modifyDev_linkView_spec (fun s => s = initial) f hf
  unfold pubkeyHashtableAlloc
  apply SameView.bind (ambient (AmbientM.envOk .pubkeyHashtableAlloc))
  intro allocated
  split
  · exact SameView.pure _ _
  · apply SameView.bind (ambient (AmbientM.hidden .pubkeyHashKey))
    intro key
    exact SameView.bind (edit _ (fun _ => rfl)) (fun _ => SameView.pure _ _)

def registeredLink (v : WGStoreView) : WGStoreView :=
  {v with netIfindexNext := v.netIfindexNext + 1, dev := v.dev.map fun d => {d with ifindex := v.netIfindexNext}}

/-- Every normal newlink return is either the early allocation refusal or the
registered endpoint. All other allocation/refusal paths remain original Stops. -/
theorem wgNewlink_endpoint (initial : WGStoreView) :
    ⦃fun g => ⌜linkView g = initial⌝⦄ wgNewlink
    ⦃⇓? ret g => ⌜(ret = -ENOMEM ∧ linkView g = initial) ∨
      (ret = 0 ∧ linkView g = registeredLink initial)⌝⦄ := by
  let P := fun g => linkView g = initial
  let Q := fun ret g => (ret = -ENOMEM ∧ linkView g = initial) ∨
    (ret = 0 ∧ linkView g = registeredLink initial)
  change Hoare wgNewlink P Q
  have ambient {α : Type} (a : AmbientM α) : SameLink (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun g => linkView g = initial)
  have edit (f : Device → Device) (hf : ∀ d, linkDevice (f d) = linkDevice d) :
      SameLink (modifyDev f) :=
    fun initial => modifyDev_linkView_spec (fun s => s = initial) f hf
  have keep {α : Type} {a : WG.M α} {f : α → WG.M Int} (h : SameLink a)
      (next : ∀ x, Hoare (f x) P Q) : Hoare (a >>= f) P Q :=
    hoare_bind a f (h.wp (fun v => v = initial)) next
  have choose (condition : Prop) [Decidable condition] (yes no : WG.M Int)
      (hy : Hoare yes P Q) (hn : Hoare no P Q) :
      Hoare (if condition then yes else no) P Q := by
    split <;> assumption
  have rejected : Hoare (pure (-ENOMEM) : WG.M Int) P Q :=
    hoare_consequence (hoare_pure (-ENOMEM) P) (fun _ h => h)
      (fun _ _ h => Or.inl h)
  have unwind : Hoare
      (unsupported "wg_newlink's unwinding after an allocation failure" : WG.M Int) P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro g ambient x g' ambient' hp hr
    cases hr
  have register : Hoare (do
      let ifindex := (← get).netIfindexNext
      modify fun k => {k with netIfindexNext := ifindex + 1}
      modifyDev fun d => {d with ifindex}
      skipCutExactly .neighReachTime 2 allocCuts
      return 0 : WG.M Int) P Q := by
    refine hoare_bind _ _ (hoare_get P) ?_
    intro saved
    refine hoare_bind _ _
      (Q := fun _ g => P saved ∧ g = {saved with netIfindexNext := saved.netIfindexNext + 1}) ?_ ?_
    · apply hoare_modify
      intro g hp
      rcases hp with ⟨rfl, hp⟩
      exact ⟨hp, rfl⟩
    · intro _
      refine hoare_bind _ _ (Q := fun _ g => linkView g = registeredLink initial) ?_ ?_
      · apply hoare_modify
        intro g hp
        rcases hp with ⟨hp, rfl⟩
        have h := congrArg registeredLink hp
        simpa [P, linkView, linkStore, linkDevice, registeredLink, wgStoreView,
          Option.map_map, Function.comp_def] using h
      · intro _
        refine hoare_bind _ _
          (hoare_liftAmbient (AmbientM.skipCutExactly .neighReachTime 2 allocCuts)
            (fun g => linkView g = registeredLink initial)) ?_
        intro _
        exact hoare_consequence (hoare_pure 0 (fun g => linkView g = registeredLink initial))
          (fun _ h => h) (fun _ _ h => Or.inr h)
  delta wgNewlink
  apply keep (edit (fun d => {d with creatingNet := true}) (fun _ => rfl))
  intro _
  apply keep cookieCheckerInit_sameLink
  intro _
  apply keep (edit (fun d => {d with deviceUpdateGen := 1}) (fun _ => rfl))
  intro _
  apply keep pubkeyHashtableAlloc_sameLink
  intro allocated
  apply keep (ambient (AmbientM.branch _ _))
  intro failed
  apply choose
  · exact rejected
  · apply keep (ambient (AmbientM.envOk .indexHashtableAlloc))
    intro allocated
    apply keep (ambient (AmbientM.branch _ _))
    intro failed
    apply choose
    · exact unwind
    · apply keep (ambient (AmbientM.envOk .allocWorkqueue))
      intro allocated
      apply keep (ambient (AmbientM.branch _ _))
      intro failed
      apply choose
      · exact unwind
      · apply keep (ambient (AmbientM.envOk .allocWorkqueue))
        intro allocated
        apply keep (ambient (AmbientM.branch _ _))
        intro failed
        apply choose
        · exact unwind
        · apply keep (ambient (AmbientM.envOk .allocWorkqueue))
          intro allocated
          apply keep (sameLinkView_of_wg wgStoreView mayHaveSlept_sameWGStore)
          intro _
          apply keep (ambient (AmbientM.branch _ _))
          intro failed
          apply choose
          · exact unwind
          · apply keep (ambient (AmbientM.envOk .packetQueueInit))
            intro allocated
            apply keep (ambient (AmbientM.branch _ _))
            intro failed
            apply choose
            · exact unwind
            · apply keep (ambient (AmbientM.envOk .packetQueueInit))
              intro allocated
              apply keep (ambient (AmbientM.branch _ _))
              intro failed
              apply choose
              · exact unwind
              · apply keep (ambient (AmbientM.envOk .packetQueueInit))
                intro allocated
                apply keep (ambient (AmbientM.branch _ _))
                intro failed
                apply choose
                · exact unwind
                · apply keep (ambient (AmbientM.skipCut allocCuts))
                  intro _
                  apply keep (ratelimiterInit_sameRatelimiter.of_factor linkStore linkView (fun _ => rfl))
                  intro ret
                  apply keep (ambient (AmbientM.branch _ _))
                  intro failed
                  apply choose
                  · exact unwind
                  · apply keep (ambient (AmbientM.envOk .registerNetdevice))
                    intro allocated
                    apply keep (ambient (AmbientM.branch _ _))
                    intro failed
                    apply choose
                    · exact unwind
                    · exact register

def setupLink (v : WGStoreView) : WGStoreView :=
  {v with dev := some (linkDevice {ifindex := 0, ifname := "wg0", creatingNet := false, deviceUpdateGen := 0})}

/-- The complete guarded create either retains its entry allocation geometry
or installs a fresh empty registered device, without a record-success premise. -/
theorem wgCreate_endpoint (initial : WGStoreView) :
    ⦃fun g => ⌜linkView g = initial⌝⦄ wgCreate
    ⦃⇓? _ g => ⌜linkView g = initial ∨
      (initial.dev = none ∧ linkView g = registeredLink (setupLink initial))⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g ambient ret g' ambient' hp hr
  cases hd : g.dev with
  | some d =>
    simp [wgCreate, hd] at hr
    cases hr
    exact Or.inl hp
  | none =>
    let setup : WGWorld := {g with dev := some {
      ifindex := 0, ifname := "wg0", creatingNet := false, deviceUpdateGen := 0}}
    have hi : initial.dev = none := by
      have h := congrArg WGStoreView.dev hp
      simpa [linkView, linkStore, wgStoreView, hd] using h.symm
    have hs : linkView setup = setupLink initial := by
      have h := congrArg setupLink hp
      simpa [setup, setupLink, linkView, linkStore, wgStoreView, linkDevice] using h
    simp only [wgCreate, StateT.run_bind, StateT.run_get, pure_bind, hd,
      Option.isSome_none, Bool.false_eq_true, ite_false] at hr
    have setupRun : (wgSetup.run g).run ambient = .ok (((), setup), ambient) := rfl
    rw [setupRun] at hr
    change (do
      let p ← (wgNewlink.run setup).run ambient
      ((if p.1.1 < 0 then do
          modify fun k => {k with dev := none}
          pure p.1.1
        else pure p.1.1 : WG.M Int).run p.1.2).run p.2) =
      Except.ok ((ret, g'), ambient') at hr
    cases he : (wgNewlink.run setup).run ambient with
    | error e =>
      rw [he] at hr
      cases hr
    | ok out =>
      rcases out with ⟨⟨x, v⟩, b⟩
      have hx := (hoare_iff_run_ambient _ _ _).mp (wgNewlink_endpoint (setupLink initial))
        setup ambient x v b hs he
      rcases hx with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
      · rw [he] at hr
        change Except.ok (((-ENOMEM : Int), {v with dev := none}), b) =
          Except.ok ((ret, g'), ambient') at hr
        cases hr
        apply Or.inl
        have h := congrArg (fun s : WGStoreView => {s with dev := none}) hv
        simpa [linkView, linkStore, wgStoreView, setupLink, hi, WGStoreView.ext_iff] using h
      · rw [he] at hr
        change Except.ok (((0 : Int), v), b) = Except.ok ((ret, g'), ambient') at hr
        cases hr
        exact Or.inr ⟨hi, hv⟩

end Leanux.Proofs.Framing
