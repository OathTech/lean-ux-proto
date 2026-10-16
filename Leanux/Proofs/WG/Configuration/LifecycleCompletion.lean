import Leanux.Proofs.WG.Configuration.DeviceCompletion
import Leanux.Proofs.WG.AllowedIps.RoutingDeviceLifecycleFrames

/-! Optional-device routing at the actual configuration and lifecycle calls.
An absent device is not identified with an empty resident device, and arbitrary
fixture interface rows remain permitted. Only whole-command acquisition makes
the absent configuration paths unable to emit routing completions. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false


private def Absent (original : List RoutingCompletion) (h : List RoutingCompletion) (w : WGWorld) : Prop :=
  h = original ∧ routingView w = none

private theorem absent_history (h0 : List RoutingCompletion) :
    ∀ h w, Absent h0 h w → h = h0 := fun _ _ hi => hi.1

private theorem absent_lift_wg (h0 : List RoutingCompletion) (a : WG.M α) (ha : RetainsRoutingCall a) :
    StatePrefixPreserves (fun h w _ => Absent h0 h w) (fun h => h = h0) (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  have hf := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr
  change RetainsRouting (routingView w) (routingView v) at hf
  rw [hi.2] at hf
  refine ⟨hi.1, ?_⟩
  cases hv : routingView v <;> simp_all [RetainsRouting]

private theorem absent_kernel_wg (h0 : List RoutingCompletion) (a : WG.M α) (ha : SameWGStore a) :
    StatePrefixPreserves (fun h w _ => Absent h0 h w) (fun h => h = h0) (liftWGPrefix a) :=
  absent_lift_wg h0 a (ProjectedRetainsRoutingCall.of_same (routing_kernel (project := id) a ha))

private theorem absent_bad_wg (h0 : List RoutingCompletion) (message : String) :
    StatePrefixPreserves (fun h w _ => Absent h0 h w) (fun h => h = h0)
      (liftWGPrefix (invariant message : WG.M α)) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => absent_history h0 h w hi)
  intro h w ambient x v ambient' hi hr
  cases hr

private theorem absent_abort_bind_wg (h0 : List RoutingCompletion) (a : WG.M α)
    (ha : ∀ w ambient x v ambient', routingView w = none →
      (a.run w).run ambient = .ok ((x, v), ambient') → False)
    (f : α → WGPrefix RoutingCompletion β) :
    StatePrefixPreserves (fun h w _ => Absent h0 h w) (fun h => h = h0) (liftWGPrefix a >>= f) := by
  apply StatePrefixEnsures.bind (Q := fun _ _ _ _ => False)
  · apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
    intro h w ambient x v ambient' hi hr
    exact ha w ambient x v ambient' hi.2 hr
  · intro x w ambient h hf
    contradiction

private theorem getDev_absent (w : WGWorld) (ambient : Ambient) (x : Device) (v : WGWorld)
    (ambient' : Ambient) (hn : routingView w = none)
    (hr : (getDev.run w).run ambient = .ok ((x, v), ambient')) : False := by
  have hd : w.dev = none := by simpa [routingView] using hn
  simp [getDev, invariant, AmbientM.invariant, hd] at hr
  cases hr

private theorem pubkeyLookup_absent (key : Key) (w : WGWorld) (ambient : Ambient)
    (x : Option PeerId) (v : WGWorld) (ambient' : Ambient)
    (hn : routingView w = none)
    (hr : ((pubkeyLookup key).run w).run ambient = .ok ((x, v), ambient')) : False := by
  have hd : w.dev = none := by simpa [routingView] using hn
  simp [pubkeyLookup, getDev, invariant, AmbientM.invariant, hd] at hr
  cases hr

elab "lifecycle_bind_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "not an observer contract"
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not an observer bind"
  let bindArgs := action.getAppArgs
  unless bindArgs.size ≥ 2 do Lean.throwError "missing bound action"
  let first := bindArgs[bindArgs.size - 2]!.consumeMData
  unless first.isAppOf ``liftWGPrefix do Lean.throwError "not a native lifted first action"
  let .const actual _ := first.getAppArgs.back!.consumeMData.getAppFn
    | Lean.throwError "not a constant native action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different first action"

private theorem absent_out (h0 : List RoutingCompletion) (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StatePrefixPreserves (fun h w _ => Absent h0 h w) (fun h => h = h0) (peerConfigOutObserved a peer ret) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun saved => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = saved)
  unfold peerConfigOutObserved
  repeat' first
    | contradiction
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_lift_action_head peerPut; exact absent_lift_wg h0 _ (peerPut_retainsRouting _))
    | (maintenance_lift_action_head branch; exact absent_kernel_wg h0 _ (hb _ _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => absent_history h0 h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => Absent h0 h w))
    | (maintenance_intro; try dsimp only)

/-- Every absent-entry outcome retains exactly the entry history. This is a
whole-command fact: a direct invalid setAllowedip can return before getDev. -/
theorem setPeerCmdObserved_absent (h0 : List RoutingCompletion) (a : PeerAttrs) :
    StatePrefixPreserves (fun h w _ => h = h0 ∧ routingView w = none) (fun h => h = h0)
      (setPeerCmdObserved a) := by
  change StatePrefixPreserves (fun h w _ => Absent h0 h w) _ _
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun saved => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = saved)
  unfold setPeerCmdObserved
  repeat' first
    | contradiction
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head peerConfigOutObserved; exact absent_out h0 _ _ _)
    | (lifecycle_bind_head pubkeyLookup; exact absent_abort_bind_wg h0 _ (pubkeyLookup_absent _) _)
    | (maintenance_lift_action_head branch; exact absent_kernel_wg h0 _ (hb _ _))
    | (maintenance_lift_action_head WG.andM; exact absent_kernel_wg h0 _ (DumpComposition.andM_sameView _ _ (hb _ _) (hb _ _)))
    | (maintenance_lift_action_head invariant; exact absent_bad_wg h0 _)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => absent_history h0 h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => Absent h0 h w))
    | (maintenance_intro; try dsimp only)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match

private theorem absent_removeAll (h0 : List RoutingCompletion) :
    StatePrefixPreserves (fun h w _ => Absent h0 h w) (fun h => h = h0) peerRemoveAllObserved := by
  intro w ambient h hi
  have hd : w.dev = none := by simpa [routingView] using hi.2
  have hf : runWGPrefix completedFree w ambient h =
      (.error (.invariant "no WireGuard device in this trace's fixture"), h) := by
    simp [completedFree_run, WG.free, getDev, invariant, AmbientM.invariant, hd]
    rfl
  have hg : runWGPrefix peerRemoveAllObserved w ambient h =
      (.error (.invariant "no WireGuard device in this trace's fixture"), h) := by
    unfold peerRemoveAllObserved runWGPrefix
    rw [runStatePrefix_bind]
    change runStatePrefix completedFree w ambient h =
      (.error (.invariant "no WireGuard device in this trace's fixture"), h) at hf
    rw [hf]
  have hg' : runPrefix (peerRemoveAllObserved.run w) ambient h =
      (.error (.invariant "no WireGuard device in this trace's fixture"), h) := hg
  rw [hg']
  exact ⟨[], by simp, hi.1, trivial⟩

private theorem absent_devicePeers (h0 : List RoutingCompletion) (a : DeviceAttrs) :
    StatePrefixPreserves (fun h w _ => Absent h0 h w) (fun h => h = h0) (devicePeersObserved a) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun saved => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = saved)
  unfold devicePeersObserved
  repeat' first
    | contradiction
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head setPeerCmdObserved; exact setPeerCmdObserved_absent h0 _)
    | (maintenance_lift_action_head branch; exact absent_kernel_wg h0 _ (hb _ _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => absent_history h0 h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => Absent h0 h w) _ (fun _ h w _ hi => absent_history h0 h w hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => Absent h0 h w))
    | (maintenance_intro; try dsimp only)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match

private theorem absent_deviceKey (h0 : List RoutingCompletion) (a : DeviceAttrs) :
    StatePrefixPreserves (fun h w _ => Absent h0 h w) (fun h => h = h0) (deviceKeyObserved a) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun saved => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = saved)
  unfold deviceKeyObserved
  repeat' first
    | contradiction
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head devicePeersObserved; exact absent_devicePeers h0 _)
    | (lifecycle_bind_head getDev; exact absent_abort_bind_wg h0 _ getDev_absent _)
    | (maintenance_lift_action_head branch; exact absent_kernel_wg h0 _ (hb _ _))
    | (maintenance_lift_action_head WG.andM; exact absent_kernel_wg h0 _ (DumpComposition.andM_sameView _ _ (hb _ _) (hb _ _)))
    | (maintenance_lift_action_head invariant; exact absent_bad_wg h0 _)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => absent_history h0 h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => Absent h0 h w))
    | (maintenance_intro; try dsimp only)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match

private theorem absent_deviceUpdate (h0 : List RoutingCompletion) (a : DeviceAttrs) (flags : UInt32) :
    StatePrefixPreserves (fun h w _ => Absent h0 h w) (fun h => h = h0) (deviceUpdateObserved a flags) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun saved => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = saved)
  unfold deviceUpdateObserved
  repeat' first
    | contradiction
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head deviceKeyObserved; exact absent_deviceKey h0 _)
    | (maintenance_head peerRemoveAllObserved; exact absent_removeAll h0)
    | (lifecycle_bind_head getDev; exact absent_abort_bind_wg h0 _ getDev_absent _)
    | (maintenance_lift_action_head setPort; exact absent_lift_wg h0 _ (ProjectedRetainsRoutingCall.of_same (setPort_routing _)))
    | (maintenance_lift_action_head modifyDev; exact absent_lift_wg h0 _ (ProjectedRetainsRoutingCall.of_same (modifyDev_routing (fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}) (fun _ => rfl))))
    | (maintenance_lift_action_head modifyDev; exact absent_lift_wg h0 _ (ProjectedRetainsRoutingCall.of_same (modifyDev_routing (fun d => {d with fwmark := a.fwmark.getD 0}) (fun _ => rfl))))
    | (maintenance_lift_action_head branch; exact absent_kernel_wg h0 _ (hb _ _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => absent_history h0 h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => Absent h0 h w))
    | (maintenance_intro; try dsimp only)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match

/-- This covers arbitrary fixture interface rows, including a successful
lookup with no resident device. Early normal errors and original Stops retain
exactly the entry journal; normal endpoints remain absent. -/
theorem wgSetDeviceObserved_absent (h0 : List RoutingCompletion) (a : DeviceAttrs) :
    StatePrefixPreserves (fun h w _ => h = h0 ∧ routingView w = none) (fun h => h = h0)
      (wgSetDeviceObserved a) := by
  change StatePrefixPreserves (fun h w _ => Absent h0 h w) _ _
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun saved => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = saved)
  unfold wgSetDeviceObserved
  repeat' first
    | contradiction
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head deviceUpdateObserved; exact absent_deviceUpdate h0 _ _)
    | (lifecycle_bind_head getDev; exact absent_abort_bind_wg h0 _ getDev_absent _)
    | (maintenance_lift_action_head branch; exact absent_kernel_wg h0 _ (hb _ _))
    | (maintenance_lift_action_head WG.orM; exact absent_kernel_wg h0 _ (DumpComposition.orM_sameView _ _ (hb _ _) (hb _ _)))
    | (maintenance_lift_action_head lookupInterface; exact absent_kernel_wg h0 _ ((lookupInterface_sameWGWorld _).factor wgStoreView))
    | (maintenance_lift_action_head invariant; exact absent_bad_wg h0 _)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => absent_history h0 h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => Absent h0 h w))
    | (maintenance_intro; try dsimp only)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match


private theorem global_cases_wg (initial : FlatTable × FlatTable) (g : WGPrefix RoutingCompletion α)
    (present : StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial) g
      (fun _ h w _ => GlobalCompletionState initial h w))
    (absent : ∀ h0, StatePrefixPreserves (fun h w _ => h = h0 ∧ routingView w = none)
      (fun h => h = h0) g) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial) g := by
  intro w ambient h hi
  by_cases hn : routingView w = none
  · obtain ⟨suffix, he, hh, ho⟩ := absent h w ambient h ⟨rfl, hn⟩
    refine ⟨suffix, he, (by simpa only [hh] using hi.1), ?_⟩
    cases hr : (runPrefix (g.run w) ambient h).1 with
    | error e => trivial
    | ok out =>
      rcases out with ⟨⟨x, v⟩, ambient'⟩
      have hv : routingView v = none :=
        (show (runPrefix (g.run w) ambient h).2 = h ∧ routingView v = none by simpa [hr] using ho).2
      exact ⟨(by simpa only [hh] using hi.1),
        by simpa [GlobalRoutedView, hv, hh] using
          (show completionFold h initial = ([], []) by simpa [GlobalRoutedView, hn] using hi.2)⟩
  · exact present w ambient h (hi.present hn)

theorem setPeerCmdObserved_global (initial : FlatTable × FlatTable) (a : PeerAttrs)
    (shape : PeerAddressShape a) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
      (CompletionSafe initial) (setPeerCmdObserved a) :=
  global_cases_wg initial _
    ((setPeerCmdObserved_spec initial a shape).consequence
      (fun _ _ _ hi => hi) (fun _ _ _ _ hi => hi.global)) (fun h => setPeerCmdObserved_absent h a)

theorem wgSetDeviceObserved_global (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (shape : DeviceAddressShape a) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
      (CompletionSafe initial) (wgSetDeviceObserved a) :=
  global_cases_wg initial _
    ((wgSetDeviceObserved_spec initial a shape).consequence
      (fun _ _ _ hi => hi) (fun _ _ _ _ hi => hi.global)) (fun h => wgSetDeviceObserved_absent h a)

/- The original suffix has no routing completion cut. Keeping it as one lift
retains prior events on every queue/record Stop; only normal return drops wg. -/
private def destructFinish : WG.M Unit := do
  let d ← getDev
  if !d.sendWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.empty || !d.clearWorkQueue.isEmpty then
    unsupported "wg_destruct with queued work (destroy_workqueue runs it)"
  if !d.handshakeQueue.empty then
    invariant "wg_destruct with handshake messages queued (wg_stop drains the ring)"
  mayHaveSlept
  modifyDev fun d => {d with handshakeQueueLen := 0}
  mayHaveSlept
  ratelimiterUninit
  modify fun k => {k with dev := none}
  retireDeviceUnits

def wgDestructObserved : WGPrefix RoutingCompletion Unit := do
  liftWGPrefix (modifyDev fun d => {d with creatingNet := false, incomingPort := 0})
  liftWGPrefix (socketReinit none none)
  peerRemoveAllObserved
  liftWGPrefix destructFinish

def wgDeleteObserved : WGPrefix RoutingCompletion Int := do
  if (← liftWGPrefix getWG).dev.isNone then return -ENODEV
  if (← liftWGPrefix getDev).running then liftWGPrefix wgDown
  liftWGPrefix (skipCut allocCuts)
  liftWGPrefix mayHaveSlept
  wgDestructObserved
  return 0

theorem wgDestructObserved_erases : ErasesStatePrefix wgDestructObserved (wgDestruct : WG.M Unit) := by
  unfold wgDestructObserved wgDestruct destructFinish
  repeat' first
    | contradiction
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head peerRemoveAllObserved; exact peerRemoveAllObserved_erases)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | maintenance_intro
    | (with_reducible split)
    | rfl

theorem wgDeleteObserved_erases : ErasesStatePrefix wgDeleteObserved (wgDelete : WG.M Int) := by
  unfold wgDeleteObserved wgDelete
  simp only [pure_bind]
  repeat' first
    | contradiction
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head peerRemoveAllObserved; exact peerRemoveAllObserved_erases)
    | (maintenance_head wgDestructObserved; exact wgDestructObserved_erases)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | maintenance_intro
    | (with_reducible split)
    | rfl


private theorem destructFinish_none (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : (destructFinish.run w).run ambient = .ok (((), v), ambient')) : routingView v = none := by
  have triv {α : Type} (a : WG.M α) : Hoare a (fun _ => True) (fun _ _ => True) :=
    (hoare_iff_run_ambient _ _ _).mpr (fun _ _ _ _ _ _ _ => trivial)
  have hc : Hoare destructFinish (fun _ => True) (fun _ w => routingView w = none) := by
    have ht := (routing_kernel (project := id) _ retireDeviceUnits_sameWGStore).wp (fun v => v = none)
    unfold destructFinish
    apply hoare_bind _ _ (triv _)
    intro d
    dsimp only
    split
    · apply hoare_bind _ _ (Q := fun _ _ => False)
      · apply (hoare_iff_run_ambient _ _ _).mpr
        intro w ambient x v ambient' _ hr
        cases hr
      · intro _
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w ambient x v ambient' impossible _
        contradiction
    · try dsimp only
      split
      · apply hoare_bind _ _ (Q := fun _ _ => False)
        · apply (hoare_iff_run_ambient _ _ _).mpr
          intro w ambient x v ambient' _ hr
          cases hr
        · intro _
          apply (hoare_iff_run_ambient _ _ _).mpr
          intro w ambient x v ambient' impossible _
          contradiction
      · apply hoare_bind _ _ (triv _)
        intro _
        apply hoare_bind _ _ (triv _)
        intro _
        apply hoare_bind _ _ (triv _)
        intro _
        apply hoare_bind _ _ (triv _)
        intro _
        apply hoare_bind _ _ (Q := fun _ w => routingView w = none)
          (hoare_modify (fun w : WGWorld => {w with dev := none}) (fun _ _ => rfl))
        intro _
        exact ht
  exact (hoare_iff_run_ambient _ _ _).mp hc w ambient () v ambient' True.intro hr

private theorem destructFinish_spec (initial : FlatTable × FlatTable) :
    StatePrefixEnsures (fun h w _ => CompletionEmpty initial h w) (CompletionSafe initial)
      (liftWGPrefix destructFinish) (fun _ h w _ => GlobalCompletionState initial h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1)
  intro h w ambient u v ambient' hi hr
  cases u
  exact ⟨hi.1.1, by simpa [GlobalRoutedView, destructFinish_none w v ambient ambient' hr] using hi.2⟩

private theorem destruct_present (initial : FlatTable × FlatTable) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      wgDestructObserved (fun _ h w _ => GlobalCompletionState initial h w) := by
  unfold wgDestructObserved
  apply StatePrefixEnsures.bind (completion_lift_retains_wg initial _
    (ProjectedRetainsRoutingCall.of_same (modifyDev_routing
      (fun d => {d with creatingNet := false, incomingPort := 0}) (fun _ => rfl))))
  intro _
  apply StatePrefixEnsures.bind (completion_lift_retains_wg initial _
    (ProjectedRetainsRoutingCall.of_same (socketControl_routing_native _ (socketReinit_sameSocket none none))))
  intro _
  exact StatePrefixEnsures.bind (peerRemoveAllObserved_empty_spec initial) (fun _ => destructFinish_spec initial)

private theorem destruct_absent (h0 : List RoutingCompletion) :
    StatePrefixPreserves (fun h w _ => h = h0 ∧ routingView w = none)
      (fun h => h = h0) wgDestructObserved := by
  unfold wgDestructObserved
  apply StatePrefixEnsures.bind (absent_lift_wg h0 _
    (ProjectedRetainsRoutingCall.of_same (modifyDev_routing
      (fun d => {d with creatingNet := false, incomingPort := 0}) (fun _ => rfl))))
  intro _
  apply absent_abort_bind_wg h0 _ ?_
  intro w ambient x v ambient' hn hr
  have hd : w.dev = none := by simpa [routingView] using hn
  simp [socketReinit, getDev, invariant, AmbientM.invariant, hd] at hr
  cases hr

theorem wgDestructObserved_global (initial : FlatTable × FlatTable) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
      (CompletionSafe initial) wgDestructObserved :=
  global_cases_wg initial _ (destruct_present initial) destruct_absent

private theorem global_safe (initial : FlatTable × FlatTable) :
    ∀ h w, GlobalCompletionState initial h w → CompletionSafe initial h := fun _ _ hi => hi.1

private theorem global_getWG (initial : FlatTable × FlatTable) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
      (CompletionSafe initial) (liftWGPrefix getWG) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => global_safe initial h w hi)
  intro h w ambient x v ambient' hi hr
  cases hr
  exact hi

theorem wgDeleteObserved_global (initial : FlatTable × FlatTable) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
      (CompletionSafe initial) wgDeleteObserved := by
  have ambient {α : Type} (a : AmbientM α) : SameWGStore (MonadLift.monadLift a) :=
    fun saved => hoare_liftAmbient a (fun w => wgStoreView w = saved)
  unfold wgDeleteObserved
  repeat' first
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head wgDestructObserved; exact wgDestructObserved_global initial)
    | (maintenance_lift_action_head getWG; exact global_getWG initial)
    | (maintenance_lift_action_head wgDown; exact global_completion_lift_wg initial _ wgDown_routing)
    | (maintenance_lift_action_head getDev; exact global_completion_same_wg initial _ (routing_kernel (project := id) _ getDev_sameWGStore))
    | (maintenance_lift_action_head skipCut; exact global_completion_same_wg initial _ (routing_kernel (project := id) _ (ambient _)))
    | (maintenance_lift_action_head mayHaveSlept; exact global_completion_same_wg initial _ (routing_kernel (project := id) _ mayHaveSlept_sameWGStore))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => global_safe initial h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => GlobalCompletionState initial h w))
    | maintenance_intro
    | (with_reducible split)

theorem global_initial (trace : Runner.Trace) (w : World)
    (hk : w.wg = Runner.initialWG trace.net trace.bare) :
    GlobalCompletionState ([], []) [] w.wg := by
  refine ⟨.nil, ?_⟩
  rw [hk]
  exact initialWG_global _ _

private theorem absent_lift (h0 : List RoutingCompletion) (a : Leanux.M α) (ha : ProjectedRetainsRoutingCall World.wg a) :
    PrefixPreserves (fun h (w : World) => Absent h0 h w.wg) (fun h => h = h0) (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  have hf := (ProjectedAction.iff_run _ _ _).mp ha w x v hr
  rw [hi.2] at hf
  refine ⟨hi.1, ?_⟩
  cases hv : routingView v.wg <;> simp_all [RetainsRouting]

private theorem absent_kernel (h0 : List RoutingCompletion) (a : Leanux.M α) (ha : SameProductStore a) :
    PrefixPreserves (fun h (w : World) => Absent h0 h w.wg) (fun h => h = h0) (liftPrefix a) :=
  absent_lift h0 a (ProjectedRetainsRoutingCall.of_same (routing_kernel a (ha.of_factor (fun s : ProductStore43 => s.2.2.2) (fun w : World => wgStoreView w.wg) (fun _ => rfl))))

private theorem absent_bad (h0 : List RoutingCompletion) (message : String) :
    PrefixPreserves (fun h (w : World) => Absent h0 h w.wg) (fun h => h = h0) (liftPrefix (invariant message : Leanux.M α)) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun h w hi => absent_history h0 h w.wg hi)
  intro h w x v hi hr
  cases hr

private theorem absent_abort_bind (h0 : List RoutingCompletion) (a : Leanux.M α)
    (ha : ∀ w x v, routingView w.wg = none → a.run w = .ok (x, v) → False)
    (f : α → PrefixM RoutingCompletion β) :
    PrefixPreserves (fun h (w : World) => Absent h0 h w.wg) (fun h => h = h0) (liftPrefix a >>= f) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (Q := fun _ _ _ => False)
  · apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
    intro h w x v hi hr
    exact ha w x v hi.2 hr
  · intro x w h hf
    contradiction

private theorem global_cases (initial : FlatTable × FlatTable) (g : PrefixM RoutingCompletion α)
    (present : PrefixEnsures (fun h (w : World) => CompletionState initial h w.wg) (CompletionSafe initial) g (fun _ h (w : World) => GlobalCompletionState initial h w.wg))
    (absent : ∀ h0, PrefixPreserves (fun h w => h = h0 ∧ routingView w.wg = none) (fun h => h = h0) g) :
    PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) g := by
  intro w h hi
  by_cases hn : routingView w.wg = none
  · obtain ⟨suffix, he, hh, ho⟩ := absent h w h ⟨rfl, hn⟩
    refine ⟨suffix, he, (by simpa only [hh] using hi.1), ?_⟩
    cases hr : (runPrefix g w h).1 with
    | error e => trivial
    | ok out =>
      have hv : routingView out.2.wg = none := (show (runPrefix g w h).2 = h ∧ routingView out.2.wg = none by simpa [hr] using ho).2
      exact ⟨(by simpa only [hh] using hi.1), by simpa [GlobalRoutedView, hv, hh] using (show completionFold h initial = ([], []) by simpa [GlobalRoutedView, hn] using hi.2)⟩
  · obtain ⟨suffix, he, hs, ho⟩ := present w h (hi.present hn)
    refine ⟨suffix, he, hs, ?_⟩
    cases hr : (runPrefix g w h).1 with
    | error e => trivial
    | ok out => simpa [hr] using ho


end Leanux.Proofs.WG.Configuration
