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

private def Absent (original : List RoutingCompletion) (h : List RoutingCompletion) (w : World) : Prop :=
  h = original ∧ routingView w = none

private theorem absent_history (h0 : List RoutingCompletion) :
    ∀ h w, Absent h0 h w → h = h0 := fun _ _ hi => hi.1

private theorem absent_lift (h0 : List RoutingCompletion) (a : M α) (ha : RetainsRoutingCall a) :
    PrefixPreserves (Absent h0) (fun h => h = h0) (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  have hf := ha w x v hr
  rw [hi.2] at hf
  refine ⟨hi.1, ?_⟩
  cases hv : routingView v <;> simp_all [RetainsRouting]

private theorem absent_kernel (h0 : List RoutingCompletion) (a : M α) (ha : SameKernel a) :
    PrefixPreserves (Absent h0) (fun h => h = h0) (liftPrefix a) :=
  absent_lift h0 a (.of_same (routing_kernel a ha))

private theorem absent_bad (h0 : List RoutingCompletion) (message : String) :
    PrefixPreserves (Absent h0) (fun h => h = h0) (liftPrefix (invariant message : M α)) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (absent_history h0)
  intro h w x v hi hr
  cases hr

private theorem absent_abort_bind (h0 : List RoutingCompletion) (a : M α)
    (ha : ∀ w x v, routingView w = none → a.run w = .ok (x, v) → False)
    (f : α → PrefixM RoutingCompletion β) :
    PrefixPreserves (Absent h0) (fun h => h = h0) (liftPrefix a >>= f) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (Q := fun _ _ _ => False)
  · apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
    intro h w x v hi hr
    exact ha w x v hi.2 hr
  · intro x w h hf
    contradiction

private theorem getDev_absent (w : World) (x : Device) (v : World)
    (hn : routingView w = none) (hr : getDev.run w = .ok (x, v)) : False := by
  have hd : w.k.wg = none := by simpa [routingView] using hn
  simp [getDev, getK, invariant, hd] at hr

private theorem pubkeyLookup_absent (key : Key) (w : World) (x : Option PeerId) (v : World)
    (hn : routingView w = none) (hr : (pubkeyLookup key).run w = .ok (x, v)) : False := by
  have hd : w.k.wg = none := by simpa [routingView] using hn
  simp [pubkeyLookup, getDev, getK, invariant, hd] at hr

private theorem absent_out (h0 : List RoutingCompletion) (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    PrefixPreserves (Absent h0) (fun h => h = h0) (peerConfigOutObserved a peer ret) := by
  unfold peerConfigOutObserved
  repeat' first
    | with_reducible exact absent_lift h0 _ (peerPut_retainsRouting _)
    | with_reducible exact absent_kernel h0 _ (sameKernel_branch _ _)
    | with_reducible exact PrefixPreserves.pure (absent_history h0) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)

/-- Every absent-entry outcome retains exactly the entry history. This is a
whole-command fact: a direct invalid setAllowedip can return before getDev. -/
theorem setPeerCmdObserved_absent (h0 : List RoutingCompletion) (a : PeerAttrs) :
    PrefixPreserves (fun h w => h = h0 ∧ routingView w = none) (fun h => h = h0)
      (setPeerCmdObserved a) := by
  change PrefixPreserves (Absent h0) _ _
  unfold setPeerCmdObserved
  repeat' first
    | with_reducible exact absent_out h0 _ _ _
    | with_reducible exact absent_abort_bind h0 _ (pubkeyLookup_absent _) _
    | (solve | with_reducible apply absent_kernel h0; repeat' first | exact sameKernel_branch _ _ | exact (by intro w x v hr; cases hr) | apply andM_sameKernel)
    | with_reducible exact absent_bad h0 _
    | with_reducible exact PrefixPreserves.pure (absent_history h0) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

private theorem absent_removeAll (h0 : List RoutingCompletion) :
    PrefixPreserves (Absent h0) (fun h => h = h0) peerRemoveAllObserved := by
  intro w h hi
  have hd : w.k.wg = none := by simpa [routingView] using hi.2
  have hf : runPrefix completedFree w h =
      (.error (.invariant "no WireGuard device in this trace's fixture"), h) := by
    simp [completedFree_run, WG.free, getDev, getK, invariant, hd]
  unfold peerRemoveAllObserved
  rw [runPrefix_bind, hf]
  exact ⟨[], by simp, hi.1, trivial⟩

private theorem absent_devicePeers (h0 : List RoutingCompletion) (a : DeviceAttrs) :
    PrefixPreserves (Absent h0) (fun h => h = h0) (devicePeersObserved a) := by
  unfold devicePeersObserved
  repeat' first
    | exact setPeerCmdObserved_absent h0 _
    | with_reducible exact absent_kernel h0 _ (sameKernel_branch _ _)
    | with_reducible exact PrefixPreserves.pure (absent_history h0) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (absent_history h0)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

private theorem absent_deviceKey (h0 : List RoutingCompletion) (a : DeviceAttrs) :
    PrefixPreserves (Absent h0) (fun h => h = h0) (deviceKeyObserved a) := by
  unfold deviceKeyObserved
  repeat' first
    | with_reducible exact absent_devicePeers h0 _
    | with_reducible exact absent_abort_bind h0 _ getDev_absent _
    | (solve | with_reducible apply absent_kernel h0; repeat' first | exact sameKernel_branch _ _ | apply andM_sameKernel)
    | with_reducible exact absent_bad h0 _
    | with_reducible exact PrefixPreserves.pure (absent_history h0) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

private theorem absent_deviceUpdate (h0 : List RoutingCompletion) (a : DeviceAttrs) (flags : UInt32) :
    PrefixPreserves (Absent h0) (fun h => h = h0) (deviceUpdateObserved a flags) := by
  unfold deviceUpdateObserved
  repeat' first
    | with_reducible exact absent_deviceKey h0 _
    | with_reducible exact absent_removeAll h0
    | with_reducible exact absent_abort_bind h0 _ getDev_absent _
    | with_reducible exact absent_lift h0 _ (.of_same (setPort_routing _))
    | with_reducible exact absent_lift h0 _ (.of_same (modifyDev_routing (fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}) (fun _ => rfl)))
    | with_reducible exact absent_lift h0 _ (.of_same (modifyDev_routing (fun d => {d with fwmark := a.fwmark.getD 0}) (fun _ => rfl)))
    | with_reducible exact absent_kernel h0 _ (sameKernel_branch _ _)
    | with_reducible exact PrefixPreserves.pure (absent_history h0) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

/-- This covers arbitrary fixture interface rows, including a successful
lookup with no resident device. Early normal errors and original Stops retain
exactly the entry journal; normal endpoints remain absent. -/
theorem wgSetDeviceObserved_absent (h0 : List RoutingCompletion) (a : DeviceAttrs) :
    PrefixPreserves (fun h w => h = h0 ∧ routingView w = none) (fun h => h = h0)
      (wgSetDeviceObserved a) := by
  change PrefixPreserves (Absent h0) _ _
  unfold wgSetDeviceObserved
  repeat' first
    | with_reducible exact absent_deviceUpdate h0 _ _
    | with_reducible exact absent_abort_bind h0 _ getDev_absent _
    | (solve | with_reducible apply absent_kernel h0; repeat' first | exact sameKernel_branch _ _ | exact lookupInterface_sameKernel _ | apply orM_sameKernel)
    | with_reducible exact absent_bad h0 _
    | with_reducible exact PrefixPreserves.pure (absent_history h0) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

private theorem global_cases (initial : FlatTable × FlatTable) (g : PrefixM RoutingCompletion α)
    (present : PrefixEnsures (CompletionState initial) (CompletionSafe initial) g (fun _ => GlobalCompletionState initial))
    (absent : ∀ h0, PrefixPreserves (fun h w => h = h0 ∧ routingView w = none) (fun h => h = h0) g) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) g := by
  intro w h hi
  by_cases hn : routingView w = none
  · obtain ⟨suffix, he, hh, ho⟩ := absent h w h ⟨rfl, hn⟩
    refine ⟨suffix, he, (by simpa only [hh] using hi.1), ?_⟩
    cases hr : (runPrefix g w h).1 with
    | error e => trivial
    | ok out =>
      have hv : routingView out.2 = none := (show (runPrefix g w h).2 = h ∧ routingView out.2 = none by simpa [hr] using ho).2
      exact ⟨(by simpa only [hh] using hi.1), by simpa [GlobalRoutedView, hv, hh] using (show completionFold h initial = ([], []) by simpa [GlobalRoutedView, hn] using hi.2)⟩
  · obtain ⟨suffix, he, hs, ho⟩ := present w h (hi.present hn)
    refine ⟨suffix, he, hs, ?_⟩
    cases hr : (runPrefix g w h).1 with
    | error e => trivial
    | ok out => simpa [hr] using ho

theorem setPeerCmdObserved_global (initial : FlatTable × FlatTable) (a : PeerAttrs)
    (shape : PeerAddressShape a) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (setPeerCmdObserved a) :=
  global_cases initial _ ((setPeerCmdObserved_spec initial a shape).consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.global)) (fun h => setPeerCmdObserved_absent h a)

theorem wgSetDeviceObserved_global (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (shape : DeviceAddressShape a) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (wgSetDeviceObserved a) :=
  global_cases initial _ ((wgSetDeviceObserved_spec initial a shape).consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.global)) (fun h => wgSetDeviceObserved_absent h a)

/- The original suffix has no routing completion cut. Keeping it as one lift
retains prior events on every queue/record Stop; only normal return drops wg. -/
private def destructFinish : M Unit := do
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
  modifyK fun k => {k with wg := none}
  retireDeviceUnits

def wgDestructObserved : PrefixM RoutingCompletion Unit := do
  liftPrefix (modifyDev fun d => {d with creatingNet := false, incomingPort := 0})
  liftPrefix (socketReinit none none)
  peerRemoveAllObserved
  liftPrefix destructFinish

def wgDeleteObserved : PrefixM RoutingCompletion Int := do
  if (← liftPrefix getK).wg.isNone then return -ENODEV
  if (← liftPrefix getDev).running then liftPrefix wgDown
  liftPrefix (skipCut allocCuts)
  liftPrefix mayHaveSlept
  wgDestructObserved
  return 0

theorem wgDestructObserved_erases : ErasesPrefix wgDestructObserved wgDestruct := by
  unfold wgDestructObserved wgDestruct destructFinish
  repeat' first
    | with_reducible exact peerRemoveAllObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem wgDeleteObserved_erases : ErasesPrefix wgDeleteObserved wgDelete := by
  unfold wgDeleteObserved wgDelete
  repeat' first
    | with_reducible exact wgDestructObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

private theorem destructFinish_none (w v : World)
    (hr : destructFinish.run w = .ok ((), v)) : routingView v = none := by
  have hc : ⦃fun _ => ⌜True⌝⦄ destructFinish ⦃⇓? _ w => ⌜routingView w = none⌝⦄ := by
    have hm := (routing_kernel _ mayHaveSlept_sameKernel).wp (fun _ => True)
    have hr := (ratelimiter_routing _ ratelimiterUninit_sameRatelimiterKernel).wp (fun _ => True)
    have ht := (routing_kernel _ retireDeviceUnits_sameKernel).wp (fun v => v = none)
    mvcgen [destructFinish, hm, hr, ht, getDev, getK, modifyDev, modifyK, unsupported, invariant]
    all_goals simp [routingView]
  exact (hoare_iff_triple _ _ _).mpr hc w () v True.intro hr

private theorem destructFinish_spec (initial : FlatTable × FlatTable) :
    PrefixEnsures (CompletionEmpty initial) (CompletionSafe initial) (liftPrefix destructFinish)
      (fun _ => GlobalCompletionState initial) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.1)
  intro h w u v hi hr
  cases u
  exact ⟨hi.1.1, by simpa [GlobalRoutedView, destructFinish_none w v hr] using hi.2⟩

private theorem destruct_present (initial : FlatTable × FlatTable) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial) wgDestructObserved
      (fun _ => GlobalCompletionState initial) := by
  unfold wgDestructObserved
  apply PrefixEnsures.bind (show PrefixEnsures _ _ _ (fun _ => CompletionState initial) from
    completion_lift_retains initial _ (.of_same (modifyDev_routing
      (fun d => {d with creatingNet := false, incomingPort := 0}) (fun _ => rfl))))
  intro _
  apply PrefixEnsures.bind (show PrefixEnsures _ _ _ (fun _ => CompletionState initial) from
    completion_lift_retains initial _ (.of_same (socketControl_routing _ (socketReinit_sameSocketKernel none none))))
  intro _
  exact PrefixEnsures.bind (peerRemoveAllObserved_empty_spec initial) (fun _ => destructFinish_spec initial)

private theorem destruct_absent (h0 : List RoutingCompletion) :
    PrefixPreserves (fun h w => h = h0 ∧ routingView w = none) (fun h => h = h0) wgDestructObserved := by
  change PrefixPreserves (Absent h0) _ _
  unfold wgDestructObserved
  apply PrefixPreserves.bind (absent_lift h0 _ (.of_same (modifyDev_routing
    (fun d => {d with creatingNet := false, incomingPort := 0}) (fun _ => rfl))))
  intro _
  apply absent_abort_bind h0 _ ?_
  intro w x v hn hr
  have hd : w.k.wg = none := by simpa [routingView] using hn
  simp [socketReinit, getDev, getK, invariant, hd] at hr

theorem wgDestructObserved_global (initial : FlatTable × FlatTable) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) wgDestructObserved :=
  global_cases initial _ (destruct_present initial) destruct_absent

private theorem global_safe (initial : FlatTable × FlatTable) :
    ∀ h w, GlobalCompletionState initial h w → CompletionSafe initial h := fun _ _ hi => hi.1

private theorem global_getK (initial : FlatTable × FlatTable) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (liftPrefix getK) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (global_safe initial)
  intro h w x v hi hr
  cases hr
  exact hi

theorem wgDeleteObserved_global (initial : FlatTable × FlatTable) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) wgDeleteObserved := by
  unfold wgDeleteObserved
  repeat' first
    | with_reducible exact wgDestructObserved_global initial
    | with_reducible exact global_getK initial
    | with_reducible exact global_completion_lift initial _ wgDown_routing
    | (solve | with_reducible apply global_completion_same initial; apply routing_kernel; first | exact getDev_sameKernel | exact skipCut_sameKernel _ | exact mayHaveSlept_sameKernel | (intro w x v hr; cases hr; rfl))
    | with_reducible exact PrefixPreserves.pure (global_safe initial) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem global_initial (trace : Runner.Trace) (w : World)
    (hk : w.k = Runner.initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild) :
    GlobalCompletionState ([], []) [] w := by
  refine ⟨.nil, ?_⟩
  change GlobalRoutedView (w.k.wg.map routingState) ([], [])
  rw [hk]
  exact initialKernel_global _ _ _ _ _ _

theorem global_initial_prefill (trace : Runner.Trace) (w : World)
    (hr : Env.seccompPrefill trace.seccompPrefill
      (Runner.initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild) = .ok w.k) :
    GlobalCompletionState ([], []) [] w :=
  ⟨.nil, prefill_global _ _ _ (initialKernel_global _ _ _ _ _ _) hr⟩

end Leanux.Proofs.WG.Configuration
