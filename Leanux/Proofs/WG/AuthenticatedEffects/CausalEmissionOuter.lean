import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionTraffic

/-! The complete syscall boundary preserves positional delivery coverage.
Administrative steps use direct sent frames, independently of WGStore. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Configuration TransmitSecurity.Driver
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem dispatch_observe : ProductSafe (dispatchObserveObserved hooks) := by
  unfold dispatchObserveObserved
  apply product_bind observe
  rintro ⟨ret,json⟩
  exact product_bind (ambient _) (fun _ => socket_call _ _ (product_pure ret))

theorem dispatch (call : Syscall) : ProductSafe (dispatchObserved hooks call) := by
  apply dispatchWith_preserves
  · exact retained
  · intro attrs; exact netlink _ (product_state (config_device attrs))
  · apply rtnetlink
    simpa only [liftWGObserver_lift] using product_state device_create
  · exact rtnetlink _ env_delete
  · exact syscall_xmit
  · intro family port message tos ll dest
    exact socket_call _ _ (inject family port message tos ll dest)
  · exact flood
  · exact batch
  · exact dispatch_observe

private theorem current : ProductSafe (liftPrefix Leanux.getCurrent) := by
  unfold Leanux.getCurrent
  exact fs (StateT.lift TaskM.getCurrent)

macro "emission_syscall_step" : tactic => `(tactic| first
  | assumption
  | (change PrefixPreserves (fun h w => Deliveries.Carrier h w.wg) Safe _; owner_outer_callback)
  | (emission_carrier_native_head Leanux.getCurrent; exact current)
  | emission_outer_step)

private theorem syscall_tail (call : Syscall) (body : PrefixM Event Int)
    (send timers route xmit advance cleanup : PrefixM Event Unit)
    (hd : ProductSafe body) (hs : ProductSafe send) (ht : ProductSafe timers)
    (hr : ProductSafe route) (hx : ProductSafe xmit) (ha : ProductSafe advance)
    (hc : ProductSafe cleanup) : ProductSafe (do
      let ret ← body
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
      match call with
      | .wgSet _ | .wgInject .. => send; timers
      | .wgUp => send; timers; route
      | .wgXmit .. => xmit; timers
      | .wgBatch .. => timers
      | .wgAdvance _ => advance
      | .wgNetnsClose => cleanup
      | _ => pure ()
      match call with
      | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
      | .wgAddroute .. | .wgAddaddr .. =>
        let shape := Net.Fib.shape (← liftPrefix getRouting)
        liftPrefix (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie",shape)]})
      | _ => pure ()
      pure ret) := by
  apply product_bind hd
  intro ret
  apply product_bind
  · apply product_forIn
    intro c acc
    exact product_bind (seccomp (Seccomp.enterHarnessCall c)) (fun _ => product_pure _)
  · intro _
    apply product_bind (fs taskWorkRun)
    intro _
    cases call
    all_goals dsimp only
    all_goals repeat' emission_syscall_step

private theorem syscall_entry (call : Syscall) (body : PrefixM Event Int) (hb : ProductSafe body) :
    ProductSafe (do
      liftPrefix (modify fun w => {w with fs := {w.fs with userOut := none,userFds := none},seccomp := {w.seccomp with emitted := {},translatedLen := none}})
      liftPrefix (modifyWG fun g => {g with queuedThisCall := []})
      liftPrefix (modifyAmbient fun a => {a with steps := #[],extraOut := [],fired := #[],netRxSections := 0,netRxSection := 0})
      match syscallNr call with
      | some nr => liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
      | none =>
        if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
          liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
      body) := by
  apply product_bind
  · apply edit; intro w; rfl
  intro _
  apply product_bind
  · apply native; apply EmissionFrames.wg_edit; intro w; rfl
  intro _
  apply product_bind (ambient _)
  intro _
  cases hn : syscallNr call
  all_goals repeat' first
    | exact hb
    | emission_syscall_step

theorem syscall (call : Syscall) : ProductSafe (syscallObserved hooks call) :=
  syscall_entry call _ (syscall_tail call _ _ _ _ _ _ _
    (dispatch call) send_workers idle_timers (native _ EmissionFrames.route_into)
    after_xmit after_advance (native _ TransmitSecurity.EmissionCleanup.env_cleanup))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
