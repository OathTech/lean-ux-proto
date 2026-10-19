import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionConfiguration

/-! Fresh device creation consumes the exact native below-cut records while
retaining suspended activations. Allocation outcomes and every source failure
remain in the original path. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem exact_cut_ambient (site : HiddenSite) (n : Nat) (between : List HiddenSite) :
    SameView Ambient.suspended (AmbientM.skipCutExactly site n between) := by
  intro initial
  let P:=fun w:Ambient=>w.suspended=initial
  have read {α : Type} (next : Ambient→AmbientM α)
      (after : ∀saved,saved.suspended=initial→Preserves P (next saved)) :
      Preserves P ((MonadStateOf.get : AmbientM Ambient) >>= next) := ambient_get_bind initial next after
  have write (value : Ambient) (same : value.suspended=initial) :
      Preserves P (MonadStateOf.set value : AmbientM Unit) := ambient_set initial value same
  have cut : Preserves P (AmbientM.skipCut between) := cut_ambient between initial
  have skip : Preserves P AmbientM.skipAmbient := TxActorFrames.skip initial
  have note (site : Nat) : Preserves P (AmbientM.noteNetRxStart site) := TxActorFrames.note site initial
  have stopped {α : Type} (stop : Stop) : Preserves P (throw stop : AmbientM α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
  change Preserves P _
  unfold AmbientM.skipCutExactly
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (first | env_bind_head MonadStateOf.get | env_bind_head MonadState.get; apply read)
    | env_operation_fact write
    | env_operation_fact cut
    | env_operation_fact skip
    | env_operation_fact note
    | env_operation_fact stopped
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id P
       intro item state
       change Preserves P _)
    | routing_tx_step
  all_goals assumption

theorem exact_cut (site : HiddenSite) (n : Nat) (between : List HiddenSite) :
    Keeps (skipCutExactly site n between : StateT S AmbientM Unit) := ambient (exact_cut_ambient site n between)

theorem limiter_init : Keeps ratelimiterInit := by
  suspension_source [ratelimiterInit] using [branch,hidden]

theorem cookie_init : Keeps cookieCheckerInit := by
  suspension_source [cookieCheckerInit] using [clock,hidden,modify_device]

theorem pubkey_alloc : Keeps pubkeyHashtableAlloc := by
  suspension_source [pubkeyHashtableAlloc] using [env_ok,hidden,modify_device]

theorem newlink : Keeps wgNewlink := by
  suspension_source [wgNewlink] using
    [unsupported,modify_device,cookie_init,branch,pubkey_alloc,env_ok,slept,cuts,limiter_init,exact_cut]

theorem setup : Keeps wgSetup := by
  suspension_source [wgSetup] using []

theorem device_create : Keeps wgCreate := by
  suspension_source [wgCreate] using [setup,newlink]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
