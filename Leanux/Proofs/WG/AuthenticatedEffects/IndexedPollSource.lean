import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationPollSource
import Leanux.Proofs.WG.Lifetimes.MaintenanceTimers
import Leanux.Proofs.Logged.ProjectsPrefix

/-! The native poll replay cut retains the actual skb identity in scope. The
neutral specialization is the existing source, and callback projection retains
all normal results and internally stopped prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.IndexedPoll
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

def sourceWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (counter : SkbId → RxPacket → m Bool)
    (consume : PeerId → RxPacket → Endpoint → m (Option (List UInt8)))
    (receive : GroState → List UInt8 → m GroState) (flush : GroState → m Unit)
    (pid : PeerId) (budget : Nat) : m Nat := do
  if ← step (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : GroState := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let (first, q) ← step (do (← getPeer pid).rxQueue.peek)
    step (do setPeer pid { (← getPeer pid) with rxQueue := q })
    let go ← step (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted))
    if !go then
      drained := true
      break
    let some id := first | step (invariant "unreachable")
    let pkt ← step (getRxSkb id)
    if pkt.peer != pid then step (invariant "a packet on another peer's rx_queue")
    step (do setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked })
    let mut free := true
    if !(← step (branch .rxPollNotCrypted (pkt.state != .crypted))) then
      if !(← step (branch .rxPollCounterInvalid !(← counter id pkt))) then
        let endpoint ← step (endpointFromSkb pkt.source)
        if !(← step (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | step (invariant "unreachable")
          for inner in (← consume pid pkt e).toList do
            gro ← receive gro inner
          free := false
    step (keypairPut (some pkt.keypair) false)
    step (peerPut (some pid))
    _ ← step (branch .rxPollFree free)
    step (freeRxSkb id)
    workDone := workDone + 1
    if ← step (branch .rxPollBudgetDone (workDone ≥ budget)) then break
  if !drained && workDone < budget then step (invariant "the rx_queue did not drain")
  if ← step (branch .rxPollComplete (workDone < budget)) then
    step (do setPeer pid { (← getPeer pid) with napiScheduled := false })
    flush gro
  else step (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone


theorem unindexed {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (counter : RxPacket → m Bool)
    (consume : PeerId → RxPacket → Endpoint → m (Option (List UInt8)))
    (receive : GroState → List UInt8 → m GroState) (flush : GroState → m Unit)
    (pid : PeerId) (budget : Nat) :
    sourceWith step (fun _ pkt => counter pkt) consume receive flush pid budget =
      HandshakeSecurity.Confirmation.Poll.sourceWith step counter consume receive flush pid budget := rfl

private theorem forIn_projects (ρ : E → Option F) (xs : List γ) (b : β)
    (g : γ → β → PrefixT E State (ForInStep β))
    (a : γ → β → PrefixT F State (ForInStep β))
    (each : ∀ x b, ProjectsPrefix ρ id (g x b) (a x b)) :
    ProjectsPrefix ρ id (forIn xs b g) (forIn xs b a) := by
  induction xs generalizing b with
  | nil => exact projectsPrefix_pure ρ id b
  | cons x xs ih =>
    rw [List.forIn_cons,List.forIn_cons]
    apply projectsPrefix_bind ρ id id (each x b)
    intro step
    cases step with
    | done b => exact projectsPrefix_pure ρ id b
    | yield b => exact ih b

macro "indexed_poll_project_step " rho:ident : tactic => `(tactic| first
  | (maintenance_head Pure.pure; exact projectsPrefix_pure $rho id _)
  | (maintenance_head ForIn.forIn; apply forIn_projects $rho)
  | (maintenance_head Bind.bind; apply projectsPrefix_bind $rho id id)
  | (maintenance_head ite; apply projectsPrefix_ite $rho _ id)
  | (maintenance_intro; try dsimp only [id])
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem projects (ρ : E → Option F)
    (sg : {α : Type} → WG.M α → PrefixT E State α)
    (sa : {α : Type} → WG.M α → PrefixT F State α)
    (cg : SkbId → RxPacket → PrefixT E State Bool)
    (ca : SkbId → RxPacket → PrefixT F State Bool)
    (ug : PeerId → RxPacket → Endpoint → PrefixT E State (Option (List UInt8)))
    (ua : PeerId → RxPacket → Endpoint → PrefixT F State (Option (List UInt8)))
    (rg : GroState → List UInt8 → PrefixT E State GroState)
    (ra : GroState → List UInt8 → PrefixT F State GroState)
    (fg : GroState → PrefixT E State Unit) (fa : GroState → PrefixT F State Unit)
    (hs : ∀ {α} (action : WG.M α), ProjectsPrefix ρ id (sg action) (sa action))
    (hc : ∀ skb pkt, ProjectsPrefix ρ id (cg skb pkt) (ca skb pkt))
    (hu : ∀ pid pkt ep, ProjectsPrefix ρ id (ug pid pkt ep) (ua pid pkt ep))
    (hr : ∀ gro bytes, ProjectsPrefix ρ id (rg gro bytes) (ra gro bytes))
    (hf : ∀ gro, ProjectsPrefix ρ id (fg gro) (fa gro))
    (pid : PeerId) (budget : Nat) :
    ProjectsPrefix ρ id (sourceWith sg cg ug rg fg pid budget) (sourceWith sa ca ua ra fa pid budget) := by
  unfold sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | exact hs _
    | exact hc _ _
    | exact hu _ _ _
    | exact hr _ _
    | exact hf _
    | indexed_poll_project_step ρ

end Leanux.Proofs.WG.AuthenticatedEffects.IndexedPoll
