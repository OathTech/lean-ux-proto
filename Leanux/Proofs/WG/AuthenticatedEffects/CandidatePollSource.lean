import Leanux.Proofs.WG.AuthenticatedEffects.IndexedPollSource
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects

/-! A candidate scope begins before the native replay call and ends after its
conditional consumer. Its label identifies the current packet, not an accepted
packet: authorization still requires that occurrence's successful certified
replay. The replay receipt remains adjacent to native confirmation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CandidatePoll
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

def sourceWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (enter : SkbId → RxPacket → m Nat) (leave : Nat → m Unit)
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
      let scope ← enter id pkt
      if !(← step (branch .rxPollCounterInvalid !(← counter id pkt))) then
        let endpoint ← step (endpointFromSkb pkt.source)
        if !(← step (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | step (invariant "unreachable")
          for inner in (← consume pid pkt e).toList do
            gro ← receive gro inner
          free := false
      leave scope
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


theorem neutral {m : Type → Type} [Monad m] [LawfulMonad m]
    (step : {α : Type} → WG.M α → m α)
    (counter : SkbId → RxPacket → m Bool)
    (consume : PeerId → RxPacket → Endpoint → m (Option (List UInt8)))
    (receive : GroState → List UInt8 → m GroState) (flush : GroState → m Unit)
    (pid : PeerId) (budget : Nat) :
    sourceWith step (fun _ _ => pure 0) (fun _ => pure ()) counter consume receive flush pid budget =
      IndexedPoll.sourceWith step counter consume receive flush pid budget := by
  simp only [sourceWith,IndexedPoll.sourceWith,pure_bind]
  rfl

theorem projects (ρ : E → Option F) (scopeMap : Nat → Nat)
    (eg : SkbId → RxPacket → PrefixT E State Nat)
    (ea : SkbId → RxPacket → PrefixT F State Nat)
    (lg : Nat → PrefixT E State Unit) (la : Nat → PrefixT F State Unit)
    (sg : {α : Type} → WG.M α → PrefixT E State α)
    (sa : {α : Type} → WG.M α → PrefixT F State α)
    (cg : SkbId → RxPacket → PrefixT E State Bool)
    (ca : SkbId → RxPacket → PrefixT F State Bool)
    (ug : PeerId → RxPacket → Endpoint → PrefixT E State (Option (List UInt8)))
    (ua : PeerId → RxPacket → Endpoint → PrefixT F State (Option (List UInt8)))
    (rg : GroState → List UInt8 → PrefixT E State GroState)
    (ra : GroState → List UInt8 → PrefixT F State GroState)
    (fg : GroState → PrefixT E State Unit) (fa : GroState → PrefixT F State Unit)
    (he : ∀ id pkt, ProjectsPrefix ρ scopeMap (eg id pkt) (ea id pkt))
    (hl : ∀ token, ProjectsPrefix ρ id (lg token) (la (scopeMap token)))
    (hs : ∀ {α} (action : WG.M α), ProjectsPrefix ρ id (sg action) (sa action))
    (hc : ∀ skb pkt, ProjectsPrefix ρ id (cg skb pkt) (ca skb pkt))
    (hu : ∀ pid pkt ep, ProjectsPrefix ρ id (ug pid pkt ep) (ua pid pkt ep))
    (hr : ∀ gro bytes, ProjectsPrefix ρ id (rg gro bytes) (ra gro bytes))
    (hf : ∀ gro, ProjectsPrefix ρ id (fg gro) (fa gro))
    (pid : PeerId) (budget : Nat) :
    ProjectsPrefix ρ id (sourceWith sg eg lg cg ug rg fg pid budget) (sourceWith sa ea la ca ua ra fa pid budget) := by
  unfold sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (apply projectsPrefix_bind ρ scopeMap id (he _ _); intro token)
    | exact hl _
    | exact hs _
    | exact hc _ _
    | exact hu _ _ _
    | exact hr _ _
    | exact hf _
    | indexed_poll_project_step ρ

end Leanux.Proofs.WG.AuthenticatedEffects.CandidatePoll
