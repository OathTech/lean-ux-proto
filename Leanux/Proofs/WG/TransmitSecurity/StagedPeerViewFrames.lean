import Leanux.Proofs.WG.TransmitSecurity.StagedNativeFrames

/-! Exact staged-queue frames through peer metadata updates and native timer placement. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem read (pid : PeerId) : SameView stagedAt (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg stagedAt (getPeer_normal pid w v p a b run).1

theorem store {action : WG.M α} (same : SameWGStore action) : SameView stagedAt action :=
  same.of_factor (fun s : WGStoreView => fun pid => (s.dev.bind fun d => d.peers[pid]?).map
    fun p => (p.internalId,p.staged)) stagedAt (fun _ => rfl)

theorem modify_world (f : WGWorld → WGWorld) (same : ∀ w, stagedAt (f w) = stagedAt w) :
    SameView stagedAt (modify f : WG.M Unit) := by
  intro initial
  apply hoare_modify
  intro w before
  simpa only [same] using before

theorem modify_preserves_world (f : WGWorld → WGWorld) (P : (PeerId → Option (Nat × List Packet)) → Prop)
    (same : ∀ w, stagedAt (f w) = stagedAt w) :
    Preserves (fun w => P (stagedAt w)) (modify f : WG.M Unit) :=
  (modify_world f same).wp P

theorem write_known (P : (PeerId → Option (Nat × List Packet)) → Prop) (pid : PeerId) (p : Peer) :
    Hoare (setPeer pid p)
      (fun w => P (stagedAt w) ∧ stagedAt w pid = some (p.internalId,p.staged))
      (fun _ w => P (stagedAt w) ∧ stagedAt w pid = some (p.internalId,p.staged)) :=
  hoare_consequence (Staged.write_saved (fun s => P s ∧ s pid = some (p.internalId,p.staged)) pid p)
    (fun _ hi => ⟨hi,hi.2⟩) (fun _ _ hi => hi)

theorem update_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    SameView stagedAt (getPeer pid >>= fun p => setPeer pid (f p)) := by
  intro initial
  apply hoare_bind _ _ (Staged.read_saved (· = initial) pid)
  intro p
  exact hoare_consequence (Staged.write_saved (· = initial) pid (f p))
    (fun _ hi => ⟨hi.1,by simpa only [(same p).1,(same p).2] using hi.2⟩) (fun _ _ hi => hi)

theorem place (pid : PeerId) (timer : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
    SameView stagedAt (placeOnWheel pid timer expires clk unit) := by
  intro initial
  unfold placeOnWheel
  apply hoare_bind _ _ (Staged.read_saved (· = initial) pid)
  intro p
  let P := fun w => stagedAt w = initial ∧ stagedAt w pid = some (p.internalId,p.staged)
  have write (q : Peer) (same : q.internalId = p.internalId ∧ q.staged = p.staged) :
      Preserves P (setPeer pid q) := by
    simpa only [Preserves,P,same.1,same.2] using write_known (· = initial) pid q
  apply hoare_consequence (P := P) (Q := fun _ => P) ?_ (fun _ hi => hi) (fun _ _ hi => hi.1)
  change Preserves P _
  simp only [hidden,peekHiddenSite,invariant]
  repeat' first
      | (rx_retention_head setPeer; apply write; cases timer <;> exact ⟨rfl,rfl⟩)
      | (rx_retention_head getPeer; exact (read _).wp (fun s => s = initial ∧ s pid = some (p.internalId,p.staged)))
      | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
      | (rx_retention_head get; exact hoare_consequence (hoare_get P) (fun _ hi => hi) (fun _ _ hi => hi.2))
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
         apply (hoare_iff_run_ambient _ _ _).mpr
         intro w a value v b before run
         cases run)
      | rxstack_preserves_join
      | rx_retention_step

theorem update_peer_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WG.M α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged)
    (initial : PeerId → Option (Nat × List Packet))
    (tail : ∀ x, Preserves (fun w => stagedAt w = initial) (next x)) :
    Preserves (fun w => stagedAt w = initial)
      (getPeer pid >>= fun p => setPeer pid (f p) >>= next) := by
  simpa only [bind_assoc] using preserves_bind (update_peer pid f same initial) tail

private theorem conditional (p : Prop) [Decidable p] (a b : WG.M α)
    (P : WGWorld → Prop) (ha : Preserves P a) (hb : Preserves P b) :
    Preserves P (if p then a else b) := by
  by_cases h : p <;> simp only [h,↓reduceIte] <;> assumption

macro "staged_exact_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head ite; apply conditional)
  | (rx_retention_head getAmbient; unfold getAmbient; exact hoare_liftAmbient _ _)
  | (rx_retention_head hidden; unfold hidden; exact hoare_liftAmbient _ _)
  | (rx_retention_head invariant; unfold invariant; exact hoare_liftAmbient _ _)
  | (rx_retention_head unsupported; unfold unsupported; exact hoare_liftAmbient _ _)
  | (receive_update_head Bind.bind
     apply update_peer_bind
     · intro p; exact ⟨rfl,rfl⟩
     intro x)
  | (receive_update_head setPeer; apply update_peer; intro p; exact ⟨rfl,rfl⟩)
  | (rx_retention_head getPeer; exact read _ $initial)
  | (rx_retention_head getDev; exact store getDev_sameWGStore $initial)
  | (rx_retention_head get; exact hoare_consequence (hoare_get (fun w => stagedAt w = $initial)) (fun _ hi => hi) (fun _ _ hi => hi.2))
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a value v b before run
     cases run)
  | rxstack_preserves_join
  | rx_retention_step)

set_option maxHeartbeats 2000000 in
theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64) :
    SameView stagedAt (armTimer pid timer delay jc) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold armTimer
  repeat' first
    | (rx_retention_head placeOnWheel; exact place _ _ _ _ _ initial)
    | staged_exact_step initial

theorem delete_timer (pid : PeerId) (timer : PeerTimer) : SameView stagedAt (delTimer pid timer) :=
  update_peer pid (fun p => (p.setTimer timer none).setWheel timer none)
    (fun _ => by cases timer <;> exact ⟨rfl,rfl⟩)

theorem timer_guard (pid : PeerId) : SameView stagedAt (modPeerTimerGuard pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold modPeerTimerGuard
  simp only [branch,WG.andM]
  repeat' staged_exact_step initial

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView stagedAt (modPeerTimer site pid timer delay) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold modPeerTimer
  repeat' first
    | (rx_retention_head callerJiffies; exact ((callerJiffies_sameWGWorld _).factor stagedAt) initial)
    | (rx_retention_head modPeerTimerGuard; exact timer_guard _ initial)
    | (rx_retention_head armTimer; exact arm _ _ _ _ initial)
    | staged_exact_step initial

end Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
