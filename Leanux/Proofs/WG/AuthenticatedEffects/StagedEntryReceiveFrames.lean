import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerFrames

/-! Receive maintenance changes statistics and peer metadata, while retaining
the complete staged-ticket and allocated-cell projection used by Entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ReceiveFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity Queues.RxCredits
set_option maxHeartbeats 600000

theorem device (f : Device → Device)
    (epoch : ∀ d, (f d).ifindex = d.ifindex) (peers : ∀ d, (f d).peers = d.peers)
    (frontier : ∀ d, (f d).nextSkb = d.nextSkb)
    (tx : ∀ d, (f d).txSkbs = d.txSkbs) (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) :
    SameView StagedEntry.view (modifyDev f) := by
  intro initial
  apply hoare_modify
  intro w before
  have same : StagedEntry.view {w with dev := w.dev.map f} = StagedEntry.view w := by
    unfold StagedEntry.view
    apply Prod.ext
    · cases device : w.dev <;> simp [Packets.epoch,device,epoch]
    apply Prod.ext
    · funext pid
      cases device : w.dev <;> simp [Staged.stagedAt,device,peers]
    apply Prod.ext
    · funext id
      cases device : w.dev <;> simp [PacketMaterial.view,TxDisposition.txPackets,device,tx]
    apply Prod.ext
    · cases device : w.dev <;> simp [Packets.snapshot,Packets.deviceStore,device,frontier,tx,rx]
    apply Prod.ext
    · funext id
      cases device : w.dev <;> simp [TxDisposition.txPackets,device,tx]
    · funext pid
      cases device : w.dev <;> simp [txQueueContents,handoffTxView,device,peers]
  exact same.trans before

theorem key_read (kid : KeypairId) : SameView StagedEntry.view (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a k v b run
  exact congrArg StagedEntry.view (KeyTimes.getKeypair_return kid w v k a b run).1

theorem stats (pid : PeerId) (len : Nat) : SameView StagedEntry.view (updateRxStats pid len) := by
  unfold updateRxStats
  apply SameView.bind (device (fun d => {d with rxPackets := d.rxPackets+1,rxBytes := d.rxBytes+len})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  intro ignored
  exact Queued.update pid (fun p => {p with rxBytes := p.rxBytes + len}) (fun _ => ⟨rfl,rfl,rfl⟩)

theorem dishonest_frame (why : Dishonest) : SameView StagedEntry.view (dishonest why) := by
  unfold dishonest
  cases why <;> apply device <;> intro d <;> rfl

theorem and_frame (left right : WG.M Bool)
    (hl : SameView StagedEntry.view left) (hr : SameView StagedEntry.view right) :
    SameView StagedEntry.view (WG.andM left right) := by
  unfold WG.andM
  apply SameView.bind hl
  intro ready
  split
  · exact hr
  · exact SameView.pure _ _

def freshDecision (current : Option KeypairId) : WG.M Bool :=
  WG.andM (branch .rxFreshKeypair current.isSome) do
    let some id := current | invariant "unreachable"
    let k ← getKeypair id
    WG.andM (branch .rxFreshValid k.sending.isValid) do
      WG.andM (branch .rxFreshInitiator k.iAmTheInitiator) do
        branchExpired .rxFreshExpired k.sending.birthdate (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)

theorem fresh_decision (current : Option KeypairId) :
    SameView StagedEntry.view (freshDecision current) := by
  unfold freshDecision
  apply and_frame _ _ (TimerFrames.branch_frame _ _)
  cases current with
  | none => exact fun initial => hoare_liftAmbient (AmbientM.invariant "unreachable") (fun w => StagedEntry.view w = initial)
  | some kid =>
    apply SameView.bind (key_read kid)
    intro key
    apply and_frame _ _ (TimerFrames.branch_frame _ _)
    apply and_frame _ _ (TimerFrames.branch_frame _ _)
    exact (branchExpired_sameWGWorld _ _ _ _).factor StagedEntry.view

macro "entry_receive_native" : tactic => `(tactic| (
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  try simp (config := {zeta := false}) only [WG.andM,WG.orM,branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head getKeypair; exact (key_read _).wp (· = initial))
    | (rx_retention_head updateRxStats; exact (stats _ _).wp (· = initial))
    | (rx_retention_head dishonest; exact (dishonest_frame _).wp (· = initial))
    | (rx_retention_head inetEcnDecapsulate; exact (TimerFrames.store (inetEcnDecapsulate_sameWGStore _ _ _)).wp (· = initial))
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact (TimerFrames.delete _ _).wp (· = initial))
    | (rx_retention_head invariant; unfold invariant; exact hoare_liftAmbient _ _)
    | entry_timer_native_step initial))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ReceiveFrames
