import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumePointSource

/-! Same-world ledger frames for the fixed receive leaves. No RX allocator or
free is framed as preserving the shared allocation frontier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal

abbrev Carrier := CompletePoll.Carrier [] []
abbrev Checked (action : PrefixM Event α) := CompletePoll.Checked [] [] CompleteProduct.Safe action

theorem carrier_safe (h : History) (w : World) (before : Carrier h w) : CompleteProduct.Safe h :=
  Napi.Points.carrier_safe h w before

theorem native_checked (action : WG.M α) (frame : SameView StagedEntry.view action) : Checked (wg action) :=
  CompletePoll.state _ (CompletePassive.native _ CompleteProduct.account_safe _ frame)

theorem Native.checked (token : Native action) : Checked action := by
  cases token with
  | world =>
    apply PrefixEnsures.lift _ carrier_safe
    intro h w value v before run
    cases run
    exact before
  | branch site yes => exact native_checked _ (TimerFrames.branch_frame _ _)
  | compare site yes left right =>
    apply native_checked
    intro initial
    unfold branchCmp
    exact hoare_liftAmbient _ _
  | key kid => exact native_checked _ (ReceiveFrames.key_read kid)
  | writeKey kid key =>
    apply native_checked
    unfold setKeypair
    exact ReceiveFrames.device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | peer pid => exact native_checked _ (Queued.read pid)
  | freshWrite pid => exact native_checked _ (Queued.update pid
      (fun p => {p with sentLastminuteHandshake := true}) (fun _ => ⟨rfl,rfl,rfl⟩))
  | expired site birth limit => exact native_checked _ ((branchExpired_sameWGWorld _ _ _ _).factor StagedEntry.view)
  | previous pid => exact native_checked _ (Queued.update pid
      (fun p => {p with keypairPrevious := p.keypairCurrent}) (fun _ => ⟨rfl,rfl,rfl⟩))
  | current pid kid => exact native_checked _ (Queued.update pid
      (fun p => {p with keypairCurrent := some kid, keypairNext := none}) (fun _ => ⟨rfl,rfl,rfl⟩))
  | statsDevice len => exact native_checked _ (ReceiveFrames.device _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  | statsPeer pid len => exact native_checked _ (Queued.update pid
      (fun p => {p with rxBytes := p.rxBytes + len}) (fun _ => ⟨rfl,rfl,rfl⟩))
  | dishonest why => exact native_checked _ (ReceiveFrames.dishonest_frame why)
  | ecn protocol ds bytes => exact native_checked _ (TimerFrames.store (inetEcnDecapsulate_sameWGStore _ _ _))
  | replay skb packet receipt => exact CompletePoll.emit _ CompleteProduct.account_safe _ rfl (fun _ => rfl)
  | confirmed pid kid receipt => exact CompletePoll.emit _ CompleteProduct.account_safe _ rfl (fun _ => rfl)
  | wgInvariant message =>
    apply native_checked
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    cases run
  | wgUnsupported message =>
    apply native_checked
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    cases run
  | invariant message => exact PrefixEnsures.lift _ carrier_safe (by intro h w value v before run; cases run)
  | unsupported message => exact PrefixEnsures.lift _ carrier_safe (by intro h w value v before run; cases run)
  | excluded message => exact PrefixEnsures.lift _ carrier_safe (by intro h w value v before run; cases run)

theorem Child.checked (token : Child) : Checked token.action := by
  cases token with
  | endpoint pid endpoint => exact native_checked _ (EndpointFrames.set pid endpoint)
  | keyRelease kid => exact native_checked _ (KeyFrames.put kid true)
  | handshakeTimer pid => exact native_checked _ (TimerFrames.handshake_complete pid .walltimeLastHandshakeData)
  | authenticated pid => exact native_checked _ (TimerFrames.delete _ _)
  | traversal pid => exact CompletePoll.state _ (CompleteTimer.traversal _ CompleteProduct.account_safe pid)
  | received pid => exact CompletePoll.state _ (CompleteReceiveObserved.received _ CompleteProduct.account_safe pid)
  | queued pid => exact CompletePoll.state _ (CompleteTimerQueue.queued _ CompleteProduct.account_safe pid false)
  | staging pid => exact CompletePoll.state _ (CompleteProduct.source_state (CompleteTransmit.staging pid))
  | lookup protocol bytes => exact native_checked _ (ReceiveLookup.frame protocol bytes)
  | release peer => exact CompletePoll.state _ (CompleteSource.original peer _ CompleteProduct.account_safe)

theorem Shape.checked (shape : Shape action) : Checked action := by
  induction shape with
  | pure value => exact CompletePoll.pure_checked _ CompleteProduct.account_safe value
  | native token => exact token.checked
  | child token => exact token.checked
  | failed failure next =>
    intro w h before
    obtain ⟨reason,run⟩ := failure.run w h
    exact ⟨[],by simp only [runPrefix_bind,run,List.append_nil],by simpa only [runPrefix_bind,run] using carrier_safe h w before,by simp only [runPrefix_bind,run]⟩
  | bind head tail ihHead ihTail => exact CompletePoll.bind_checked _ ihHead ihTail
  | marked label shape ih => exact ih

theorem Shape.normal (shape : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h = (.ok (value,u),middle)) : Carrier middle u := by
  obtain ⟨suffix,extended,safe,kept⟩ := shape.checked w h before
  rw [performed] at kept
  exact kept

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
